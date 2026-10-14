use crate::{Equivalent, TryReserveError};
use hashbrown::{hash_table::Entry as HashEntry, HashTable};
use std::hash::{BuildHasher, Hash};

/// Entry layout is chosen by the map: linked entries for SurMap, pairs for BiMap.
pub(crate) trait TableEntry {
    type Key;
    type Value;
    fn pair(&self) -> &(Self::Key, Self::Value);
    fn into_pair(self) -> (Self::Key, Self::Value);
}

impl<K, V> TableEntry for (K, V) {
    type Key = K;
    type Value = V;
    fn pair(&self) -> &(K, V) {
        self
    }
    fn into_pair(self) -> (K, V) {
        self
    }
}

/// Dense entry storage and two indexes. Keys are unique; the value index holds
/// one representative per distinct value. Maps own their grouping/conflict rules.
#[derive(Clone)]
pub(crate) struct BidiTable<E, S> {
    hash_builder: S,
    entries: Vec<E>,
    keys: HashTable<usize>,
    values: HashTable<usize>,
}

impl<E, S> BidiTable<E, S> {
    pub(crate) fn with_capacity_and_hasher(capacity: usize, hash_builder: S) -> Self {
        Self {
            hash_builder,
            entries: Vec::with_capacity(capacity),
            keys: HashTable::with_capacity(capacity),
            values: HashTable::with_capacity(capacity),
        }
    }
    pub(crate) fn hasher(&self) -> &S {
        &self.hash_builder
    }
    pub(crate) fn len(&self) -> usize {
        self.entries.len()
    }
    pub(crate) fn value_len(&self) -> usize {
        self.values.len()
    }
    pub(crate) fn capacity(&self) -> usize {
        self.entries.capacity().min(self.keys.capacity())
    }
    pub(crate) fn value_capacity(&self) -> usize {
        self.values.capacity()
    }
    pub(crate) fn entries(&self) -> &[E] {
        &self.entries
    }
    // Callers must maintain index membership when changing an entry's pair.
    pub(crate) fn entry_mut(&mut self, index: usize) -> &mut E {
        &mut self.entries[index]
    }
    pub(crate) fn value_heads(
        &self,
    ) -> impl ExactSizeIterator<Item = usize> + std::iter::FusedIterator + '_ {
        self.values.iter().copied()
    }
    pub(crate) fn clear(&mut self) {
        self.keys.clear();
        self.values.clear();
        self.entries.clear();
    }
    pub(crate) fn drain(&mut self) -> std::vec::Drain<'_, E> {
        self.keys.clear();
        self.values.clear();
        self.entries.drain(..)
    }
    pub(crate) fn into_entries(self) -> std::vec::IntoIter<E> {
        self.entries.into_iter()
    }
}

impl<E: TableEntry, S> BidiTable<E, S> {
    /// Layout conversion must preserve every pair and its position. The indexes
    /// and hasher remain valid without rehashing; only the entry vector changes.
    pub(crate) fn map_entries<F: TableEntry<Key = E::Key, Value = E::Value>>(
        self,
        mut f: impl FnMut(E) -> F,
    ) -> BidiTable<F, S> {
        let mut entries = Vec::with_capacity(self.entries.len());
        for entry in self.entries {
            entries.push(f(entry));
        }
        BidiTable {
            hash_builder: self.hash_builder,
            entries,
            keys: self.keys,
            values: self.values,
        }
    }
}

impl<E, S> BidiTable<E, S>
where
    E: TableEntry,
    E::Key: Hash + Eq,
    E::Value: Hash + Eq,
    S: BuildHasher,
{
    pub(crate) fn reserve(&mut self, additional: usize) {
        self.entries.reserve(additional);
        self.keys.reserve(additional, |&i| {
            self.hash_builder.hash_one(&self.entries[i].pair().0)
        });
        self.values.reserve(additional, |&i| {
            self.hash_builder.hash_one(&self.entries[i].pair().1)
        });
    }
    pub(crate) fn try_reserve(&mut self, additional: usize) -> Result<(), TryReserveError> {
        self.entries
            .try_reserve(additional)
            .map_err(TryReserveError::Entries)?;
        self.keys
            .try_reserve(additional, |&i| {
                self.hash_builder.hash_one(&self.entries[i].pair().0)
            })
            .map_err(TryReserveError::Index)?;
        self.values
            .try_reserve(additional, |&i| {
                self.hash_builder.hash_one(&self.entries[i].pair().1)
            })
            .map_err(TryReserveError::Index)?;
        Ok(())
    }
    pub(crate) fn shrink_to(&mut self, min_capacity: usize) {
        self.entries.shrink_to(min_capacity);
        self.keys.shrink_to(min_capacity, |&i| {
            self.hash_builder.hash_one(&self.entries[i].pair().0)
        });
        self.values.shrink_to(min_capacity, |&i| {
            self.hash_builder.hash_one(&self.entries[i].pair().1)
        });
    }
    pub(crate) fn key_index<Q: Hash + Equivalent<E::Key> + ?Sized>(
        &self,
        key: &Q,
    ) -> Option<usize> {
        self.keys
            .find(self.hash_builder.hash_one(key), |&i| {
                key.equivalent(&self.entries[i].pair().0)
            })
            .copied()
    }
    pub(crate) fn value_index<Q: Hash + Equivalent<E::Value> + ?Sized>(
        &self,
        value: &Q,
    ) -> Option<usize> {
        self.values
            .find(self.hash_builder.hash_one(value), |&i| {
                value.equivalent(&self.entries[i].pair().1)
            })
            .copied()
    }

    /// Key must be absent. The returned value representative, if any, lets the
    /// owning map link the new entry into its group.
    pub(crate) fn insert_entry(&mut self, entry: E) -> (usize, Option<usize>) {
        let key_hash = self.hash_builder.hash_one(&entry.pair().0);
        self.reserve(1);
        let index = self.entries.len();
        self.entries.push(entry);
        self.keys.insert_unique(key_hash, index, |&i| {
            self.hash_builder.hash_one(&self.entries[i].pair().0)
        });
        let previous = self.link_value(index);
        (index, previous)
    }

    /// Makes this entry the representative for its value, returning the old head.
    pub(crate) fn link_value(&mut self, index: usize) -> Option<usize> {
        let hash = self.hash_builder.hash_one(&self.entries[index].pair().1);
        match self.values.entry(
            hash,
            |&i| self.entries[i].pair().1 == self.entries[index].pair().1,
            |&i| self.hash_builder.hash_one(&self.entries[i].pair().1),
        ) {
            HashEntry::Occupied(entry) => Some(std::mem::replace(entry.into_mut(), index)),
            HashEntry::Vacant(entry) => {
                entry.insert(index);
                None
            }
        }
    }

    /// The owning map supplies the next representative before modifying a head.
    pub(crate) fn detach_value_head(&mut self, index: usize, next: Option<usize>) {
        let hash = self.hash_builder.hash_one(&self.entries[index].pair().1);
        let mut head = self.values.find_entry(hash, |&i| i == index).unwrap();
        if let Some(next) = next {
            *head.get_mut() = next;
        } else {
            head.remove();
        }
    }

    /// The owning map must detach the entry from its value group first. Repairs
    /// both indexes for a moved entry; linked neighbors are the map's responsibility.
    pub(crate) fn remove_entry(&mut self, index: usize) -> E {
        let key_hash = self.hash_builder.hash_one(&self.entries[index].pair().0);
        let old_index = self.entries.len() - 1;
        let moved_hashes = (index != old_index).then(|| {
            (
                self.hash_builder
                    .hash_one(&self.entries[old_index].pair().0),
                self.hash_builder
                    .hash_one(&self.entries[old_index].pair().1),
            )
        });
        self.keys
            .find_entry(key_hash, |&i| i == index)
            .unwrap()
            .remove();
        let entry = self.entries.swap_remove(index);
        if let Some((key_hash, value_hash)) = moved_hashes {
            *self.keys.find_mut(key_hash, |&i| i == old_index).unwrap() = index;
            // A linked entry may not be the representative for its value.
            if let Some(head) = self.values.find_mut(value_hash, |&i| i == old_index) {
                *head = index;
            }
        }
        entry
    }
}
