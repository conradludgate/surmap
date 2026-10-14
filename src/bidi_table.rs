use crate::{Equivalent, TryReserveError};
use hashbrown::HashTable;
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

#[derive(Clone, Copy)]
struct HashPair {
    key: u64,
    value: u64,
}

pub(crate) struct PreparedInsert {
    pub(crate) key_index: Option<usize>,
    pub(crate) value_index: Option<usize>,
    hashes: HashPair,
}

/// Only the removed entries and the tail entries that can move need cached hashes.
pub(crate) struct PreparedRemovals {
    hashes: [Option<(usize, HashPair)>; 4],
}
impl PreparedRemovals {
    fn pair(&self, index: usize) -> HashPair {
        self.hashes
            .iter()
            .flatten()
            .find(|(i, _)| *i == index)
            .unwrap()
            .1
    }
    pub(crate) fn value_hash(&self, index: usize) -> u64 {
        self.pair(index).value
    }
    fn removed(&mut self, index: usize, last: usize) {
        for slot in &mut self.hashes {
            match slot {
                Some((i, _)) if *i == index => *slot = None,
                Some((i, _)) if index != last && *i == last => *i = index,
                _ => {}
            }
        }
    }
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
        let (keys, values) = self
            .rehash_hashes(
                additional > self.keys.capacity() - self.keys.len(),
                additional > self.values.capacity() - self.values.len(),
            )
            .expect("hash buffer reservation failed");
        self.entries.reserve(additional);
        self.keys.reserve(additional, |&i| keys[i]);
        self.values.reserve(additional, |&i| values[i]);
    }
    pub(crate) fn try_reserve(&mut self, additional: usize) -> Result<(), TryReserveError> {
        let (keys, values) = self.rehash_hashes(
            additional > self.keys.capacity() - self.keys.len(),
            additional > self.values.capacity() - self.values.len(),
        )?;
        self.entries
            .try_reserve(additional)
            .map_err(TryReserveError::Entries)?;
        self.keys
            .try_reserve(additional, |&i| keys[i])
            .map_err(TryReserveError::Index)?;
        self.values
            .try_reserve(additional, |&i| values[i])
            .map_err(TryReserveError::Index)?;
        Ok(())
    }
    pub(crate) fn shrink_to(&mut self, min_capacity: usize) {
        let (keys, values) = self
            .rehash_hashes(true, true)
            .expect("hash buffer reservation failed");
        self.entries.shrink_to(min_capacity);
        self.keys.shrink_to(min_capacity, |&i| keys[i]);
        self.values.shrink_to(min_capacity, |&i| values[i]);
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

    // Hashing must finish before HashTable starts rehashing: its callback may
    // otherwise panic halfway through an in-place rebuild and lose index entries.
    fn rehash_hashes(
        &self,
        keys_needed: bool,
        values_needed: bool,
    ) -> Result<(Vec<u64>, Vec<u64>), TryReserveError> {
        let mut keys = Vec::new();
        let mut values = Vec::new();
        if keys_needed {
            keys.try_reserve_exact(self.len())
                .map_err(TryReserveError::Entries)?;
            keys.resize(self.len(), 0);
            for &i in self.keys.iter() {
                keys[i] = self.hash_builder.hash_one(&self.entries[i].pair().0);
            }
        }
        if values_needed {
            values
                .try_reserve_exact(self.len())
                .map_err(TryReserveError::Entries)?;
            values.resize(self.len(), 0);
            for &i in self.values.iter() {
                values[i] = self.hash_builder.hash_one(&self.entries[i].pair().1);
            }
        }
        Ok((keys, values))
    }

    pub(crate) fn prepare_insert(&mut self, pair: &(E::Key, E::Value)) -> PreparedInsert {
        let hashes = HashPair {
            key: self.hash_builder.hash_one(&pair.0),
            value: self.hash_builder.hash_one(&pair.1),
        };
        let key_index = self
            .keys
            .find(hashes.key, |&i| pair.0 == self.entries[i].pair().0)
            .copied();
        let value_index = self
            .values
            .find(hashes.value, |&i| pair.1 == self.entries[i].pair().1)
            .copied();
        self.reserve(1);
        PreparedInsert {
            key_index,
            value_index,
            hashes,
        }
    }

    /// Commits a new key after preparation, without user hash/equality calls.
    pub(crate) fn insert_prepared(&mut self, entry: E, prepared: &PreparedInsert) -> usize {
        let index = self.entries.len();
        self.entries.push(entry);
        self.keys.insert_unique(prepared.hashes.key, index, |_| {
            unreachable!("key capacity was reserved")
        });
        self.link_value_prepared(index, prepared);
        index
    }

    pub(crate) fn link_value_prepared(&mut self, index: usize, prepared: &PreparedInsert) {
        if let Some(head) = prepared.value_index {
            *self
                .values
                .find_mut(prepared.hashes.value, |&i| i == head)
                .unwrap() = index;
        } else {
            self.values
                .insert_unique(prepared.hashes.value, index, |_| {
                    unreachable!("value capacity was reserved")
                });
        }
    }

    pub(crate) fn value_hash(&self, index: usize) -> u64 {
        self.hash_builder.hash_one(&self.entries[index].pair().1)
    }

    pub(crate) fn detach_value_head(&mut self, index: usize, next: Option<usize>, hash: u64) {
        let mut head = self.values.find_entry(hash, |&i| i == index).unwrap();
        if let Some(next) = next {
            *head.get_mut() = next;
        } else {
            head.remove();
        }
    }

    pub(crate) fn prepare_removals(&self, indices: &[usize]) -> PreparedRemovals {
        assert!(indices.len() <= 2);
        let mut hashes = [None; 4];
        let mut count = 0;
        for index in indices
            .iter()
            .copied()
            .chain((0..self.len()).rev().take(indices.len()))
        {
            if hashes.iter().flatten().any(|(i, _)| *i == index) {
                continue;
            }
            let pair = self.entries[index].pair();
            hashes[count] = Some((
                index,
                HashPair {
                    key: self.hash_builder.hash_one(&pair.0),
                    value: self.hash_builder.hash_one(&pair.1),
                },
            ));
            count += 1;
        }
        PreparedRemovals { hashes }
    }

    /// Group detachment happens before this commit. All user hashing was done
    /// in prepare_removals; this repairs indexes using only integer comparisons.
    pub(crate) fn remove_prepared(&mut self, index: usize, prepared: &mut PreparedRemovals) -> E {
        let key_hash = prepared.pair(index).key;
        let last = self.entries.len() - 1;
        let moved = (index != last).then(|| prepared.pair(last));
        self.keys
            .find_entry(key_hash, |&i| i == index)
            .unwrap()
            .remove();
        let entry = self.entries.swap_remove(index);
        if let Some(hashes) = moved {
            *self.keys.find_mut(hashes.key, |&i| i == last).unwrap() = index;
            if let Some(head) = self.values.find_mut(hashes.value, |&i| i == last) {
                *head = index;
            }
        }
        prepared.removed(index, last);
        entry
    }
}
