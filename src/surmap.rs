use std::hash::{BuildHasher, Hash};

use hashbrown::DefaultHashBuilder;

use crate::bidi_table::{BidiTable, TableEntry};

use crate::{Drain, Equivalent, Iter, SurMapKeysIter, TryReserveError};

/// A Surjective HashMap.
///
/// Key -> Value
/// Value -> [Key]
#[derive(Clone)]
pub struct SurMap<K, V, S = DefaultHashBuilder> {
    table: BidiTable<Entry<K, V>, S>,
}

impl<K, V, S: Default> Default for SurMap<K, V, S> {
    fn default() -> Self {
        Self::with_hasher(S::default())
    }
}

impl<K, V> SurMap<K, V> {
    pub fn new() -> Self {
        Self::default()
    }

    /// Creates an empty map with space for at least `capacity` mappings and values.
    pub fn with_capacity(capacity: usize) -> Self {
        Self::with_capacity_and_hasher(capacity, DefaultHashBuilder::default())
    }
}

impl<K, V, S> SurMap<K, V, S> {
    pub fn with_hasher(hash_builder: S) -> Self {
        Self::with_capacity_and_hasher(0, hash_builder)
    }

    pub fn with_capacity_and_hasher(capacity: usize, hash_builder: S) -> Self {
        Self {
            table: BidiTable::with_capacity_and_hasher(capacity, hash_builder),
        }
    }

    pub fn hasher(&self) -> &S {
        self.table.hasher()
    }

    pub fn len(&self) -> usize {
        self.table.len()
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Number of distinct values, which may be smaller than `len()`.
    pub fn value_len(&self) -> usize {
        self.table.value_len()
    }

    /// Capacity of the entry vector and key index. New distinct values may
    /// separately grow the value index; see `value_capacity`.
    pub fn capacity(&self) -> usize {
        self.table.capacity()
    }

    /// Number of distinct values the reverse index can hold without growth.
    pub fn value_capacity(&self) -> usize {
        self.table.value_capacity()
    }

    /// Removes all mappings, keeping allocated storage.
    pub fn clear(&mut self) {
        self.table.clear();
    }

    /// Iteration follows vector order, which can change after removals.
    pub fn iter(&self) -> Iter<'_, K, V> {
        Iter::from_surmap(self.table.entries().iter())
    }

    pub fn keys(
        &self,
    ) -> impl ExactSizeIterator<Item = &K> + DoubleEndedIterator + std::iter::FusedIterator {
        self.iter().map(|(k, _)| k)
    }

    /// Yields one value per mapping, including equal values.
    pub fn values(
        &self,
    ) -> impl ExactSizeIterator<Item = &V> + DoubleEndedIterator + std::iter::FusedIterator {
        self.iter().map(|(_, v)| v)
    }

    /// Yields one representative per distinct value in arbitrary index order.
    pub fn distinct_values(&self) -> impl ExactSizeIterator<Item = &V> + std::iter::FusedIterator {
        self.table
            .value_heads()
            .map(|i| &self.table.entries()[i].pair.1)
    }

    /// Removes all mappings and yields their owned pairs, retaining storage.
    /// Dropping the iterator also drops any remaining pairs.
    pub fn drain(&mut self) -> Drain<'_, K, V> {
        Drain::from_surmap(self.table.drain())
    }

    pub fn into_keys(
        self,
    ) -> impl ExactSizeIterator<Item = K> + DoubleEndedIterator + std::iter::FusedIterator {
        self.into_iter().map(|(k, _)| k)
    }

    pub fn into_values(
        self,
    ) -> impl ExactSizeIterator<Item = V> + DoubleEndedIterator + std::iter::FusedIterator {
        self.into_iter().map(|(_, v)| v)
    }
}

impl<K, V, S> SurMap<K, V, S> {
    pub(crate) fn into_table(self) -> BidiTable<Entry<K, V>, S> {
        self.table
    }
    pub(crate) fn from_table(table: BidiTable<Entry<K, V>, S>) -> Self {
        Self { table }
    }
    pub(crate) fn group_entry(&self, index: usize) -> Option<(&K, usize)> {
        self.table
            .entries()
            .get(index)
            .map(|entry| (&entry.pair.0, entry.ptrs.1))
    }
    #[cfg(feature = "serde")]
    pub(crate) fn serialize_entries<E>(
        &self,
        mut f: impl FnMut(&K, &V) -> Result<(), E>,
    ) -> Result<(), E> {
        let mut group = Vec::new();
        for head in self.table.value_heads() {
            group.clear();
            let mut index = head;
            while index != usize::MAX {
                group.push(index);
                index = self.table.entries()[index].ptrs.1;
            }
            for &index in group.iter().rev() {
                let (key, value) = &self.table.entries()[index].pair;
                f(key, value)?;
            }
        }
        Ok(())
    }
}

impl<K: Hash + Eq, V: Hash + Eq, S: BuildHasher> SurMap<K, V, S> {
    /// Reserves room for `additional` mappings and distinct values.
    pub fn reserve(&mut self, additional: usize) {
        self.table.reserve(additional);
    }

    /// On failure mappings are unchanged, but some storage may have grown.
    pub fn try_reserve(&mut self, additional: usize) -> Result<(), TryReserveError> {
        self.table.try_reserve(additional)
    }

    /// Shrinks each allocation as far as its current contents allow.
    pub fn shrink_to_fit(&mut self) {
        self.shrink_to(0);
    }

    /// Shrinks each allocation toward `min_capacity` without growing it.
    pub fn shrink_to(&mut self, min_capacity: usize) {
        self.table.shrink_to(min_capacity);
    }

    pub fn contains_key<Q: Hash + Equivalent<K> + ?Sized>(&self, key: &Q) -> bool {
        self.get(key).is_some()
    }

    pub fn contains_value<Q: Hash + Equivalent<V> + ?Sized>(&self, value: &Q) -> bool {
        self.value_index(value).is_some()
    }

    pub fn get_key_value<Q: Hash + Equivalent<K> + ?Sized>(&self, key: &Q) -> Option<(&K, &V)> {
        self.get_inner(key).map(|(k, v)| (k, v))
    }

    /// Tests each mapping once with a shared key and value reference.
    /// Retained value groups keep their order; overall storage order may change.
    pub fn retain(&mut self, mut f: impl FnMut(&K, &V) -> bool) {
        let mut index = 0;
        while index < self.len() {
            let (key, value) = &self.table.entries()[index].pair;
            if f(key, value) {
                index += 1;
            } else {
                self.remove_index(index);
            }
        }
    }

    fn value_index<Q: Hash + Equivalent<V> + ?Sized>(&self, value: &Q) -> Option<usize> {
        self.table.value_index(value)
    }

    pub fn insert(&mut self, key: K, value: V) -> Option<V> {
        let new_entry = Entry::from((key, value));
        let (index, result, previous) = if let Some(index) = self.table.key_index(&new_entry.pair.0)
        {
            let entry = self.table.entry_mut(index);
            if entry.pair.1 == new_entry.pair.1 {
                return Some(std::mem::replace(&mut entry.pair.1, new_entry.pair.1));
            }
            self.unlink_value(index);
            let old = std::mem::replace(self.table.entry_mut(index), new_entry);
            let previous = self.table.link_value(index);
            (index, Some(old.pair.1), previous)
        } else {
            let (index, previous) = self.table.insert_entry(new_entry);
            (index, None, previous)
        };
        if let Some(next) = previous {
            self.table.entry_mut(index).ptrs.1 = next;
            self.table.entry_mut(next).ptrs.0 = index;
        }
        result
    }

    // Detach an entry while its value and all entry indexes are still valid.
    fn unlink_value(&mut self, index: usize) {
        let (prev, next) = self.table.entries()[index].ptrs;
        if prev == usize::MAX {
            self.table
                .detach_value_head(index, (next != usize::MAX).then_some(next));
        } else {
            self.table.entry_mut(prev).ptrs.1 = next;
        }
        if next != usize::MAX {
            self.table.entry_mut(next).ptrs.0 = prev;
        }
    }

    pub fn remove<Q>(&mut self, k: &Q) -> Option<V>
    where
        Q: Hash + Equivalent<K> + ?Sized,
    {
        // Avoid `Option::map` because it bloats LLVM IR.
        #[allow(clippy::manual_map)]
        match self.remove_entry(k) {
            Some((_, v)) => Some(v),
            None => None,
        }
    }

    pub fn remove_entry<Q>(&mut self, k: &Q) -> Option<(K, V)>
    where
        Q: Hash + Equivalent<K> + ?Sized,
    {
        let index = self.table.key_index(k)?;
        Some(self.remove_index(index))
    }

    fn remove_index(&mut self, index: usize) -> (K, V) {
        self.unlink_value(index);
        let entry = self.table.remove_entry(index);
        if index < self.len() {
            let (prev, next) = self.table.entries()[index].ptrs;
            if prev != usize::MAX {
                self.table.entry_mut(prev).ptrs.1 = index;
            }
            if next != usize::MAX {
                self.table.entry_mut(next).ptrs.0 = index;
            }
        }
        entry.pair
    }

    #[inline]
    pub fn get<Q>(&self, k: &Q) -> Option<&V>
    where
        Q: Hash + Equivalent<K> + ?Sized,
    {
        // Avoid `Option::map` because it bloats LLVM IR.
        #[allow(clippy::manual_map)]
        match self.get_inner(k) {
            Some((_, v)) => Some(v),
            None => None,
        }
    }

    #[inline]
    fn get_inner<Q>(&self, k: &Q) -> Option<&(K, V)>
    where
        Q: Hash + Equivalent<K> + ?Sized,
    {
        let index = self.table.key_index(k)?;
        Some(&self.table.entries()[index].pair)
    }

    #[inline]
    pub fn get_keys<Q>(&self, v: &Q) -> SurMapKeysIter<'_, K, V, S>
    where
        Q: Hash + Equivalent<V> + ?Sized,
    {
        let entry = self.value_index(v).unwrap_or(usize::MAX);
        SurMapKeysIter { map: self, entry }
    }
}

#[derive(Clone)]
pub(crate) struct Entry<K, V> {
    pair: (K, V),
    ptrs: (usize, usize),
}

impl<K, V> TableEntry for Entry<K, V> {
    type Key = K;
    type Value = V;
    fn pair(&self) -> &(K, V) {
        &self.pair
    }
    fn into_pair(self) -> (K, V) {
        self.pair
    }
}
impl<K, V> From<(K, V)> for Entry<K, V> {
    fn from(pair: (K, V)) -> Self {
        Self {
            pair,
            ptrs: (usize::MAX, usize::MAX),
        }
    }
}
impl<K, V, S> IntoIterator for SurMap<K, V, S> {
    type Item = (K, V);
    type IntoIter = crate::IntoIter<K, V>;
    fn into_iter(self) -> Self::IntoIter {
        crate::IntoIter::from_surmap(self.table.into_entries())
    }
}

impl<K: std::fmt::Debug, V: std::fmt::Debug, S> std::fmt::Debug for SurMap<K, V, S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_map().entries(self.iter()).finish()
    }
}

impl<K: Hash + Eq, V: Hash + Eq, S: BuildHasher + Default> FromIterator<(K, V)>
    for SurMap<K, V, S>
{
    fn from_iter<T: IntoIterator<Item = (K, V)>>(iter: T) -> Self {
        let mut map = Self::default();
        map.extend(iter);
        map
    }
}

impl<K: Hash + Eq, V: Hash + Eq, S: BuildHasher> Extend<(K, V)> for SurMap<K, V, S> {
    fn extend<T: IntoIterator<Item = (K, V)>>(&mut self, iter: T) {
        for (key, value) in iter {
            self.insert(key, value);
        }
    }
}

impl<K: Hash + Eq, V: Hash + Eq, const N: usize> From<[(K, V); N]> for SurMap<K, V> {
    fn from(pairs: [(K, V); N]) -> Self {
        pairs.into_iter().collect()
    }
}

impl<K: Hash + Eq, V: Hash + Eq, S: BuildHasher, T: BuildHasher> PartialEq<SurMap<K, V, T>>
    for SurMap<K, V, S>
{
    fn eq(&self, other: &SurMap<K, V, T>) -> bool {
        self.len() == other.len() && self.iter().all(|(k, v)| other.get(k) == Some(v))
    }
}

impl<K: Hash + Eq, V: Hash + Eq, S: BuildHasher> Eq for SurMap<K, V, S> {}
