use crate::bidi_table::{BidiTable, TableEntry};
use hashbrown::DefaultHashBuilder;

use crate::{Drain, Equivalent, IntoIter, Iter, SurMap, TryReserveError};
use std::hash::{BuildHasher, Hash};

/// A one-to-one map: both keys and values are unique.
#[derive(Clone)]
pub struct BiMap<K, V, S = DefaultHashBuilder> {
    table: BidiTable<(K, V), S>,
}

/// Mappings displaced by a bijective insertion.
/// If the same mapping matches both key and value, it appears only in `by_key`.
#[derive(Debug, PartialEq, Eq)]
pub struct InsertResult<K, V> {
    pub by_key: Option<(K, V)>,
    pub by_value: Option<(K, V)>,
}

impl<K, V, S: Default> Default for BiMap<K, V, S> {
    fn default() -> Self {
        Self::with_hasher(S::default())
    }
}
impl<K, V> BiMap<K, V> {
    pub fn new() -> Self {
        Self::default()
    }
    pub fn with_capacity(capacity: usize) -> Self {
        Self::with_capacity_and_hasher(capacity, DefaultHashBuilder::default())
    }
}
impl<K, V, S> BiMap<K, V, S> {
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
    /// Minimum capacity across the entry vector and both hash indexes.
    pub fn capacity(&self) -> usize {
        self.table.capacity().min(self.table.value_capacity())
    }
    pub fn clear(&mut self) {
        self.table.clear();
    }
    pub fn iter(&self) -> Iter<'_, K, V> {
        Iter::from_bimap(self.table.entries().iter())
    }
    pub fn keys(
        &self,
    ) -> impl ExactSizeIterator<Item = &K> + DoubleEndedIterator + std::iter::FusedIterator {
        self.iter().map(|(k, _)| k)
    }
    pub fn values(
        &self,
    ) -> impl ExactSizeIterator<Item = &V> + DoubleEndedIterator + std::iter::FusedIterator {
        self.iter().map(|(_, v)| v)
    }
    pub fn drain(&mut self) -> Drain<'_, K, V> {
        Drain::from_bimap(self.table.drain())
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
impl<K: Hash + Eq, V: Hash + Eq, S: BuildHasher> BiMap<K, V, S> {
    pub fn reserve(&mut self, additional: usize) {
        self.table.reserve(additional);
    }
    pub fn try_reserve(&mut self, additional: usize) -> Result<(), TryReserveError> {
        self.table.try_reserve(additional)
    }
    pub fn shrink_to_fit(&mut self) {
        self.shrink_to(0);
    }
    pub fn shrink_to(&mut self, min_capacity: usize) {
        self.table.shrink_to(min_capacity);
    }
    fn key_index<Q: Hash + Equivalent<K> + ?Sized>(&self, key: &Q) -> Option<usize> {
        self.table.key_index(key)
    }
    fn value_index<Q: Hash + Equivalent<V> + ?Sized>(&self, value: &Q) -> Option<usize> {
        self.table.value_index(value)
    }
    pub fn get<Q: Hash + Equivalent<K> + ?Sized>(&self, key: &Q) -> Option<&V> {
        self.key_index(key).map(|i| &self.table.entries()[i].1)
    }
    pub fn get_key<Q: Hash + Equivalent<V> + ?Sized>(&self, value: &Q) -> Option<&K> {
        self.value_index(value).map(|i| &self.table.entries()[i].0)
    }
    pub fn get_key_value<Q: Hash + Equivalent<K> + ?Sized>(&self, key: &Q) -> Option<(&K, &V)> {
        self.key_index(key).map(|i| {
            let (k, v) = &self.table.entries()[i];
            (k, v)
        })
    }
    pub fn contains_key<Q: Hash + Equivalent<K> + ?Sized>(&self, key: &Q) -> bool {
        self.key_index(key).is_some()
    }
    pub fn contains_value<Q: Hash + Equivalent<V> + ?Sized>(&self, value: &Q) -> bool {
        self.value_index(value).is_some()
    }

    fn remove_index(&mut self, index: usize) -> (K, V) {
        let mut prepared = self.table.prepare_removals(&[index]);
        self.table
            .detach_value_head(index, None, prepared.value_hash(index));
        self.table.remove_prepared(index, &mut prepared)
    }

    /// Replaces mappings with the same key or value, returning both displaced pairs.
    /// On a hash/equality panic, mappings are unchanged.
    pub fn insert(&mut self, key: K, value: V) -> InsertResult<K, V> {
        let pair = (key, value);
        let mut prepared = self.table.prepare_insert(&pair);
        let mut conflicts = [0; 2];
        let mut count = 0;
        if let Some(index) = prepared.key_index {
            conflicts[count] = index;
            count += 1;
        }
        if let Some(index) = prepared.value_index {
            if Some(index) != prepared.key_index {
                conflicts[count] = index;
                count += 1;
            }
        }
        let mut removals = self.table.prepare_removals(&conflicts[..count]);
        let by_key = prepared.key_index.map(|index| {
            let last = self.len() - 1;
            self.table
                .detach_value_head(index, None, removals.value_hash(index));
            let pair = self.table.remove_prepared(index, &mut removals);
            if prepared.value_index == Some(index) {
                prepared.value_index = None;
            } else if prepared.value_index == Some(last) {
                prepared.value_index = Some(index);
            }
            pair
        });
        let by_value = prepared.value_index.map(|index| {
            self.table
                .detach_value_head(index, None, removals.value_hash(index));
            self.table.remove_prepared(index, &mut removals)
        });
        prepared.key_index = None;
        prepared.value_index = None;
        self.table.insert_prepared(pair, &prepared);
        InsertResult { by_key, by_value }
    }

    /// Inserts only if neither the key nor the value exists.
    /// Conflicts return the supplied pair without modifying the map.
    pub fn try_insert(&mut self, key: K, value: V) -> Result<(), (K, V)> {
        let pair = (key, value);
        let prepared = self.table.prepare_insert(&pair);
        if prepared.key_index.is_some() || prepared.value_index.is_some() {
            return Err(pair);
        }
        self.table.insert_prepared(pair, &prepared);
        Ok(())
    }
    pub fn remove<Q: Hash + Equivalent<K> + ?Sized>(&mut self, key: &Q) -> Option<V> {
        self.remove_entry(key).map(|(_, v)| v)
    }
    pub fn remove_entry<Q: Hash + Equivalent<K> + ?Sized>(&mut self, key: &Q) -> Option<(K, V)> {
        self.key_index(key).map(|i| self.remove_index(i))
    }
    pub fn remove_value<Q: Hash + Equivalent<V> + ?Sized>(&mut self, value: &Q) -> Option<K> {
        self.remove_value_entry(value).map(|(k, _)| k)
    }
    pub fn remove_value_entry<Q: Hash + Equivalent<V> + ?Sized>(
        &mut self,
        value: &Q,
    ) -> Option<(K, V)> {
        let index = self.value_index(value)?;
        Some(self.remove_index(index))
    }
    pub fn retain(&mut self, mut f: impl FnMut(&K, &V) -> bool) {
        let mut index = 0;
        while index < self.len() {
            let (key, value) = &self.table.entries()[index];
            if f(key, value) {
                index += 1;
            } else {
                self.remove_index(index);
            }
        }
    }
}
impl<K: std::fmt::Debug, V: std::fmt::Debug, S> std::fmt::Debug for BiMap<K, V, S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_map().entries(self.iter()).finish()
    }
}
impl<K, V, S> IntoIterator for BiMap<K, V, S> {
    type Item = (K, V);
    type IntoIter = IntoIter<K, V>;
    fn into_iter(self) -> Self::IntoIter {
        IntoIter::from_bimap(self.table.into_entries())
    }
}
impl<'a, K, V, S> IntoIterator for &'a BiMap<K, V, S> {
    type Item = (&'a K, &'a V);
    type IntoIter = Iter<'a, K, V>;
    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}
impl<K: Hash + Eq, V: Hash + Eq, S: BuildHasher + Default> FromIterator<(K, V)> for BiMap<K, V, S> {
    fn from_iter<T: IntoIterator<Item = (K, V)>>(iter: T) -> Self {
        let mut map = Self::default();
        map.extend(iter);
        map
    }
}
impl<K: Hash + Eq, V: Hash + Eq, S: BuildHasher> Extend<(K, V)> for BiMap<K, V, S> {
    fn extend<T: IntoIterator<Item = (K, V)>>(&mut self, iter: T) {
        for (k, v) in iter {
            self.insert(k, v);
        }
    }
}
impl<K: Hash + Eq, V: Hash + Eq, const N: usize> From<[(K, V); N]> for BiMap<K, V> {
    fn from(pairs: [(K, V); N]) -> Self {
        pairs.into_iter().collect()
    }
}
impl<K: Hash + Eq, V: Hash + Eq, S: BuildHasher, T: BuildHasher> PartialEq<BiMap<K, V, T>>
    for BiMap<K, V, S>
{
    fn eq(&self, other: &BiMap<K, V, T>) -> bool {
        self.len() == other.len() && self.iter().all(|(k, v)| other.get(k) == Some(v))
    }
}
impl<K: Hash + Eq, V: Hash + Eq, S: BuildHasher> Eq for BiMap<K, V, S> {}

impl<K, V, S> TryFrom<SurMap<K, V, S>> for BiMap<K, V, S> {
    type Error = SurMap<K, V, S>;

    /// Moves mappings into compact pair storage, reusing the indexes and hasher.
    /// If values are not unique, returns the original map unchanged.
    fn try_from(map: SurMap<K, V, S>) -> Result<Self, Self::Error> {
        if map.len() != map.value_len() {
            return Err(map);
        }
        Ok(Self {
            table: map.into_table().map_entries(TableEntry::into_pair),
        })
    }
}

impl<K, V, S> From<BiMap<K, V, S>> for SurMap<K, V, S> {
    fn from(map: BiMap<K, V, S>) -> Self {
        SurMap::from_table(map.table.map_entries(crate::surmap::Entry::from))
    }
}
