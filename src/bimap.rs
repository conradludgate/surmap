use crate::bidi_table::{BidiTable, TableEntry};
use hashbrown::DefaultHashBuilder;

use crate::{Drain, Equivalent, IntoIter, Iter, SurMap, TryReserveError};
use std::hash::{BuildHasher, Hash};

/// A one-to-one map: both keys and values are unique.
///
/// [`insert`](Self::insert) replaces conflicting mappings; [`try_insert`](Self::try_insert)
/// rejects them. [`get_key`](Self::get_key) provides reverse lookup. Keys and
/// values are stored once, without a `Clone` requirement for insertion or removal.
///
/// Queries may use borrowed types implementing [`Equivalent`], provided their
/// hashes match those of the stored keys or values they match.
#[derive(Clone)]
pub struct BiMap<K, V, S = DefaultHashBuilder> {
    table: BidiTable<(K, V), S>,
}

/// Mappings displaced by a bijective insertion.
/// A pair matching both key and value appears only in [`by_key`](Self::by_key).
#[derive(Debug, PartialEq, Eq)]
pub struct InsertResult<K, V> {
    /// The displaced pair with an equal key, if any.
    pub by_key: Option<(K, V)>,
    /// The displaced pair with an equal value, excluding the pair in [`by_key`](Self::by_key).
    pub by_value: Option<(K, V)>,
}

impl<K, V, S: Default> Default for BiMap<K, V, S> {
    fn default() -> Self {
        Self::with_hasher(S::default())
    }
}
impl<K, V> BiMap<K, V> {
    /// Creates an empty map with the default hash builder, without allocating.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }
    /// Creates an empty map with room for at least `capacity` mappings.
    #[must_use]
    pub fn with_capacity(capacity: usize) -> Self {
        Self::with_capacity_and_hasher(capacity, DefaultHashBuilder::default())
    }
}
impl<K, V, S> BiMap<K, V, S> {
    /// Creates an empty map with the supplied hash builder, without allocating.
    pub fn with_hasher(hash_builder: S) -> Self {
        Self::with_capacity_and_hasher(0, hash_builder)
    }
    /// Creates a map with the supplied hasher and room for `capacity` mappings.
    pub fn with_capacity_and_hasher(capacity: usize, hash_builder: S) -> Self {
        Self {
            table: BidiTable::with_capacity_and_hasher(capacity, hash_builder),
        }
    }
    /// Returns the hash builder used by both indexes.
    pub fn hasher(&self) -> &S {
        self.table.hasher()
    }
    /// Returns the number of mappings.
    pub fn len(&self) -> usize {
        self.table.len()
    }
    /// Returns whether the map contains no mappings.
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
    /// Minimum capacity across the entry vector and both hash indexes.
    pub fn capacity(&self) -> usize {
        self.table.capacity().min(self.table.value_capacity())
    }
    /// Removes and drops all mappings, retaining allocated storage.
    pub fn clear(&mut self) {
        self.table.clear();
    }
    /// Iterates over key/value references in storage order. Removal may reorder entries.
    pub fn iter(&self) -> Iter<'_, K, V> {
        Iter::from_bimap(self.table.entries().iter())
    }
    /// Iterates over key references in [`iter`](Self::iter) order.
    pub fn keys(
        &self,
    ) -> impl ExactSizeIterator<Item = &K> + DoubleEndedIterator + std::iter::FusedIterator {
        self.iter().map(|(k, _)| k)
    }
    /// Iterates over value references in [`iter`](Self::iter) order.
    pub fn values(
        &self,
    ) -> impl ExactSizeIterator<Item = &V> + DoubleEndedIterator + std::iter::FusedIterator {
        self.iter().map(|(_, v)| v)
    }
    /// Removes all mappings and yields owned pairs in storage order, retaining
    /// allocated storage. Dropping the iterator drops any remaining pairs.
    ///
    /// ```
    /// use surmap::BiMap;
    /// let mut map = BiMap::from([(1, "one"), (2, "two")]);
    /// let capacity = map.capacity();
    /// assert_eq!(map.drain().collect::<Vec<_>>(), [(1, "one"), (2, "two")]);
    /// assert!(map.is_empty());
    /// assert_eq!(map.capacity(), capacity);
    /// ```
    pub fn drain(&mut self) -> Drain<'_, K, V> {
        Drain::from_bimap(self.table.drain())
    }
    /// Consumes the map and yields keys in storage order.
    /// Each value is dropped when its key is yielded. Dropping the iterator
    /// drops all remaining pairs.
    pub fn into_keys(
        self,
    ) -> impl ExactSizeIterator<Item = K> + DoubleEndedIterator + std::iter::FusedIterator {
        self.into_iter().map(|(k, _)| k)
    }
    /// Consumes the map and yields values in storage order.
    /// Each key is dropped when its value is yielded. Dropping the iterator
    /// drops all remaining pairs.
    pub fn into_values(
        self,
    ) -> impl ExactSizeIterator<Item = V> + DoubleEndedIterator + std::iter::FusedIterator {
        self.into_iter().map(|(_, v)| v)
    }
}
impl<K: Hash + Eq, V: Hash + Eq, S: BuildHasher> BiMap<K, V, S> {
    /// Reserves room for `additional` more mappings in the entry vector and both indexes.
    pub fn reserve(&mut self, additional: usize) {
        self.table.reserve(additional);
    }
    /// Fallible version of [`reserve`](Self::reserve).
    ///
    /// # Errors
    /// Returns an error if capacity overflows or an allocation fails. Some
    /// allocations may already have grown when an error is returned.
    pub fn try_reserve(&mut self, additional: usize) -> Result<(), TryReserveError> {
        self.table.try_reserve(additional)
    }
    /// Shrinks all allocations as far as the current mappings allow.
    pub fn shrink_to_fit(&mut self) {
        self.shrink_to(0);
    }
    /// Shrinks allocations toward `min_capacity`, retaining room for existing
    /// mappings. Does not grow smaller allocations.
    pub fn shrink_to(&mut self, min_capacity: usize) {
        self.table.shrink_to(min_capacity);
    }
    fn key_index<Q: Hash + Equivalent<K> + ?Sized>(&self, key: &Q) -> Option<usize> {
        self.table.key_index(key)
    }
    fn value_index<Q: Hash + Equivalent<V> + ?Sized>(&self, value: &Q) -> Option<usize> {
        self.table.value_index(value)
    }
    /// Returns the value associated with `key`, or `None` if absent.
    pub fn get<Q: Hash + Equivalent<K> + ?Sized>(&self, key: &Q) -> Option<&V> {
        self.key_index(key).map(|i| &self.table.entries()[i].1)
    }
    /// Returns the key associated with `value`, or `None` if absent.
    ///
    /// ```
    /// use surmap::BiMap;
    /// let map = BiMap::from([(String::from("alice"), String::from("engineering"))]);
    /// assert_eq!(map.get_key("engineering").map(String::as_str), Some("alice"));
    /// assert_eq!(map.get_key("missing"), None);
    /// ```
    pub fn get_key<Q: Hash + Equivalent<V> + ?Sized>(&self, value: &Q) -> Option<&K> {
        self.value_index(value).map(|i| &self.table.entries()[i].0)
    }
    /// Returns references to the stored key and its value, or `None` if absent.
    pub fn get_key_value<Q: Hash + Equivalent<K> + ?Sized>(&self, key: &Q) -> Option<(&K, &V)> {
        self.key_index(key).map(|i| {
            let (k, v) = &self.table.entries()[i];
            (k, v)
        })
    }
    /// Returns whether a mapping with an equivalent key exists.
    pub fn contains_key<Q: Hash + Equivalent<K> + ?Sized>(&self, key: &Q) -> bool {
        self.key_index(key).is_some()
    }
    /// Returns whether a mapping with an equivalent value exists.
    pub fn contains_value<Q: Hash + Equivalent<V> + ?Sized>(&self, value: &Q) -> bool {
        self.value_index(value).is_some()
    }

    fn remove_index(&mut self, index: usize) -> (K, V) {
        let mut prepared = self.table.prepare_removals(&[index]);
        self.table
            .detach_value_head(index, None, prepared.value_hash(index));
        self.table.remove_prepared(index, &mut prepared)
    }

    /// Stores the supplied pair, removing any mappings with an equal key or value.
    ///
    /// Returns displaced pairs in [`InsertResult`]. Even when the supplied pair
    /// equals an existing pair, both stored objects are replaced.
    ///
    /// A panic in hashing or equality leaves mappings unchanged. Capacity may
    /// increase during preparation.
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
    /// Capacity may grow even if insertion is rejected.
    ///
    /// # Errors
    /// Returns the supplied pair on a key or value conflict, leaving mappings unchanged.
    pub fn try_insert(&mut self, key: K, value: V) -> Result<(), (K, V)> {
        let pair = (key, value);
        let prepared = self.table.prepare_insert(&pair);
        if prepared.key_index.is_some() || prepared.value_index.is_some() {
            return Err(pair);
        }
        self.table.insert_prepared(pair, &prepared);
        Ok(())
    }
    /// Removes the mapping for `key`, returning its value or `None` if absent.
    pub fn remove<Q: Hash + Equivalent<K> + ?Sized>(&mut self, key: &Q) -> Option<V> {
        self.remove_entry(key).map(|(_, v)| v)
    }
    /// Removes the mapping for `key`, returning the owned stored pair or `None`.
    pub fn remove_entry<Q: Hash + Equivalent<K> + ?Sized>(&mut self, key: &Q) -> Option<(K, V)> {
        self.key_index(key).map(|i| self.remove_index(i))
    }
    /// Removes the mapping for `value`, returning its key or `None` if absent.
    pub fn remove_value<Q: Hash + Equivalent<V> + ?Sized>(&mut self, value: &Q) -> Option<K> {
        self.remove_value_entry(value).map(|(k, _)| k)
    }
    /// Removes the mapping for `value`, returning the owned stored pair or `None`.
    pub fn remove_value_entry<Q: Hash + Equivalent<V> + ?Sized>(
        &mut self,
        value: &Q,
    ) -> Option<(K, V)> {
        let index = self.value_index(value)?;
        Some(self.remove_index(index))
    }
    /// Keeps only mappings for which `f(&key, &value)` returns `true`.
    /// Each mapping is visited once, in unspecified order. If `f` panics,
    /// completed removals remain in effect and the map remains usable.
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
    ///
    /// ```
    /// use surmap::{BiMap, SurMap};
    /// let original = SurMap::from([("a", 1), ("b", 1)]);
    /// let mut original = BiMap::try_from(original).unwrap_err();
    /// original.insert("b", 2);
    /// let bijective = BiMap::try_from(original).unwrap();
    /// assert_eq!(bijective.get_key(&2), Some(&"b"));
    /// ```
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
