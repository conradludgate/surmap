use std::hash::{BuildHasher, Hash};

use hashbrown::DefaultHashBuilder;

use crate::bidi_table::{BidiTable, TableEntry};

use crate::{Drain, Equivalent, Iter, SurMapKeysIter, TryReserveError};

/// A surjective hash map.
///
/// Each key maps to one value; [`get_keys`](Self::get_keys) returns all keys
/// with an equal value. Each pair is owned once, without a `Clone` requirement
/// for insertion or removal.
///
/// Queries may use borrowed types implementing [`Equivalent`], provided their
/// hashes match those of the stored keys or values they match.
///
/// Values are owned per mapping. Shared values can use [`std::rc::Rc`]:
///
/// ```
/// use std::rc::Rc;
/// use surmap::SurMap;
/// let team: Rc<str> = Rc::from("engineering");
/// let mut map = SurMap::new();
/// map.insert(String::from("alice"), Rc::clone(&team));
/// map.insert(String::from("bob"), Rc::clone(&team));
/// assert!(Rc::ptr_eq(map.get("alice").unwrap(), map.get("bob").unwrap()));
/// assert_eq!(map.get_keys("engineering").count(), 2);
/// ```
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
    /// Creates an empty map with the default hash builder, without allocating.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Creates an empty map with space for at least `capacity` mappings and values.
    #[must_use]
    pub fn with_capacity(capacity: usize) -> Self {
        Self::with_capacity_and_hasher(capacity, DefaultHashBuilder::default())
    }
}

impl<K, V, S> SurMap<K, V, S> {
    /// Creates an empty map with the supplied hash builder, without allocating.
    pub fn with_hasher(hash_builder: S) -> Self {
        Self::with_capacity_and_hasher(0, hash_builder)
    }

    /// Creates a map with the supplied hasher and room for `capacity` mappings
    /// and distinct values.
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

    /// Returns the number of distinct values, which may be smaller than [`len`](Self::len).
    pub fn value_len(&self) -> usize {
        self.table.value_len()
    }

    /// Capacity of the entry vector and key index. New distinct values may
    /// separately grow the value index; see [`value_capacity`](Self::value_capacity).
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

    /// Iterates over key/value references in storage order. Removal may reorder entries.
    pub fn iter(&self) -> Iter<'_, K, V> {
        Iter::from_surmap(self.table.entries().iter())
    }

    /// Iterates over key references in [`iter`](Self::iter) order.
    pub fn keys(
        &self,
    ) -> impl ExactSizeIterator<Item = &K> + DoubleEndedIterator + std::iter::FusedIterator {
        self.iter().map(|(k, _)| k)
    }

    /// Iterates over value references in [`iter`](Self::iter) order, including duplicates.
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

    /// Consumes the map and yields keys in storage order.
    /// Each value is dropped when its key is yielded. Dropping the iterator
    /// drops all remaining pairs.
    pub fn into_keys(
        self,
    ) -> impl ExactSizeIterator<Item = K> + DoubleEndedIterator + std::iter::FusedIterator {
        self.into_iter().map(|(k, _)| k)
    }

    /// Consumes the map and yields one value per mapping in storage order,
    /// including duplicates. Each key is dropped when its value is yielded.
    /// Dropping the iterator drops all remaining pairs.
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

    /// Fallible version of [`reserve`](Self::reserve).
    ///
    /// # Errors
    /// Returns an error on capacity overflow or allocation failure. Mappings
    /// are unchanged, but some allocations may already have grown.
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

    /// Returns whether a mapping with an equivalent key exists.
    pub fn contains_key<Q: Hash + Equivalent<K> + ?Sized>(&self, key: &Q) -> bool {
        self.get(key).is_some()
    }

    /// Returns whether at least one mapping has an equivalent value.
    pub fn contains_value<Q: Hash + Equivalent<V> + ?Sized>(&self, value: &Q) -> bool {
        self.value_index(value).is_some()
    }

    /// Returns references to the stored key and its value, or `None` if absent.
    pub fn get_key_value<Q: Hash + Equivalent<K> + ?Sized>(&self, key: &Q) -> Option<(&K, &V)> {
        self.get_inner(key).map(|(k, v)| (k, v))
    }

    /// Keeps mappings for which `f(&key, &value)` returns `true`.
    /// Each mapping is visited once, in unspecified order. Retained groups keep
    /// their relative key order. If `f` panics, completed removals remain in
    /// effect and the map remains usable.
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

    /// Inserts a mapping, returning the previous value for an equal key, if any.
    ///
    /// New keys are linked at the head of the value's group. Reassigning a key
    /// to a different value replaces the stored key and moves it to the head
    /// of the new group. If the new value equals the old one, the stored key
    /// and group position are retained. The supplied value is stored in both cases.
    ///
    /// A panic in hashing or equality leaves mappings and group order unchanged.
    /// Capacity may increase during preparation.
    ///
    /// ```
    /// use surmap::SurMap;
    /// let mut map = SurMap::from([("a", 1), ("b", 1), ("c", 2)]);
    /// assert_eq!(map.insert("a", 2), Some(1));
    /// assert_eq!(map.get_keys(&1).copied().collect::<Vec<_>>(), ["b"]);
    /// assert_eq!(map.get_keys(&2).copied().collect::<Vec<_>>(), ["a", "c"]);
    /// ```
    pub fn insert(&mut self, key: K, value: V) -> Option<V> {
        let new_entry = Entry::from((key, value));
        let prepared = self.table.prepare_insert(&new_entry.pair);
        let (index, result) = if let Some(index) = prepared.key_index {
            let entry = self.table.entry_mut(index);
            if entry.pair.1 == new_entry.pair.1 {
                return Some(std::mem::replace(&mut entry.pair.1, new_entry.pair.1));
            }
            let old_hash = self.table.value_hash(index);
            self.unlink_value(index, old_hash);
            let old = std::mem::replace(self.table.entry_mut(index), new_entry);
            self.table.link_value_prepared(index, &prepared);
            (index, Some(old.pair.1))
        } else {
            let index = self.table.insert_prepared(new_entry, &prepared);
            (index, None)
        };
        if let Some(next) = prepared.value_index {
            self.table.entry_mut(index).ptrs.1 = next;
            self.table.entry_mut(next).ptrs.0 = index;
        }
        result
    }

    // Detach an entry while its value and all entry indexes are still valid.
    fn unlink_value(&mut self, index: usize, value_hash: u64) {
        let (prev, next) = self.table.entries()[index].ptrs;
        if prev == usize::MAX {
            self.table
                .detach_value_head(index, (next != usize::MAX).then_some(next), value_hash);
        } else {
            self.table.entry_mut(prev).ptrs.1 = next;
        }
        if next != usize::MAX {
            self.table.entry_mut(next).ptrs.0 = prev;
        }
    }

    /// Removes the mapping for `k`, returning its value or `None` if absent.
    /// Other keys in the value group keep their relative order.
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

    /// Removes the mapping for `k`, returning the owned stored pair or `None`.
    /// Other keys in the value group keep their relative order.
    pub fn remove_entry<Q>(&mut self, k: &Q) -> Option<(K, V)>
    where
        Q: Hash + Equivalent<K> + ?Sized,
    {
        let index = self.table.key_index(k)?;
        Some(self.remove_index(index))
    }

    fn remove_index(&mut self, index: usize) -> (K, V) {
        let mut prepared = self.table.prepare_removals(&[index]);
        self.unlink_value(index, prepared.value_hash(index));
        let entry = self.table.remove_prepared(index, &mut prepared);
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

    /// Returns the value associated with `k`, or `None` if absent.
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

    /// Iterates over all keys with a value equivalent to `v`.
    ///
    /// The most recently linked key is visited first. An absent value produces
    /// an empty iterator. Constructing the iterator takes expected O(1) time;
    /// advancing it takes O(1) time per key.
    ///
    /// ```
    /// use surmap::SurMap;
    /// let map = SurMap::from([("alice", "team"), ("bob", "team")]);
    /// assert_eq!(map.get_keys("team").copied().collect::<Vec<_>>(), ["bob", "alice"]);
    /// assert_eq!(map.get_keys("missing").next(), None);
    /// ```
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
