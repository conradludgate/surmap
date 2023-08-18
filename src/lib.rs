use std::hash::{BuildHasher, Hash};

pub use hashbrown::Equivalent;
use hashbrown::{hash_map::DefaultHashBuilder, raw::RawTable};

/// A Surjective HashMap.
///
/// Key -> Value
/// Value -> [Key]
pub struct SurMap<K, V, S = DefaultHashBuilder> {
    hash_builder: S,
    entries: Vec<Entry<K, V>>,
    // points to the entry that contains this key
    keys: RawTable<usize>,
    // points to the first entry that contains this value
    values: RawTable<usize>,
}

impl<K, V, S: Default> Default for SurMap<K, V, S> {
    fn default() -> Self {
        SurMap {
            hash_builder: S::default(),
            entries: Vec::new(),
            keys: RawTable::new(),
            values: RawTable::new(),
        }
    }
}

impl<K, V> SurMap<K, V> {
    pub fn new() -> Self {
        Self::default()
    }
}

impl<K: Hash + Eq, V: Hash + Eq, S: BuildHasher> SurMap<K, V, S> {
    pub fn insert(&mut self, key: K, value: V) -> Option<V> {
        let mut index = self.entries.len();

        let key_hash = make_hash(&self.hash_builder, &key);
        let value_hash = make_hash(&self.hash_builder, &value);

        let new_entry = Entry {
            pair: (key, value),
            ptrs: (usize::MAX, usize::MAX),
        };

        let result;

        let key_hasher =
            |&key_idx: &usize| make_hash::<K, S>(&self.hash_builder, &self.entries[key_idx].pair.0);
        match self.keys.find_or_find_insert_slot(
            key_hash,
            |&key_idx| self.entries[key_idx].pair.0 == new_entry.pair.0,
            key_hasher,
        ) {
            Ok(bucket) => {
                // SAFETY:
                // we know this pointer is valid as the table found this slot for us
                index = unsafe { *bucket.as_ref() };

                // table index always points inside the entries
                let entry = unsafe { self.entries.get_unchecked_mut(index) };

                // optimisation
                if new_entry.pair.1 == entry.pair.1 {
                    return Some(std::mem::replace(&mut entry.pair.1, new_entry.pair.1));
                }

                let old_entry = std::mem::replace(entry, new_entry);
                // fix pointers
                if let Some(prev) = self.entries.get_mut(old_entry.ptrs.0) {
                    prev.ptrs.1 = old_entry.ptrs.1;
                }
                if let Some(next) = self.entries.get_mut(old_entry.ptrs.1) {
                    next.ptrs.0 = old_entry.ptrs.0;
                }
                result = Some(old_entry.pair.1);
            }
            Err(slot) => {
                // SAFETY:
                // slot must point to a slot previously returned by find_or_find_insert_slot
                // and no mutation of the table must have occurred since that call.
                unsafe { self.keys.insert_in_slot(key_hash, slot, index) };
                self.entries.push(new_entry);
                result = None;
            }
        }

        let value_hasher =
            |&val_idx: &usize| make_hash::<V, S>(&self.hash_builder, &self.entries[val_idx].pair.1);
        match self.values.find_or_find_insert_slot(
            value_hash,
            |&val_idx| self.entries[val_idx].pair.1 == self.entries[index].pair.1,
            value_hasher,
        ) {
            // this value is known. add it to the linked list
            Ok(bucket) => {
                // SAFETY:
                // we know this pointer is valid as the table found this slot for us
                self.entries[index].ptrs.1 = unsafe { std::mem::replace(bucket.as_mut(), index) };
            }
            Err(slot) => {
                // SAFETY:
                // slot must point to a slot previously returned by find_or_find_insert_slot
                // and no mutation of the table must have occurred since that call.
                unsafe { self.values.insert_in_slot(value_hash, slot, index) };
            }
        }

        result
    }

    pub fn remove<Q: ?Sized>(&mut self, k: &Q) -> Option<V>
    where
        Q: Hash + Equivalent<K>,
    {
        // Avoid `Option::map` because it bloats LLVM IR.
        #[allow(clippy::manual_map)]
        match self.remove_entry(k) {
            Some((_, v)) => Some(v),
            None => None,
        }
    }

    pub fn remove_entry<Q: ?Sized>(&mut self, k: &Q) -> Option<(K, V)>
    where
        Q: Hash + Equivalent<K>,
    {
        let hash = make_hash::<Q, S>(&self.hash_builder, k);
        let index = self
            .keys
            .remove_entry(hash, |&i| k.equivalent(&self.entries[i].pair.0))?;
        let entry = self.entries.swap_remove(index);

        if index < self.entries.len() {
            let (prev, next) = self.entries[index].ptrs;

            if let Some(prev) = self.entries.get_mut(prev) {
                prev.ptrs.1 = index;
            }
            if let Some(next) = self.entries.get_mut(next) {
                next.ptrs.0 = index;
            }
        }

        Some(entry.pair)
    }

    #[inline]
    pub fn get<Q: ?Sized>(&mut self, k: &Q) -> Option<&V>
    where
        Q: Hash + Equivalent<K>,
    {
        // Avoid `Option::map` because it bloats LLVM IR.
        #[allow(clippy::manual_map)]
        match self.get_inner(k) {
            Some((_, v)) => Some(v),
            None => None,
        }
    }

    #[inline]
    fn get_inner<Q: ?Sized>(&self, k: &Q) -> Option<&(K, V)>
    where
        Q: Hash + Equivalent<K>,
    {
        if self.entries.is_empty() {
            None
        } else {
            let hash = make_hash::<Q, S>(&self.hash_builder, k);
            let index = self
                .keys
                .get(hash, |&i| k.equivalent(&self.entries[i].pair.0))?;
            let entry = &self.entries[*index];
            Some(&entry.pair)
        }
    }

    #[inline]
    pub fn get_keys<Q: ?Sized>(&self, v: &Q) -> SurMapKeysIter<'_, K, V, S>
    where
        Q: Hash + Equivalent<V>,
    {
        let entry = if self.entries.is_empty() {
            usize::MAX
        } else {
            let hash = make_hash::<Q, S>(&self.hash_builder, v);
            self.values
                .get(hash, |&i| v.equivalent(&self.entries[i].pair.1))
                .copied()
                .unwrap_or(usize::MAX)
        };
        SurMapKeysIter { map: self, entry }
    }
}

pub struct SurMapKeysIter<'a, K, V, S> {
    map: &'a SurMap<K, V, S>,
    entry: usize,
}

impl<'a, K, V, S> Iterator for SurMapKeysIter<'a, K, V, S> {
    type Item = &'a K;

    fn next(&mut self) -> Option<Self::Item> {
        let entry = self.map.entries.get(self.entry)?;
        self.entry = entry.ptrs.1;
        Some(&entry.pair.0)
    }
}

fn make_hash<Q, S>(hash_builder: &S, val: &Q) -> u64
where
    Q: Hash + ?Sized,
    S: BuildHasher,
{
    use core::hash::Hasher;
    let mut state = hash_builder.build_hasher();
    val.hash(&mut state);
    state.finish()
}

struct Entry<K, V> {
    pair: (K, V),
    ptrs: (usize, usize),
}

#[cfg(test)]
mod tests {
    use crate::SurMap;

    #[test]
    fn it_works() {
        let mut map = SurMap::new();
        map.insert("foo", 3);
        map.insert("conrad", 6);
        map.insert("joseph", 6);
        map.insert("bar", 3);
        map.insert("ludgate", 7);
        map.insert("baz", 3);

        assert_eq!(*map.get("foo").unwrap(), 3);
        assert_eq!(*map.get("bar").unwrap(), 3);
        assert_eq!(*map.get("baz").unwrap(), 3);

        assert_eq!(*map.get("conrad").unwrap(), 6);
        assert_eq!(*map.get("joseph").unwrap(), 6);
        assert_eq!(*map.get("ludgate").unwrap(), 7);

        assert_eq!(map.get("missing"), None);

        let keys: Vec<&'static str> = map.get_keys(&3).copied().collect();
        assert_eq!(keys, ["baz", "bar", "foo"]);

        assert_eq!(map.remove(&"bar").unwrap(), 3);
        assert_eq!(map.get("bar"), None);
        let keys: Vec<&'static str> = map.get_keys(&3).copied().collect();
        assert_eq!(keys, ["baz", "foo"]);

        let keys: Vec<&'static str> = map.get_keys(&6).copied().collect();
        assert_eq!(keys, ["joseph", "conrad"]);

        let keys: Vec<&'static str> = map.get_keys(&7).copied().collect();
        assert_eq!(keys, ["ludgate"]);

        let keys: Vec<&'static str> = map.get_keys(&0).copied().collect();
        assert_eq!(keys, ["missing"; 0]);
    }
}
