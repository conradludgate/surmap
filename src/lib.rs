#![forbid(unsafe_code)]

use std::hash::{BuildHasher, Hash};

pub use hashbrown::Equivalent;
use hashbrown::{hash_table::Entry as TableEntry, DefaultHashBuilder, HashTable};

/// A Surjective HashMap.
///
/// Key -> Value
/// Value -> [Key]
pub struct SurMap<K, V, S = DefaultHashBuilder> {
    hash_builder: S,
    entries: Vec<Entry<K, V>>,
    // points to the entry that contains this key
    keys: HashTable<usize>,
    // points to the first entry that contains this value
    values: HashTable<usize>,
}

impl<K, V, S: Default> Default for SurMap<K, V, S> {
    fn default() -> Self {
        SurMap {
            hash_builder: S::default(),
            entries: Vec::new(),
            keys: HashTable::new(),
            values: HashTable::new(),
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

        let key_hasher =
            |&key_idx: &usize| make_hash::<K, S>(&self.hash_builder, &self.entries[key_idx].pair.0);
        let result = match self.keys.entry(
            key_hash,
            |&key_idx| self.entries[key_idx].pair.0 == new_entry.pair.0,
            key_hasher,
        ) {
            TableEntry::Occupied(entry) => {
                index = *entry.get();

                let entry = &mut self.entries[index];

                // optimisation
                if new_entry.pair.1 == entry.pair.1 {
                    return Some(std::mem::replace(&mut entry.pair.1, new_entry.pair.1));
                }

                self.unlink_value(index);
                let old_entry = std::mem::replace(&mut self.entries[index], new_entry);
                Some(old_entry.pair.1)
            }
            TableEntry::Vacant(entry) => {
                entry.insert(index);
                self.entries.push(new_entry);
                None
            }
        };

        let value_hasher =
            |&val_idx: &usize| make_hash::<V, S>(&self.hash_builder, &self.entries[val_idx].pair.1);
        match self.values.entry(
            value_hash,
            |&val_idx| self.entries[val_idx].pair.1 == self.entries[index].pair.1,
            value_hasher,
        ) {
            // this value is known. add it to the linked list
            TableEntry::Occupied(entry) => {
                self.entries[index].ptrs.1 = std::mem::replace(entry.into_mut(), index);
                let next = self.entries[index].ptrs.1;
                self.entries[next].ptrs.0 = index;
            }
            TableEntry::Vacant(entry) => {
                entry.insert(index);
            }
        }

        result
    }

    // Detach an entry while its value and all entry indexes are still valid.
    fn unlink_value(&mut self, index: usize) {
        let (prev, next) = self.entries[index].ptrs;
        if prev == usize::MAX {
            let hash = make_hash(&self.hash_builder, &self.entries[index].pair.1);
            if next == usize::MAX {
                self.values
                    .find_entry(hash, |&i| i == index)
                    .unwrap()
                    .remove();
            } else {
                *self.values.find_mut(hash, |&i| i == index).unwrap() = next;
            }
        } else {
            self.entries[prev].ptrs.1 = next;
        }
        if next != usize::MAX {
            self.entries[next].ptrs.0 = prev;
        }
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
            .find_entry(hash, |&i| k.equivalent(&self.entries[i].pair.0))
            .ok()?
            .remove()
            .0;
        self.unlink_value(index);
        let entry = self.entries.swap_remove(index);

        if index < self.entries.len() {
            let old_index = self.entries.len();
            let key_hash = make_hash(&self.hash_builder, &self.entries[index].pair.0);
            *self.keys.find_mut(key_hash, |&i| i == old_index).unwrap() = index;

            let (prev, next) = self.entries[index].ptrs;

            if prev == usize::MAX {
                let value_hash = make_hash(&self.hash_builder, &self.entries[index].pair.1);
                *self
                    .values
                    .find_mut(value_hash, |&i| i == old_index)
                    .unwrap() = index;
            } else {
                self.entries[prev].ptrs.1 = index;
            }
            if let Some(next) = self.entries.get_mut(next) {
                next.ptrs.0 = index;
            }
        }

        Some(entry.pair)
    }

    #[inline]
    pub fn get<Q: ?Sized>(&self, k: &Q) -> Option<&V>
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
                .find(hash, |&i| k.equivalent(&self.entries[i].pair.0))?;
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
                .find(hash, |&i| v.equivalent(&self.entries[i].pair.1))
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
    use std::collections::BTreeMap;
    use std::hash::{BuildHasher, BuildHasherDefault, Hasher};

    #[test]
    fn get_supports_shared_references_and_borrowed_keys() {
        let mut map = SurMap::new();
        map.insert(String::from("alice"), 1);
        map.insert(String::from("bob"), 2);

        let shared = &map;
        let alice = shared.get("alice").unwrap();
        let bob = shared.get("bob").unwrap();
        assert_eq!((*alice, *bob), (1, 2));
        assert_eq!(shared.get("missing"), None);
    }

    #[test]
    fn replacing_keys_updates_value_groups() {
        let mut map = SurMap::new();
        map.insert("a", 1);
        map.insert("b", 1);
        map.insert("c", 1);
        assert_eq!(map.insert("b", 2), Some(1));
        assert_eq!(map.get_keys(&1).copied().collect::<Vec<_>>(), ["c", "a"]);
        assert_eq!(map.insert("c", 2), Some(1));
        assert_eq!(map.get_keys(&1).copied().collect::<Vec<_>>(), ["a"]);
        assert_eq!(map.get_keys(&2).copied().collect::<Vec<_>>(), ["c", "b"]);
        assert_eq!(map.insert("a", 2), Some(1));
        assert_eq!(map.get_keys(&1).next(), None);
        assert_eq!(map.insert("c", 2), Some(2));
        assert_eq!(
            map.get_keys(&2).copied().collect::<Vec<_>>(),
            ["a", "c", "b"]
        );
        assert_eq!(map.remove_entry("c"), Some(("c", 2)));
        assert_eq!(map.get_keys(&2).copied().collect::<Vec<_>>(), ["a", "b"]);
        assert_eq!(map.remove("a"), Some(2));
        assert_eq!(map.remove("b"), Some(2));
        assert_eq!(map.get_keys(&2).next(), None);
        assert_eq!(map.remove("missing"), None);
        assert_eq!(map.insert("d", 2), None);
        assert_eq!(map.get_keys(&2).copied().collect::<Vec<_>>(), ["d"]);
    }

    #[derive(Default)]
    struct ConstantHasher;

    impl Hasher for ConstantHasher {
        fn finish(&self) -> u64 {
            0
        }

        fn write(&mut self, _: &[u8]) {}
    }

    fn check_mixed_operations<S: BuildHasher + Default>() {
        let mut map = SurMap::<u32, u32, S>::default();
        let mut expected = BTreeMap::new();
        let mut groups = vec![Vec::new(); 8];
        let mut state = 42_u64;
        for _ in 0..2000 {
            state = state.wrapping_mul(6364136223846793005).wrapping_add(1);
            let key = ((state >> 32) % 32) as u32;
            let value = ((state >> 40) % 8) as u32;
            if state & 3 == 0 {
                let old = expected.remove(&key);
                assert_eq!(map.remove_entry(&key), old.map(|v| (key, v)));
                if let Some(old) = old {
                    groups[old as usize].retain(|&k| k != key);
                }
            } else {
                let old = expected.insert(key, value);
                assert_eq!(map.insert(key, value), old);
                if old != Some(value) {
                    if let Some(old) = old {
                        groups[old as usize].retain(|&k| k != key);
                    }
                    groups[value as usize].insert(0, key);
                }
            }

            assert_eq!(map.entries.len(), expected.len());
            assert_eq!(map.keys.len(), expected.len());
            assert_eq!(
                map.values.len(),
                groups.iter().filter(|g| !g.is_empty()).count()
            );
            for key in 0..32 {
                assert_eq!(map.get(&key).copied(), expected.get(&key).copied());
            }
            for value in 0..8 {
                // Bound iteration so an accidental linked-list cycle fails promptly.
                let keys: Vec<_> = map.get_keys(&value).take(33).copied().collect();
                assert_eq!(keys, groups[value as usize]);
            }
        }
    }

    #[test]
    fn mixed_operations_match_reference_map() {
        check_mixed_operations::<hashbrown::DefaultHashBuilder>();
    }

    #[test]
    fn mixed_operations_with_hash_collisions_match_reference_map() {
        check_mixed_operations::<BuildHasherDefault<ConstantHasher>>();
    }

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
