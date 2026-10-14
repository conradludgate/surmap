mod common;

use common::{Collisions, SeededHasher};
use std::collections::BTreeMap;
use std::hash::BuildHasher;
use std::panic::{catch_unwind, AssertUnwindSafe};
use surmap::SurMap;

#[test]
fn capacity_reservation_shrinking_and_custom_hasher() {
    let mut map = SurMap::with_capacity_and_hasher(64, SeededHasher(7));
    assert_eq!(map.hasher().0, 7);
    assert!(map.capacity() >= 64);
    for key in 0..40 {
        map.insert(key, key % 4);
    }
    assert_eq!((map.len(), map.value_len()), (40, 4));
    map.shrink_to_fit();
    assert!(map.capacity() >= map.len());
    let capacity = map.capacity();
    map.shrink_to(capacity + 100);
    assert_eq!(map.capacity(), capacity);
    map.reserve(30);
    assert!(map.capacity() >= map.len() + 30);
    let capacity = map.capacity();
    let value_capacity = map.value_capacity();
    for key in 40..70 {
        map.insert(key, key);
    }
    assert_eq!(map.capacity(), capacity);
    assert_eq!(map.value_capacity(), value_capacity);
    map.try_reserve(10).unwrap();
    assert!(map.capacity() >= map.len() + 10);
    assert!(map.try_reserve(usize::MAX).is_err());
    assert_eq!(map.len(), 70);
    for key in 0..70 {
        assert_eq!(map.get(&key), Some(&if key < 40 { key % 4 } else { key }));
    }
    map.clear();
    assert!(map.is_empty());
    assert_eq!(map.value_len(), 0);
    assert!(map.capacity() >= 80);
    map.shrink_to_fit();
    assert_eq!(map.capacity(), 0);
    map.insert(1, 1);
    assert_eq!(map.get(&1), Some(&1));

    let mut map = SurMap::with_hasher(SeededHasher(9));
    map.insert("key", "value");
    assert_eq!(map.hasher().0, 9);
    assert_eq!(map.get("key"), Some(&"value"));
    let map = SurMap::<u32, u32>::with_capacity(12);
    assert!(map.capacity() >= 12);
}

#[test]
fn collection_iteration_clone_and_equality() {
    let map = SurMap::from([(1, 10), (2, 10), (3, 30)]);
    assert_eq!(map.len(), 3);
    let mut iter = map.iter();
    assert_eq!(iter.len(), 3);
    assert_eq!(iter.next(), Some((&1, &10)));
    assert_eq!(iter.next_back(), Some((&3, &30)));
    assert_eq!(iter.clone().collect::<Vec<_>>(), vec![(&2, &10)]);
    assert_eq!(iter.next(), Some((&2, &10)));
    assert_eq!(iter.next(), None);
    assert_eq!(iter.next_back(), None);
    assert_eq!(map.keys().copied().collect::<Vec<_>>(), [1, 2, 3]);
    assert_eq!(map.values().copied().collect::<Vec<_>>(), [10, 10, 30]);
    assert_eq!((&map).into_iter().count(), 3);
    assert_eq!(map.clone(), map);
    assert_eq!(map.clone().into_keys().collect::<Vec<_>>(), [1, 2, 3]);
    assert_eq!(map.clone().into_values().collect::<Vec<_>>(), [10, 10, 30]);
    let mut owned = map.clone().into_iter();
    assert_eq!(owned.len(), 3);
    assert_eq!(owned.next_back(), Some((3, 30)));
    assert_eq!(owned.collect::<Vec<_>>(), [(1, 10), (2, 10)]);
    let mut other: SurMap<_, _, Collisions> = [(3, 30), (2, 10), (1, 10)].into_iter().collect();
    assert_eq!(map, other);
    other.extend([(4, 40), (1, 11)]);
    assert_ne!(map, other);
    assert_eq!(other.get_key_value(&1), Some((&1, &11)));
    assert!(other.contains_key(&4));
    assert!(other.contains_value(&11));
    assert!(!other.contains_value(&99));
    assert!(!format!("{other:?}").is_empty());
}

#[test]
fn retain_and_drain_preserve_indexes_even_when_interrupted() {
    let mut map: SurMap<_, _, Collisions> = (0..30).map(|k| (k, k % 3)).collect();
    map.retain(|k, _| k % 2 == 0);
    assert_eq!(map.len(), 15);
    for value in 0..3 {
        let mut actual = map.get_keys(&value).copied().collect::<Vec<_>>();
        actual.sort();
        assert_eq!(
            actual,
            (0..30)
                .filter(|k| k % 2 == 0 && k % 3 == value)
                .collect::<Vec<_>>()
        );
    }
    let mut calls = 0;
    let result = catch_unwind(AssertUnwindSafe(|| {
        map.retain(|_, _| {
            calls += 1;
            if calls == 4 {
                panic!("predicate failed");
            }
            false
        })
    }));
    assert!(result.is_err());
    assert_eq!(map.len(), 12);
    for (key, value) in &map {
        assert_eq!(map.get(key), Some(value));
        assert!(map.get_keys(value).any(|k| k == key));
    }
    let capacity = map.capacity();
    {
        let mut drain = map.drain();
        assert_eq!(drain.len(), 12);
        assert!(drain.next().is_some());
        assert!(drain.next_back().is_some());
    }
    assert!(map.is_empty());
    assert_eq!(map.value_len(), 0);
    assert_eq!(map.capacity(), capacity);
    map.insert(100, 9);
    assert_eq!(map.get_keys(&9).copied().collect::<Vec<_>>(), [100]);
    std::mem::forget(map.drain());
    assert!(map.is_empty());
    assert!(!map.contains_value(&9));
    map.insert(200, 9);
    assert_eq!(map.get(&200), Some(&9));
}

#[test]
fn surmap_capacity_operations_preserve_group_order_with_collisions() {
    let mut map: SurMap<_, _, Collisions> = (0..100).map(|k| (k, k % 7)).collect();
    map.insert(0, 6);
    map.remove(&80);
    let groups: Vec<Vec<_>> = (0..7)
        .map(|v| map.get_keys(&v).copied().collect())
        .collect();
    map.reserve(1000);
    map.try_reserve(1000).unwrap();
    map.shrink_to(300);
    assert!(map.capacity() >= 300);
    map.shrink_to_fit();
    assert!(map.capacity() >= map.len());
    for value in 0..7 {
        assert_eq!(
            map.get_keys(&value).copied().collect::<Vec<_>>(),
            groups[value as usize]
        );
    }
    let mut values = map.distinct_values().copied().collect::<Vec<_>>();
    values.sort();
    assert_eq!(values, (0..7).collect::<Vec<_>>());
    let mut iter = map.get_keys(&6);
    assert_eq!(iter.clone().copied().collect::<Vec<_>>(), groups[6]);
    while iter.next().is_some() {}
    assert_eq!(iter.next(), None);
    assert_eq!(iter.next(), None);
}

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

        assert_eq!(map.len(), expected.len());
        assert_eq!(map.keys().count(), expected.len());
        assert_eq!(
            map.value_len(),
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
    check_mixed_operations::<Collisions>();
}

#[test]
fn removal_preserves_reverse_lookup_groups() {
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
