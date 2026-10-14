mod common;

use common::{Collisions, SeededHasher};
use std::collections::BTreeMap;
use std::hash::BuildHasher;
use surmap::{BiMap, SurMap};

#[test]
fn bijective_conflicts_and_borrowed_queries() {
    let mut map = BiMap::new();
    let result = map.insert(String::from("alice"), String::from("one"));
    assert_eq!(result.by_key, None);
    assert_eq!(result.by_value, None);
    map.insert(String::from("bob"), String::from("two"));
    assert_eq!(map.get("alice").map(String::as_str), Some("one"));
    assert_eq!(map.get_key("two").map(String::as_str), Some("bob"));
    assert!(map
        .try_insert(String::from("alice"), String::from("three"))
        .is_err());
    assert!(map
        .try_insert(String::from("carol"), String::from("two"))
        .is_err());
    assert_eq!(map.len(), 2);
    let result = map.insert(String::from("alice"), String::from("two"));
    assert_eq!(
        result.by_key,
        Some((String::from("alice"), String::from("one")))
    );
    assert_eq!(
        result.by_value,
        Some((String::from("bob"), String::from("two")))
    );
    assert_eq!(map.len(), 1);
    assert!(!map.contains_key("bob"));
    assert!(!map.contains_value("one"));
    let result = map.insert(String::from("alice"), String::from("two"));
    assert!(result.by_key.is_some());
    assert_eq!(result.by_value, None);
    assert_eq!(
        map.remove_value_entry("two"),
        Some((String::from("alice"), String::from("two")))
    );
    assert!(map.is_empty());
}

fn check_bijection<S: BuildHasher + Default>() {
    let mut map = BiMap::<u32, u32, S>::default();
    let mut expected = BTreeMap::new();
    let mut state = 123_u64;
    for step in 0..2000 {
        state = state.wrapping_mul(6364136223846793005).wrapping_add(1);
        let key = ((state >> 32) % 32) as u32;
        let value = ((state >> 40) % 32) as u32;
        match state & 3 {
            0 => {
                assert_eq!(map.remove(&key), expected.remove(&key));
            }
            1 => {
                let old = expected.iter().find(|(_, v)| **v == value).map(|(&k, _)| k);
                if let Some(k) = old {
                    expected.remove(&k);
                }
                assert_eq!(map.remove_value(&value), old);
            }
            _ => {
                let by_key = expected.remove(&key).map(|v| (key, v));
                let old_key = expected.iter().find(|(_, v)| **v == value).map(|(&k, _)| k);
                let by_value = old_key.map(|k| (k, expected.remove(&k).unwrap()));
                expected.insert(key, value);
                let result = map.insert(key, value);
                assert_eq!(result.by_key, by_key);
                assert_eq!(result.by_value, by_value);
            }
        }
        if step % 100 == 0 {
            map.reserve(40);
            map.shrink_to_fit();
        }
        assert_eq!(map.len(), expected.len());
        for key in 0..32 {
            assert_eq!(map.get(&key), expected.get(&key));
        }
        for value in 0..32 {
            let key = expected.iter().find(|(_, v)| **v == value).map(|(k, _)| k);
            assert_eq!(map.get_key(&value), key);
        }
    }
}

#[test]
fn bijective_mixed_operations_and_collisions() {
    check_bijection::<hashbrown::DefaultHashBuilder>();
    check_bijection::<Collisions>();
}

#[test]
fn bijective_utilities_use_the_same_capacity_and_collection_contracts() {
    let mut map = BiMap::with_capacity_and_hasher(20, SeededHasher(12));
    assert_eq!(map.hasher().0, 12);
    assert!(map.capacity() >= 20);
    map.try_insert(1, 10).unwrap();
    map.try_reserve(10).unwrap();
    assert!(map.try_reserve(usize::MAX).is_err());
    assert_eq!(map.get_key_value(&1), Some((&1, &10)));
    map.extend([(2, 20), (3, 30)]);
    assert_eq!(map.keys().copied().collect::<Vec<_>>(), [1, 2, 3]);
    assert_eq!(map.values().copied().collect::<Vec<_>>(), [10, 20, 30]);
    assert_eq!((&map).into_iter().count(), 3);
    map.retain(|k, _| *k != 2);
    assert!(!map.contains_value(&20));
    assert_eq!(map.remove_entry(&1), Some((1, 10)));
    assert_eq!(map.drain().collect::<Vec<_>>(), [(3, 30)]);
    map.clear();
    map.shrink_to(5);
    let map = BiMap::from([(1, 10), (2, 20)]);
    assert_eq!(map, map.clone());
    assert_eq!(map.clone().into_keys().collect::<Vec<_>>(), [1, 2]);
    assert_eq!(map.into_values().collect::<Vec<_>>(), [10, 20]);
    assert!(BiMap::<i32, i32>::with_capacity(10).capacity() >= 10);
}

#[test]
fn bijective_conversion_checks_uniqueness_without_losing_the_original() {
    let map = SurMap::from([(1, 10), (2, 10)]);
    let original = BiMap::try_from(map.clone()).unwrap_err();
    assert_eq!(original, map);
    let map = SurMap::from([(1, 10), (2, 20)]);
    let bijective = BiMap::try_from(map.clone()).unwrap();
    assert_eq!(bijective.get_key(&20), Some(&2));
    let restored = SurMap::from(bijective);
    assert_eq!(restored, map);
    let empty = BiMap::try_from(SurMap::<u32, u32>::new()).unwrap();
    assert!(empty.is_empty());
}

#[test]
fn compact_storage_iteration_and_capacity() {
    let mut map = BiMap::with_capacity(32);
    for key in 0..20 {
        map.insert(key, key + 100);
    }
    let capacity = map.capacity();
    let mut iter = map.iter();
    assert_eq!(iter.len(), 20);
    assert_eq!(iter.next(), Some((&0, &100)));
    assert_eq!(iter.next_back(), Some((&19, &119)));
    assert_eq!(iter.clone().count(), 18);
    assert_eq!(iter.count(), 18);
    let mut owned = map.clone().into_iter();
    assert_eq!(owned.len(), 20);
    assert_eq!(owned.next(), Some((0, 100)));
    assert_eq!(owned.next_back(), Some((19, 119)));
    assert_eq!(owned.count(), 18);
    {
        let mut drain = map.drain();
        assert_eq!(drain.len(), 20);
        assert_eq!(drain.next(), Some((0, 100)));
        assert_eq!(drain.next_back(), Some((19, 119)));
    }
    assert!(map.is_empty());
    assert_eq!(map.capacity(), capacity);
    assert_eq!(map.get(&19), None);
    assert_eq!(map.get_key(&119), None);
    map.insert(20, 120);
    std::mem::forget(map.drain());
    assert!(map.is_empty());
    assert!(!map.contains_key(&20));
    assert!(!map.contains_value(&120));
    map.insert(30, 130);
    assert_eq!(map.get_key(&130), Some(&30));
    map.clear();
    map.shrink_to_fit();
    assert_eq!(map.capacity(), 0);
}

#[test]
fn conversion_preserves_custom_hasher_and_both_indexes_after_moves() {
    let mut map = SurMap::with_hasher(SeededHasher(42));
    for key in 0..40 {
        map.insert(key, key + 100);
    }
    map.remove(&5);
    map.remove(&20);
    let mut map = BiMap::try_from(map).unwrap();
    assert_eq!(map.hasher().0, 42);
    assert_eq!(map.remove_value(&139), Some(39));
    assert_eq!(map.remove(&0), Some(100));
    map.insert(1, 102);
    for (key, value) in &map {
        assert_eq!(map.get(key), Some(value));
        assert_eq!(map.get_key(value), Some(key));
    }
    let mut restored = SurMap::from(map);
    assert_eq!(restored.hasher().0, 42);
    for (key, value) in &restored {
        assert_eq!(
            restored.get_keys(value).copied().collect::<Vec<_>>(),
            [*key]
        );
    }
    restored.insert(50, 102);
    assert_eq!(
        restored.get_keys(&102).copied().collect::<Vec<_>>(),
        [50, 1]
    );
    assert_eq!(restored.remove(&1), Some(102));
    assert_eq!(restored.get_keys(&102).copied().collect::<Vec<_>>(), [50]);
}

#[test]
fn retain_panic_leaves_both_bijective_indexes_consistent() {
    use std::panic::{catch_unwind, AssertUnwindSafe};
    let mut map: BiMap<_, _, Collisions> = (0..30).map(|k| (k, k + 100)).collect();
    let mut calls = 0;
    let result = catch_unwind(AssertUnwindSafe(|| {
        map.retain(|_, _| {
            calls += 1;
            if calls == 5 {
                panic!("predicate failed");
            }
            false
        })
    }));
    assert!(result.is_err());
    assert_eq!(map.len(), 26);
    for key in 0..30 {
        assert_eq!(map.get(&key).is_some(), map.get_key(&(key + 100)).is_some());
    }
    for (key, value) in &map {
        assert_eq!(map.get(key), Some(value));
        assert_eq!(map.get_key(value), Some(key));
    }
    map.insert(1000, 2000);
    assert_eq!(map.remove_value(&2000), Some(1000));
}
