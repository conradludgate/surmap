mod common;

use common::{Collisions, SeededHasher};
use surmap::{BiMap, SurMap, TryReserveError};

macro_rules! shared_contracts {
    ($test:ident, $map:ident) => {
        #[test]
        fn $test() {
            let mut map = $map::new();
            assert!(map.is_empty());
            assert!(!map.contains_key(&1));
            assert!(!map.contains_value(&10));
            map.reserve(0);
            map.try_reserve(0).unwrap();
            map.try_reserve(10).unwrap();
            assert!(map.capacity() >= 10);
            assert!(map.is_empty());
            map.insert(1, 10);
            assert!(!map.is_empty());
            assert!(map.contains_key(&1));
            assert!(map.contains_value(&10));
            assert!(!map.contains_key(&2));
            assert!(!map.contains_value(&20));
            assert_eq!(map.remove(&1), Some(10));
            assert!(map.is_empty());
            assert!(!map.contains_key(&1));
            assert!(!map.contains_value(&10));

            let a = $map::from([(1, 10), (2, 20)]);
            let reordered: $map<_, _, Collisions> = [(2, 20), (1, 10)].into_iter().collect();
            assert_eq!(a, reordered);
            // Same length does not imply equality; neither does a shared subset.
            for other in [
                $map::from([(1, 10), (2, 30)]),
                $map::from([(1, 10), (3, 20)]),
                $map::from([(1, 10)]),
                $map::from([(1, 10), (2, 20), (3, 30)]),
            ] {
                assert_ne!(a, other);
                assert_ne!(other, a);
            }
            let debug = format!("{a:?}");
            assert!(debug.starts_with('{') && debug.ends_with('}'));
            assert!(debug.contains("1: 10"));
            assert!(debug.contains("2: 20"));

            let mut map = $map::with_hasher(SeededHasher(7));
            map.extend([(1, 10), (2, 20)]);
            map.reserve(100);
            assert_eq!(map.hasher().0, 7);
            assert!(map.capacity() >= map.len() + 100);
            let capacity = map.capacity();
            for k in 3..103 {
                map.insert(k, k + 1000);
            }
            assert_eq!(map.capacity(), capacity);
            for k in 3..103 {
                assert_eq!(map.get(&k), Some(&(k + 1000)));
            }
        }
    };
}
shared_contracts!(surmap_membership_equality_and_reservation, SurMap);
shared_contracts!(bimap_membership_equality_and_reservation, BiMap);

#[test]
fn distinct_value_capacity_tracks_reservation_and_shrinking() {
    let mut map = SurMap::with_capacity(16);
    assert!(map.value_capacity() >= 16);
    for k in 0..12 {
        map.insert(k, k % 3);
    }
    assert_eq!(map.value_len(), 3);
    map.reserve(100);
    assert!(map.value_capacity() >= map.value_len() + 100);
    let capacity = map.value_capacity();
    for k in 12..112 {
        map.insert(k, k + 1000);
    }
    assert_eq!(map.value_capacity(), capacity);
    map.clear();
    assert_eq!(map.value_capacity(), capacity);
    map.shrink_to_fit();
    assert_eq!(map.value_capacity(), 0);
}

#[test]
fn reservation_errors_describe_the_failed_allocation() {
    let mut entries = Vec::<u8>::new();
    let allocation = entries.try_reserve(usize::MAX).unwrap_err();
    let expected = allocation.to_string();
    let error = TryReserveError::Entries(allocation);
    assert_eq!(error.to_string(), expected);
    let mut index = hashbrown::HashTable::<usize>::new();
    let allocation = index.try_reserve(usize::MAX, |_| 0).unwrap_err();
    let expected = format!("hash index reservation failed: {allocation:?}");
    let error = TryReserveError::Index(allocation);
    assert_eq!(error.to_string(), expected);
}

#[test]
fn insertion_and_removal_accept_non_clone_keys_and_values() {
    #[derive(Debug, Eq, Hash, PartialEq)]
    struct Owned(u32);
    let mut sur = SurMap::new();
    sur.insert(Owned(1), Owned(10));
    sur.insert(Owned(2), Owned(10));
    assert_eq!(sur.get_keys(&Owned(10)).count(), 2);
    assert_eq!(sur.remove_entry(&Owned(1)), Some((Owned(1), Owned(10))));
    let mut bi = BiMap::try_from(sur).unwrap();
    assert_eq!(bi.get_key(&Owned(10)), Some(&Owned(2)));
    assert_eq!(
        bi.insert(Owned(2), Owned(20)).by_key,
        Some((Owned(2), Owned(10)))
    );
    assert_eq!(
        bi.remove_value_entry(&Owned(20)),
        Some((Owned(2), Owned(20)))
    );
}

#[test]
fn surmap_replacement_preserves_the_key_only_for_equal_values() {
    use std::rc::Rc;
    let old_key: Rc<str> = Rc::from("key");
    let new_key: Rc<str> = Rc::from("key");
    let old_value: Rc<str> = Rc::from("value");
    let new_value: Rc<str> = Rc::from("value");
    let mut map = SurMap::new();
    map.insert(Rc::clone(&old_key), Rc::clone(&old_value));
    let displaced = map
        .insert(Rc::clone(&new_key), Rc::clone(&new_value))
        .unwrap();
    assert!(Rc::ptr_eq(&displaced, &old_value));
    let (key, value) = map.get_key_value("key").unwrap();
    assert!(Rc::ptr_eq(key, &old_key));
    assert!(Rc::ptr_eq(value, &new_value));

    let changed_value: Rc<str> = Rc::from("changed");
    map.insert(Rc::clone(&new_key), Rc::clone(&changed_value));
    let (key, value) = map.get_key_value("key").unwrap();
    assert!(Rc::ptr_eq(key, &new_key));
    assert!(Rc::ptr_eq(value, &changed_value));
}

#[test]
fn bimap_replacement_stores_both_supplied_objects_even_when_equal() {
    use std::rc::Rc;
    let old_key: Rc<str> = Rc::from("key");
    let new_key: Rc<str> = Rc::from("key");
    let old_value: Rc<str> = Rc::from("value");
    let new_value: Rc<str> = Rc::from("value");
    let mut map = BiMap::new();
    map.insert(Rc::clone(&old_key), Rc::clone(&old_value));
    let displaced = map.insert(Rc::clone(&new_key), Rc::clone(&new_value));
    let (key, value) = displaced.by_key.unwrap();
    assert!(Rc::ptr_eq(&key, &old_key));
    assert!(Rc::ptr_eq(&value, &old_value));
    assert!(displaced.by_value.is_none());
    let (key, value) = map.get_key_value("key").unwrap();
    assert!(Rc::ptr_eq(key, &new_key));
    assert!(Rc::ptr_eq(value, &new_value));
}

macro_rules! consuming_iterator_drops {
    ($test:ident, $map:ident) => {
        #[test]
        fn $test() {
            use std::rc::Rc;
            let first: Rc<str> = Rc::from("first");
            let second: Rc<str> = Rc::from("second");
            let map = $map::from([(1, Rc::clone(&first)), (2, Rc::clone(&second))]);
            let mut keys = map.into_keys();
            assert_eq!(
                (Rc::strong_count(&first), Rc::strong_count(&second)),
                (2, 2)
            );
            assert_eq!(keys.next(), Some(1));
            assert_eq!(
                (Rc::strong_count(&first), Rc::strong_count(&second)),
                (1, 2)
            );
            drop(keys);
            assert_eq!(Rc::strong_count(&second), 1);

            let map = $map::from([(Rc::clone(&first), 1), (Rc::clone(&second), 2)]);
            let mut values = map.into_values();
            assert_eq!(
                (Rc::strong_count(&first), Rc::strong_count(&second)),
                (2, 2)
            );
            assert_eq!(values.next_back(), Some(2));
            assert_eq!(
                (Rc::strong_count(&first), Rc::strong_count(&second)),
                (2, 1)
            );
            drop(values);
            assert_eq!(Rc::strong_count(&first), 1);
        }
    };
}
consuming_iterator_drops!(
    surmap_consuming_iterators_drop_unused_components_lazily,
    SurMap
);
consuming_iterator_drops!(
    bimap_consuming_iterators_drop_unused_components_lazily,
    BiMap
);
