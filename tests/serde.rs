#![cfg(feature = "serde")]
use std::collections::hash_map::RandomState;
use surmap::{BiMap, SurMap};

#[test]
fn surmap_round_trip_preserves_groups_after_reassignment() {
    let mut map: SurMap<String, u32, RandomState> = SurMap::default();
    for (key, value) in [("a", 1), ("b", 1), ("c", 2), ("d", 2)] {
        map.insert(key.to_owned(), value);
    }
    map.insert("a".to_owned(), 2);
    map.insert("b".to_owned(), 2);
    map.remove("c");
    let json = serde_json::to_string(&map).unwrap();
    let mut restored: SurMap<String, u32, RandomState> = serde_json::from_str(&json).unwrap();
    assert_eq!(map, restored);
    for value in 1..=2 {
        assert_eq!(
            map.get_keys(&value).collect::<Vec<_>>(),
            restored.get_keys(&value).collect::<Vec<_>>()
        );
    }
    restored.remove("b");
    restored.insert("new".to_owned(), 3);
    assert_eq!(
        restored
            .get_keys(&3)
            .map(String::as_str)
            .collect::<Vec<_>>(),
        ["new"]
    );
}

#[test]
fn serde_empty_maps_and_surmap_duplicate_keys() {
    let map = SurMap::<String, u32>::new();
    assert_eq!(serde_json::to_string(&map).unwrap(), "{}");
    assert!(serde_json::from_str::<SurMap<String, u32>>("{}")
        .unwrap()
        .is_empty());
    assert!(serde_json::from_str::<BiMap<String, u32>>("{}")
        .unwrap()
        .is_empty());
    let map: SurMap<String, u32> = serde_json::from_str(r#"{"a":1,"a":2,"b":2}"#).unwrap();
    assert_eq!(map.len(), 2);
    assert_eq!(map.value_len(), 1);
    assert_eq!(map.get("a"), Some(&2));
    assert_eq!(map.get_keys(&1).next(), None);
    assert!(serde_json::from_str::<SurMap<String, u32>>("[]").is_err());
}

#[test]
fn bijective_round_trip_and_duplicate_rejection() {
    let map = BiMap::from([(String::from("a"), 1), (String::from("b"), 2)]);
    let json = serde_json::to_string(&map).unwrap();
    let restored: BiMap<String, u32> = serde_json::from_str(&json).unwrap();
    assert_eq!(map, restored);
    assert_eq!(restored.get_key(&2).map(String::as_str), Some("b"));
    for json in [r#"{"a":1,"b":1}"#, r#"{"a":1,"a":2}"#, r#"{"a":1,"a":1}"#] {
        let error = serde_json::from_str::<BiMap<String, u32>>(json).unwrap_err();
        assert!(error.to_string().contains("duplicate key or value"));
    }
}

#[test]
fn deserialization_supports_borrowed_keys_and_values() {
    let json = r#"{"alice":"engineering","bob":"design"}"#;
    let map: SurMap<&str, &str> = serde_json::from_str(json).unwrap();
    assert_eq!(map.get("alice"), Some(&"engineering"));
    let map: BiMap<&str, &str> = serde_json::from_str(json).unwrap();
    assert_eq!(map.get_key("design"), Some(&"bob"));
}

#[test]
fn invalid_input_reports_the_expected_map_shape() {
    for input in ["[]", "42", "null", "true"] {
        let error = serde_json::from_str::<SurMap<String, u32>>(input).unwrap_err();
        assert!(error.to_string().contains("a map of keys to values"));
        let error = serde_json::from_str::<BiMap<String, u32>>(input).unwrap_err();
        assert!(error
            .to_string()
            .contains("a map with unique keys and unique values"));
    }
}
