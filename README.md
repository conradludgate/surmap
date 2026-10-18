# surmap

Bidirectional hash maps for many-to-one and one-to-one relationships:

- `SurMap<K, V>` maps each key to one value and each value to all associated keys.
- `BiMap<K, V>` requires unique keys and values, with lookup in either direction.

Both store each key/value pair once, with dense iteration and no `Clone`
requirement for insertion or removal.

## `SurMap`

```rust
use surmap::SurMap;

let mut teams = SurMap::new();
teams.insert("alice", "engineering");
teams.insert("bob", "engineering");
teams.insert("carol", "design");

assert_eq!(teams.get("alice"), Some(&"engineering"));
assert_eq!(
    teams.get_keys("engineering").copied().collect::<Vec<_>>(),
    ["bob", "alice"],
);

// Reassignment updates both directions and returns the previous value.
assert_eq!(teams.insert("alice", "design"), Some("engineering"));
assert_eq!(teams.get_keys("engineering").copied().collect::<Vec<_>>(), ["bob"]);
assert_eq!(teams.remove("bob"), Some("engineering"));
assert!(!teams.contains_value("engineering"));
```

Equal values form a group; `get_keys` visits its most recently linked key first.
Each mapping owns its value. Use `SurMap<String, Rc<str>>` to share allocations
for repeated string values while keeping owned, unique keys.

## `BiMap`

`insert` replaces mappings that conflict with either the key or value. Its
`InsertResult` returns displaced pairs in `by_key` and `by_value`; a pair matching
both appears only in `by_key`. `try_insert` rejects conflicts without changing
mappings and returns the supplied pair.

```rust
use surmap::BiMap;

let mut map = BiMap::new();
map.insert("alice", 1);
map.insert("bob", 2);

let replaced = map.insert("alice", 2);
assert_eq!(replaced.by_key, Some(("alice", 1)));
assert_eq!(replaced.by_value, Some(("bob", 2)));
assert_eq!(map.get_key(&2), Some(&"alice"));
assert_eq!(map.len(), 1);
assert_eq!(map.try_insert("carol", 2), Err(("carol", 2)));
```

`remove_value` and `remove_value_entry` remove by value. `BiMap::try_from(surmap)`
succeeds when values are unique, otherwise returning the original `SurMap`.
Conversion in either direction reuses the indexes and hasher and moves pairs
into a new entry vector.

## Shared API

| Methods | Purpose |
| --- | --- |
| `new`, `with_capacity`, `with_hasher`, `with_capacity_and_hasher` | Construction |
| `get`, `get_key_value`, `contains_key`, `contains_value` | Lookup |
| `insert`, `remove`, `remove_entry`, `retain` | Mutation |
| `iter`, `keys`, `values` | Borrowed iteration |
| `into_iter`, `into_keys`, `into_values` | Owned iteration |
| `len`, `is_empty`, `capacity`, `hasher` | Metadata |
| `reserve`, `try_reserve`, `shrink_to`, `shrink_to_fit` | Storage management |
| `clear`, `drain` | Remove all mappings while retaining storage |

`SurMap` additionally provides `get_keys`, `distinct_values`, `value_len`, and
`value_capacity`. `values` yields one value per mapping, including equal values.
Both maps support `collect`, `extend`, array conversion, cloning, and equality
by mappings. General iteration follows storage order, which may change on removal.

`SurMap::capacity` covers the entry vector and key index; `value_capacity` covers
the distinct-value index. `BiMap::capacity` is the minimum across its entry vector
and both indexes. `reserve(n)` reserves n additional entries in all three
allocations. `try_reserve` preserves mappings on failure, though capacity may grow.

Custom hashers use the standard `BuildHasher` interface:

```rust
use std::collections::hash_map::RandomState;
use surmap::SurMap;

let mut map = SurMap::with_hasher(RandomState::new());
map.insert("alice", "engineering");
assert_eq!(map.get("alice"), Some(&"engineering"));
```

## Serde

Enable the `serde` feature to serialize either type as a key-to-value map.
Deserialization rebuilds indexes using the hash builder's default value.
Duplicate input keys use the last value for `SurMap`; duplicate keys or values
are errors for `BiMap`. Value-group order survives round trips when the format
preserves map entry order. Formats such as JSON may restrict key types.

## Storage and performance

Both maps use a dense vector and two `hashbrown::HashTable<usize>` indexes.
`SurMap` stores two links per entry to connect equal values; `BiMap` stores plain
pairs. Removal uses `swap_remove` and repairs indexes and links for the moved
entry. Keys and values are stored in the vector, rather than duplicated in indexes.

Insertion and rehashing prepare hashes before changing mappings. A panic in
hashing or equality leaves mappings and value-group order unchanged; capacity
may increase during preparation. Rehashing uses temporary hash buffers.

| Operation | Expected cost | Worst-case cost |
| --- | --- | --- |
| Lookup by key | O(1) | O(n) |
| `BiMap::get_key` | O(1) | O(d) |
| Insert | Amortized O(1) | O(n²) |
| Remove | O(1) | O(n + d) |
| Construct `get_keys` | O(1) | O(d) |
| Advance `get_keys` | O(1) | O(1) |
| Reserve or shrink when rebuilding | O(n + d) | O(n² + d²) |
| Clear or construct `drain` | O(n + d) | O(n + d) |
| Retain | O(m) | O(m(n + d)) |

Here n and d are key/value index capacities and m is the number of mappings.
Bounds assume constant-time hashing, equality, dropping, and retain predicates;
expected costs assume well-distributed hashes. General iteration advances in
O(1); `distinct_values` scans the value index and may take O(d) for one step.

## Benchmarks

Compare against `bimap::BiHashMap`, `multi_bimap::HashMultiBimap`, and a two-index
`HashMap`/`HashSet` baseline with standard `RandomState` and foldhash where supported:

```sh
cargo bench --bench maps       # usize keys and values
cargo bench --bench strings    # String and Rc<str> variants
```

Benchmarks require Rust 1.92+. See the
[benchmark guide](https://github.com/conradludgate/surmap/blob/main/benches/README.md)
and [results](https://github.com/conradludgate/surmap/blob/main/benches/RESULTS.md)
for workloads, commands, and measurements.
