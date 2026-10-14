# surmap

A Rust map for looking up a value by key and finding every key associated with a
value. Each key has one value, and multiple keys can have equal values.

Use `SurMap` when you need both directions of a many-to-one relationship, such as
user IDs grouped by team or aliases grouped by destination.

## Example

```rust
use surmap::SurMap;

let mut teams = SurMap::new();
assert_eq!(teams.insert("alice", "engineering"), None);
teams.insert("bob", "engineering");
teams.insert("carol", "design");

assert_eq!(teams.get("alice"), Some(&"engineering"));

let engineers: Vec<_> = teams.get_keys("engineering").copied().collect();
assert_eq!(engineers, ["bob", "alice"]);

// Reassigning a key updates both directions and returns its previous value.
assert_eq!(teams.insert("alice", "design"), Some("engineering"));
assert_eq!(teams.get_keys("engineering").copied().collect::<Vec<_>>(), ["bob"]);
assert_eq!(teams.get_keys("design").copied().collect::<Vec<_>>(), ["alice", "carol"]);

assert_eq!(teams.remove("bob"), Some("engineering"));
assert_eq!(teams.get("bob"), None);
assert_eq!(teams.get_keys("engineering").next(), None);
```

## API

| Method | Behavior |
| --- | --- |
| `SurMap::new()` / `with_capacity(n)` | Creates a map with the default hasher, optionally preallocating storage. |
| `with_hasher(s)` / `with_capacity_and_hasher(n, s)` | Creates a map with a supplied hash builder. |
| `hasher()` | Returns the hash builder. |
| `len()` / `is_empty()` | Reports the number of mappings or whether there are none. |
| `value_len()` | Reports the number of distinct values. |
| `capacity()` / `value_capacity()` | Reports mapping and distinct-value storage capacities. |
| `reserve(n)` / `try_reserve(n)` | Reserves space for n additional mappings and distinct values. |
| `shrink_to(n)` / `shrink_to_fit()` | Reduces allocated storage. |
| `insert(key, value)` | Adds or replaces a mapping; returns the previous value, if any. |
| `get(&key)` / `get_key_value(&key)` | Returns the value or the stored key and value, if present. |
| `contains_key(&key)` / `contains_value(&value)` | Tests membership in either direction. |
| `get_keys(&value)` | Iterates over references to all keys with an equal value. |
| `remove(&key)` | Removes a mapping and returns its value, if present. |
| `remove_entry(&key)` | Removes a mapping and returns its owned `(key, value)` pair. |
| `iter()` / `keys()` / `values()` | Iterates over mappings, keys, or values; equal values occur once per mapping. |
| `distinct_values()` | Iterates over one representative of each distinct value. |
| `into_iter()` / `into_keys()` / `into_values()` | Consumes the map and yields owned items. |
| `retain(predicate)` | Keeps mappings for which `predicate(&key, &value)` returns true. |
| `clear()` / `drain()` | Removes all mappings, retaining storage; `drain` yields the removed pairs. |

`capacity()` covers the entry vector and key index. Distinct values have a
separate allocation reported by `value_capacity()`. `reserve(n)` reserves room
for n additional entries in all three allocations. `try_reserve` leaves mappings
unchanged on failure, though some allocations may already have grown.

Maps support `collect`, `extend`, array conversion, cloning, and comparison by
mappings. General iteration follows storage order, which can change after a
removal. Reverse iteration through `get_keys` follows the value group's links.

## Custom hashers

```rust
use std::collections::hash_map::RandomState;
use surmap::SurMap;

let mut map = SurMap::with_hasher(RandomState::new());
map.insert("alice", "engineering");
assert_eq!(map.get("alice"), Some(&"engineering"));
```

## Bijective maps

`BiMap` enforces a one-to-one relationship. It supports the shared capacity,
iteration, and utility APIs, with `get_key(&value)` for reverse lookup and
`remove_value` / `remove_value_entry` for removal by value.

`insert` replaces mappings that conflict with either the supplied key or value.
It returns an `InsertResult` containing the displaced pairs in `by_key` and
`by_value`. A mapping matching both appears only in `by_key`. `try_insert`
rejects either conflict, returning the supplied pair without changing the map.

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

`BiMap::capacity()` reports the minimum capacity of its entry vector and both
indexes.

`BiMap::try_from(surmap)` succeeds if its values are unique; otherwise it returns
the original `SurMap` unchanged. Conversions in either direction reuse the hash
indexes and hash builder, moving the mappings into a new entry vector.

## Serde

Enable the optional `serde` Cargo feature to serialize and deserialize either
map type. The serialized representation is a map of keys to values; indexes,
links, capacities, and the hash builder are reconstructed rather than serialized.
Deserialization uses the chosen hash builder's default value.

For `SurMap`, duplicate keys in serialized input use the last value. For `BiMap`,
duplicate keys or values are errors. Serialization emits each value group from
oldest to newest so deserialization restores its reverse iteration order when
the format preserves map entry order. Formats such as JSON may restrict the key
types they can represent.

## Implementation design

Both maps use an internal `BidiTable<E, S>` for dense entry storage and two hash
indexes. Its entry trait provides access to a key/value pair, so lookup,
reservation, shrinking, draining, index repair after removal, and layout
conversion share one implementation. Each map manages its own grouping or
conflict rules.

`SurMap` uses linked entries in the table's vector. Two
`hashbrown::HashTable<usize>` indexes refer to positions in that vector: one maps
each key to its entry, and the other maps each distinct value to the first entry
in its group. Hashing and equality checks use the keys and values stored in the
vector.

Entries with equal values form a doubly linked list. Each entry stores the vector
indexes of its previous and next entries, using `usize::MAX` for a missing link.
`get_keys` finds the group's head through the value index, then follows the next
links. The previous links let removal detach an entry without walking the group.

Insertion adds an entry at the head of its value's group. Reassigning an existing
key to a different value detaches it from its old group before linking it into
the new one. If the old group becomes empty, its value index entry is removed.

Removal detaches the entry from its group and uses `swap_remove` to fill its
vector slot with the last entry. If an entry moves, its key index, its neighbors'
links, and its value index when it is a group head are updated to its new position.
This keeps the vector dense without shifting all subsequent entries.

`BiMap` uses plain `(key, value)` pairs in the same generic table.
Both indexes point directly to entries, since keys and values are unique. Entries
need no linked-list indexes, saving two `usize` fields per mapping (typically 16
bytes on a 64-bit platform, subject to alignment and padding).

Insertion removes any mapping with a conflicting key or value before adding the
new pair. Removal uses `swap_remove` and updates both indexes for the moved pair;
there are no group links to repair.

## Performance

| Operation | Expected cost | Worst-case cost |
| --- | --- | --- |
| `get` | O(1) | O(n) |
| `insert` | Amortized O(1) | O(n²) |
| `remove` / `remove_entry` | O(1) | O(n + d) |
| `get_keys` (constructing the iterator) | O(1) | O(d) |
| `get_keys` iterator's `next()` | O(1) | O(1) |
| `reserve` / `try_reserve` / shrinking (when rebuilding storage) | O(n + d) | O(n² + d²) |
| `clear` / constructing `drain` | O(n + d) | O(n + d) |
| `retain` | O(m) | O(m(n + d)) |

Here, n is the key index's capacity, d is the value index's capacity, and m is
the number of mappings. For capacity changes, use the larger capacity before or
after the operation. Capacity can remain larger than the number of entries after
removals. These bounds assume constant-time hashing, equality checks, and dropping
keys and values.

Expected costs assume well-distributed hashes. Collisions can make a lookup scan
an entire index. An insertion that grows or rebuilds an index usually takes O(n)
time, but can take O(n²) when many entries collide during reinsertion. Vector
growth also takes O(n) time; these occasional costs are amortized across inserts.

`Iterator::next()` follows one stored link without hashing or searching an index,
so its constant-time bound holds even when hashes collide. General iteration
through `iter`, `keys`, and `values` also constructs an iterator and advances it
in O(1) time. `distinct_values` scans the value index, so constructing its iterator
is O(1), while a single `next()` call can take O(d) in the worst case.

`BiMap` has the same bounds for the shared operations. Its reverse lookup has
expected O(1) cost and worst-case O(d) cost; removal by value has expected O(1)
cost and worst-case O(n + d) cost. A `retain`
predicate is assumed to take constant time.
