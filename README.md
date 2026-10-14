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
| `SurMap::new()` | Creates an empty map with the default hasher. |
| `insert(key, value)` | Adds or replaces a mapping; returns the previous value, if any. |
| `get(&key)` | Returns a reference to the key's value, if present. |
| `get_keys(&value)` | Iterates over references to all keys with an equal value. |
| `remove(&key)` | Removes a mapping and returns its value, if present. |
| `remove_entry(&key)` | Removes a mapping and returns its owned `(key, value)` pair. |

## Implementation design

`SurMap` stores each `(key, value)` pair in a dense vector. Two
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

## Performance

| Operation | Expected cost | Worst-case cost |
| --- | --- | --- |
| `get` | O(1) | O(n) |
| `insert` | Amortized O(1) | O(n²) |
| `remove` / `remove_entry` | O(1) | O(n + d) |
| `get_keys` (constructing the iterator) | O(1) | O(d) |
| `Iterator::next()` | O(1) | O(1) |

Here, n is the key index's capacity and d is the value index's capacity. Capacity
can remain larger than the number of entries after removals. These bounds assume
constant-time hashing, equality checks, and dropping keys and values.

Expected costs assume well-distributed hashes. Collisions can make a lookup scan
an entire index. An insertion that grows or rebuilds an index usually takes O(n)
time, but can take O(n²) when many entries collide during reinsertion. Vector
growth also takes O(n) time; these occasional costs are amortized across inserts.

`Iterator::next()` follows one stored link without hashing or searching an index,
so its constant-time bound holds even when hashes collide.
