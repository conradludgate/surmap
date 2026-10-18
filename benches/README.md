# Benchmarks

Requires Rust 1.92+. All benchmark dependencies are dev-dependencies.

```sh
cargo bench --bench maps                       # Full suite
cargo bench --bench maps -- --test             # Validate all 447 cases
cargo bench --bench maps -- foldhash_fast/     # Filter by hasher
cargo bench --bench maps -- 'n=4096/'          # Filter by size
cargo bench --bench maps -- --save-baseline before
cargo bench --bench maps -- --baseline before
cargo bench --bench strings                    # String and Rc<str> workloads
cargo bench --bench strings -- --test          # Validate all 362 text cases
cargo bench --bench strings -- 'rc_str/'       # Shared string allocations
cargo bench --bench strings -- '^string_rc_str/' # String keys, shared values
```

## Implementations

| Group | Implementation | Storage |
| --- | --- | --- |
| `bimap` | `surmap::BiMap` | Dense entries, two hash indexes |
| `bimap` | `bimap::BiHashMap` | Crate implementation |
| `surmap` | `surmap::SurMap` | Dense entries, linked value groups, two hash indexes |
| `surmap` | `two_index` | Local `HashMap<K, V>` + `HashMap<V, HashSet<K>>` |
| `surmap` | `multi_bimap::HashMultiBimap` | Hash-set-valued hash maps in both directions |

Hasher prefixes are `std_random` (`std::collections::hash_map::RandomState`)
and `foldhash_fast` (`foldhash::fast::RandomState`). Each group shares one seed
across implementations, including the baseline's inner sets. Seeds change
between processes.

`multi_bimap::HashMultiBimap` runs only with `std_random`, using independent seeds and no
preallocated build case: its constructor only uses `Default`, and maplike's
HashMap/HashSet traits do not support custom hasher types. Its adapter removes
the old pair before reassignment to maintain one value per key; key-based
removal first looks up the value. These costs are timed.

## Workloads

Inputs are `usize` pairs with 256, 4,096, or 65,536 keys. SurMap groups contain
1, 8, or 64 keys per value. A fixed permutation determines insertion/query order.
Each iteration processes the whole map:

| Case | Timed work |
| --- | --- |
| `build_grow` / `build_reserved` | Allocate, insert all pairs, destroy map; without/with preallocation |
| `get_hit` / `get_miss` | One lookup per key |
| `reverse_all` | Query every distinct value and consume all returned keys |
| `iterate` | Scan all pairs into a checksum |
| `reassign` | Move every key to a fresh set of values |
| `remove` | Delete every key |

Mutation cases exclude input cloning and map destruction using
`iter_batched_ref`. Read references/results use `black_box`; adapters are
validated before measurement. Throughput counts keys processed, including keys
returned by `reverse_all`.

Results and samples are saved under `target/criterion`; selected measurements
are in [RESULTS.md](RESULTS.md). Keep Cargo.lock and record compiler, CPU, OS,
and command when reproducing a run.

The integer suite excludes memory usage, strings, skewed groups, simultaneous key/value
conflicts, and steady-state churn. Short runs are exploratory; use longer runs
on an idle machine for regression decisions.

## Strings and shared allocations

`strings` compares `String` and `Rc<str>` keys/values of 32 and 256 bytes at
4,096 keys. Bijective maps use unique values; surjective maps use eight keys per
value. Both hashers and the same implementations are covered, with multi_bimap
remaining std-only. Each representation/hasher group shares a seed except for
multi_bimap. Queries use independent `&str` buffers.

| Prefix | Key | Value |
| --- | --- | --- |
| `string` | `String` | `String` |
| `rc_str` | `Rc<str>` | `Rc<str>` |
| `string_rc_str` (surjective maps only) | `String` | `Rc<str>` |

SurMap stores each key once, so only repeated values benefit from allocation
sharing. The two-index baseline and multi_bimap also duplicate keys across
indexes; their both-Rc cases can share those key allocations.

Input strings and Rc allocations are prepared outside timing. Build and
reassignment clone inputs inside timing: String copies bytes, while Rc increments
reference counts. Rc inputs share one canonical allocation per key/distinct
value, retained by the input pool throughout measurement. Container-internal
clones and drops are timed; pool allocation and final deallocation are excluded.
The multi_bimap adapter also clones the old value for reassignment and the stored
key/value for pair removal. Mutation setup clones and final map destruction are
excluded using `BatchSize::LargeInput` to limit temporary memory usage.

Text scans black-box each pair and sum byte lengths; reverse traversal black-boxes
each key and counts results. Their scan times are not directly comparable to the
integer suite's checksum. These cases measure a caller that already owns a string
pool; they do not measure interning costs or memory usage.
