# Benchmark results

2026-10-18 · AMD Ryzen 9 7950X · NixOS 26.05 · x86_64
rustc 1.99.1 (58cf8f9c3, LLVM 23.1.1) · optimized bench profile
Criterion 0.8.2 · hashbrown 0.17.1 · bimap 0.6.3 · multi_bimap 0.8.0 · maplike 0.15.0 · foldhash 0.2.0

**µs per batch of 4,096 keys.** Ten samples, 100 ms warmup, 200 ms measurement.
`std` = standard RandomState; `foldhash` = foldhash::fast::RandomState;
`—` = unsupported. [Methodology](README.md).

```sh
cargo bench --bench maps -- '/(bimap/n=4096/|surmap/n=4096/fanout=8/)' --warm-up-time 0.1 --measurement-time 0.2 --sample-size 10
cargo bench --bench strings -- 'std_random/surmap/bytes=256/' --warm-up-time 0.1 --measurement-time 0.2 --sample-size 10
```

## usize keys and values: one-to-one

| Operation | surmap::BiMap std | surmap::BiMap foldhash | bimap::BiHashMap std | bimap::BiHashMap foldhash |
| --- | ---: | ---: | ---: | ---: |
| Build with growth | 329.37 | 153.28 | 494.32 | 288.71 |
| Build preallocated | 119.55 | 63.03 | 332.93 | 206.99 |
| Forward lookup hits | 39.77 | 8.50 | 40.75 | 8.10 |
| Forward lookup misses | 38.38 | 6.81 | 37.22 | 7.02 |
| Reverse lookup | 39.85 | 10.34 | 42.42 | 9.59 |
| Iterate | 0.59 | 0.59 | 2.86 | 3.13 |
| Reassign | 342.51 | 147.96 | 378.83 | 223.23 |
| Remove | 213.31 | 90.00 | 203.08 | 139.49 |

## usize keys and values: eight keys per value

| Operation | surmap::SurMap std | surmap::SurMap foldhash | Two-index std | Two-index foldhash | multi_bimap::HashMultiBimap std |
| --- | ---: | ---: | ---: | ---: | ---: |
| Build with growth | 234.45 | 103.52 | 336.36 | 163.89 | 651.60 |
| Build preallocated | 123.78 | 57.19 | 264.42 | 128.04 | — |
| Forward lookup hits | 39.30 | 9.15 | 39.05 | 7.04 | 46.53 |
| Forward lookup misses | 38.27 | 7.37 | 38.08 | 6.07 | 38.08 |
| Reverse lookup, all keys | 9.28 | 5.07 | 9.60 | 5.57 | 8.90 |
| Iterate | 0.87 | 0.87 | 2.47 | 2.47 | 6.78 |
| Reassign | 183.46 | 68.95 | 406.14 | 186.84 | 998.37 |
| Remove | 213.36 | 88.13 | 212.85 | 98.05 | 571.35 |

## Strings

256 bytes per key/value, eight keys per value, standard RandomState.
Representations measured separately with independent seeds.

### String keys, String values

| Operation | surmap::SurMap | Two-index | multi_bimap::HashMultiBimap |
| --- | ---: | ---: | ---: |
| Build with growth | 1094.30 | 1728.50 | 2656.00 |
| Build preallocated | 641.95 | 1333.60 | — |
| Forward lookup hits | 218.75 | 259.33 | 260.22 |
| Forward lookup misses | 190.89 | 193.28 | 187.68 |
| Reverse lookup, all keys | 33.93 | 32.55 | 31.21 |
| Iterate | 1.84 | 3.66 | 9.99 |
| Reassign | 765.88 | 1882.20 | 4222.70 |
| Remove | 907.57 | 1050.40 | 2644.80 |

### Shared strings

| Operation | `surmap::SurMap<String, Rc<str>>` | Two-index `Rc<str>` keys/values | `multi_bimap::HashMultiBimap<Rc<str>, Rc<str>>` |
| --- | ---: | ---: | ---: |
| Build with growth | 980.39 | 1278.10 | 2134.40 |
| Build preallocated | 534.34 | 924.92 | — |
| Forward lookup hits | 210.77 | 251.83 | 258.90 |
| Forward lookup misses | 196.42 | 193.10 | 186.97 |
| Reverse lookup, all keys | 34.48 | 32.24 | 31.09 |
| Iterate | 1.82 | 3.00 | 9.25 |
| Reassign | 712.03 | 1441.50 | 3562.30 |
| Remove | 877.40 | 745.58 | 2023.70 |
