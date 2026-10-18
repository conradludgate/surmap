# Testing

Tests and benchmarks require Rust 1.92+. Check the library's Rust 1.85 minimum with
`cargo +1.85.0 check --lib --all-features`.

```sh
cargo test
cargo test --all-features
cargo fmt --all -- --check
cargo clippy --all-targets --all-features -- -D warnings -W clippy::pedantic
RUSTDOCFLAGS='-D warnings' cargo doc --all-features --no-deps
```

The integration suite covers reference-model mutation sequences, collisions,
capacity contracts, membership/equality, ownership without Clone, serialization,
and panic safety. Capacity and insertion panic tests inject failures at each
hash-callback position and verify mappings, reverse indexes, and continued use.

## Coverage

```sh
cargo install cargo-llvm-cov --locked
rustup component add llvm-tools-preview
cargo llvm-cov --all-features --lib --tests --ignore-filename-regex 'tests/' --html
```

Report: `target/llvm-cov/html/index.html`. This measures library source exercised
by tests; benchmarks and documentation tests are excluded. Line coverage does
not establish assertion strength or branch coverage.

## Mutation testing

```sh
cargo install cargo-mutants --locked
cargo mutants --all-features --jobs 4 --timeout 10 --build-timeout 120 --output target/mutations
```

Results: `target/mutations/mutants.out/`. Review `missed.txt` and the corresponding
diffs for assertion gaps; distinguish behavior changes from equivalent or
performance-only mutations. `unviable.txt` lists mutations that do not compile.
Timeouts can indicate infinite loops introduced by a mutation; inspect their logs.
