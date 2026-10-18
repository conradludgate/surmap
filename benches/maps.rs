use bimap::BiHashMap;
use criterion::{criterion_group, criterion_main, BatchSize, BenchmarkId, Criterion, Throughput};
use std::collections::{hash_map::RandomState, HashMap, HashSet};
use std::hash::BuildHasher;
use std::hint::black_box;
use surmap::{BiMap, SurMap};

// Shared seeds except multi_bimap, whose constructor only uses Default.
#[expect(
    clippy::trivially_copy_pass_by_ref,
    reason = "Adapters preserve the maps' borrowed lookup APIs"
)]
trait Map: Clone {
    type Hasher: BuildHasher + Clone + Default;
    const PREALLOCATE: bool = true;
    fn empty(capacity: usize, hasher: Self::Hasher) -> Self;
    fn insert(&mut self, key: usize, value: usize);
    fn get(&self, key: &usize) -> Option<&usize>;
    fn reverse(&self, value: &usize) -> usize;
    fn remove(&mut self, key: &usize);
    fn scan(&self) -> usize;
}

#[derive(Clone)]
struct MultiBimap(multi_bimap::HashMultiBimap<usize, usize>);

impl Map for MultiBimap {
    type Hasher = RandomState;
    const PREALLOCATE: bool = false;
    fn empty(_: usize, _: RandomState) -> Self {
        // The crate only exposes Default-based construction.
        Self(multi_bimap::MultiBimap::new())
    }
    fn insert(&mut self, k: usize, v: usize) {
        if let Some(old) = self.get(&k).copied() {
            if old == v {
                return;
            }
            // Explicit pair removal preserves the other keys in the old group.
            black_box(self.0.remove(&k, &old));
        }
        black_box(self.0.insert(k, v));
    }
    fn get(&self, k: &usize) -> Option<&usize> {
        self.0
            .get_by_left(k)
            .and_then(|values| values.iter().next())
    }
    fn reverse(&self, v: &usize) -> usize {
        self.0
            .get_by_right(v)
            .map_or(0, |keys| keys.iter().fold(0, |sum, k| sum.wrapping_add(*k)))
    }
    fn remove(&mut self, k: &usize) {
        if let Some(v) = self.get(k).copied() {
            black_box(self.0.remove(k, &v));
        }
    }
    fn scan(&self) -> usize {
        self.0.left_to_right().iter().fold(0, |sum, (k, v)| {
            sum.wrapping_add(k ^ v.iter().next().unwrap())
        })
    }
}

impl<S: BuildHasher + Clone + Default> Map for BiMap<usize, usize, S> {
    type Hasher = S;
    fn empty(n: usize, s: S) -> Self {
        Self::with_capacity_and_hasher(n, s)
    }
    fn insert(&mut self, k: usize, v: usize) {
        black_box(self.insert(k, v));
    }
    fn get(&self, k: &usize) -> Option<&usize> {
        self.get(k)
    }
    fn reverse(&self, v: &usize) -> usize {
        self.get_key(v).copied().unwrap_or(0)
    }
    fn remove(&mut self, k: &usize) {
        black_box(self.remove(k));
    }
    fn scan(&self) -> usize {
        self.iter().fold(0, |sum, (k, v)| sum.wrapping_add(k ^ v))
    }
}
impl<S: BuildHasher + Clone + Default> Map for BiHashMap<usize, usize, S, S> {
    type Hasher = S;
    fn empty(n: usize, s: S) -> Self {
        Self::with_capacity_and_hashers(n, s.clone(), s)
    }
    fn insert(&mut self, k: usize, v: usize) {
        black_box(self.insert(k, v));
    }
    fn get(&self, k: &usize) -> Option<&usize> {
        self.get_by_left(k)
    }
    fn reverse(&self, v: &usize) -> usize {
        self.get_by_right(v).copied().unwrap_or(0)
    }
    fn remove(&mut self, k: &usize) {
        black_box(self.remove_by_left(k));
    }
    fn scan(&self) -> usize {
        self.iter().fold(0, |sum, (k, v)| sum.wrapping_add(k ^ v))
    }
}
impl<S: BuildHasher + Clone + Default> Map for SurMap<usize, usize, S> {
    type Hasher = S;
    fn empty(n: usize, s: S) -> Self {
        Self::with_capacity_and_hasher(n, s)
    }
    fn insert(&mut self, k: usize, v: usize) {
        black_box(self.insert(k, v));
    }
    fn get(&self, k: &usize) -> Option<&usize> {
        self.get(k)
    }
    fn reverse(&self, v: &usize) -> usize {
        self.get_keys(v).fold(0, |sum, k| sum.wrapping_add(*k))
    }
    fn remove(&mut self, k: &usize) {
        black_box(self.remove(k));
    }
    fn scan(&self) -> usize {
        self.iter().fold(0, |sum, (k, v)| sum.wrapping_add(k ^ v))
    }
}

// Many-to-one baseline: maintains both directions and removes empty groups.
#[derive(Clone)]
struct TwoIndex<S> {
    forward: HashMap<usize, usize, S>,
    reverse: HashMap<usize, HashSet<usize, S>, S>,
}
impl<S: BuildHasher + Clone + Default> Map for TwoIndex<S> {
    type Hasher = S;
    fn empty(n: usize, s: S) -> Self {
        Self {
            forward: HashMap::with_capacity_and_hasher(n, s.clone()),
            reverse: HashMap::with_capacity_and_hasher(n, s),
        }
    }
    fn insert(&mut self, k: usize, v: usize) {
        if let Some(old) = self.forward.insert(k, v) {
            if old == v {
                return;
            }
            let keys = self.reverse.get_mut(&old).unwrap();
            keys.remove(&k);
            if keys.is_empty() {
                self.reverse.remove(&old);
            }
        }
        let hasher = self.forward.hasher().clone();
        self.reverse
            .entry(v)
            .or_insert_with(|| HashSet::with_hasher(hasher))
            .insert(k);
    }
    fn get(&self, k: &usize) -> Option<&usize> {
        self.forward.get(k)
    }
    fn reverse(&self, v: &usize) -> usize {
        self.reverse
            .get(v)
            .map_or(0, |keys| keys.iter().fold(0, |sum, k| sum.wrapping_add(*k)))
    }
    fn remove(&mut self, k: &usize) {
        if let Some(v) = self.forward.remove(k) {
            let keys = self.reverse.get_mut(&v).unwrap();
            keys.remove(k);
            if keys.is_empty() {
                self.reverse.remove(&v);
            }
        }
    }
    fn scan(&self) -> usize {
        self.forward
            .iter()
            .fold(0, |sum, (k, v)| sum.wrapping_add(k ^ v))
    }
}

fn cases<M: Map>(
    c: &mut Criterion,
    family: &str,
    name: &str,
    n: usize,
    fanout: usize,
    seed: &M::Hasher,
) {
    let values = n / fanout;
    // A permutation of 0..n: reproducible nonsequential access, no RNG in timings.
    let keys: Vec<_> = (0..n).map(|i| (i * 4051) % n).collect();
    let build = |capacity| {
        let mut map = M::empty(capacity, seed.clone());
        for &k in &keys {
            map.insert(k, k % values);
        }
        map
    };
    let original = build(n);
    // Validate adapters before measuring them.
    for k in 0..n {
        assert_eq!(original.get(&k), Some(&(k % values)));
    }
    for v in 0..values {
        assert_eq!(original.reverse(&v), (v..n).step_by(values).sum::<usize>());
    }
    let mut updated = original.clone();
    for &k in &keys {
        updated.insert(k, k % values + values);
    }
    for k in 0..n {
        assert_eq!(updated.get(&k), Some(&(k % values + values)));
    }
    for v in 0..values {
        assert_eq!(updated.reverse(&v), 0);
        assert_eq!(
            updated.reverse(&(v + values)),
            (v..n).step_by(values).sum::<usize>()
        );
    }
    for &k in &keys {
        updated.remove(&k);
    }
    for k in 0..n {
        assert_eq!(updated.get(&k), None);
    }
    for v in values..2 * values {
        assert_eq!(updated.reverse(&v), 0);
    }

    let mut group = c.benchmark_group(format!("{family}/n={n}/fanout={fanout}"));
    group.throughput(Throughput::Elements(n as u64));
    for (operation, capacity) in [("build_grow", 0), ("build_reserved", n)] {
        if capacity != 0 && !M::PREALLOCATE {
            continue;
        }
        group.bench_function(BenchmarkId::new(operation, name), |b| {
            b.iter(|| black_box(build(capacity)));
        });
    }
    group.bench_function(BenchmarkId::new("get_hit", name), |b| {
        b.iter(|| {
            for k in &keys {
                black_box(black_box(&original).get(black_box(k)));
            }
        });
    });
    group.bench_function(BenchmarkId::new("get_miss", name), |b| {
        b.iter(|| {
            for k in &keys {
                black_box(black_box(&original).get(&black_box(k + n)));
            }
        });
    });
    group.bench_function(BenchmarkId::new("iterate", name), |b| {
        b.iter(|| black_box(black_box(&original).scan()));
    });
    for operation in ["reassign", "remove"] {
        group.bench_function(BenchmarkId::new(operation, name), |b| {
            b.iter_batched_ref(
                || original.clone(),
                |map| {
                    for &k in &keys {
                        if operation == "remove" {
                            map.remove(black_box(&k));
                        } else {
                            map.insert(black_box(k), black_box(k % values + values));
                        }
                    }
                    black_box(map);
                },
                BatchSize::SmallInput,
            );
        });
    }
    // Consume every reverse result once: n keys across n/fanout queries.
    group.bench_function(BenchmarkId::new("reverse_all", name), |b| {
        b.iter(|| {
            for i in 0..values {
                black_box(black_box(&original).reverse(&black_box((i * 4051) % values)));
            }
        });
    });
    group.finish();
}

fn hasher_cases<S: BuildHasher + Clone + Default>(c: &mut Criterion, hasher: &str) {
    let seed = S::default();
    let bimap = format!("{hasher}/bimap");
    let surmap = format!("{hasher}/surmap");
    for n in [256, 4096, 65536] {
        cases::<BiMap<_, _, S>>(c, &bimap, "surmap::BiMap", n, 1, &seed);
        cases::<BiHashMap<_, _, S, S>>(c, &bimap, "bimap::BiHashMap", n, 1, &seed);
        for fanout in [1, 8, 64] {
            cases::<SurMap<_, _, S>>(c, &surmap, "surmap::SurMap", n, fanout, &seed);
            cases::<TwoIndex<S>>(c, &surmap, "two_index", n, fanout, &seed);
        }
    }
}
fn benchmarks(c: &mut Criterion) {
    hasher_cases::<RandomState>(c, "std_random");
    hasher_cases::<foldhash::fast::RandomState>(c, "foldhash_fast");
    let seed = RandomState::new();
    for n in [256, 4096, 65536] {
        for fanout in [1, 8, 64] {
            cases::<MultiBimap>(
                c,
                "std_random/surmap",
                "multi_bimap::HashMultiBimap",
                n,
                fanout,
                &seed,
            );
        }
    }
}
criterion_group!(benches, benchmarks);
criterion_main!(benches);
