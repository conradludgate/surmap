use bimap::BiHashMap;
use criterion::{criterion_group, criterion_main, BatchSize, BenchmarkId, Criterion, Throughput};
use std::collections::{hash_map::RandomState, HashMap, HashSet};
use std::hash::{BuildHasher, Hash};
use std::hint::black_box;
use std::rc::Rc;
use surmap::{BiMap, SurMap};

trait Text: AsRef<str> + Clone + Eq + Hash + std::borrow::Borrow<str> {
    fn from_string(value: String) -> Self;
}
impl Text for String {
    fn from_string(value: String) -> Self {
        value
    }
}
impl Text for Rc<str> {
    fn from_string(value: String) -> Self {
        value.into()
    }
}

trait Map<K: Text, V: Text>: Clone {
    type Hasher: BuildHasher + Clone + Default;
    const PREALLOCATE: bool = true;
    fn empty(n: usize, s: Self::Hasher) -> Self;
    fn insert(&mut self, k: K, v: V);
    fn get(&self, k: &str) -> Option<&V>;
    fn reverse(&self, v: &str) -> usize;
    fn remove(&mut self, k: &str);
    fn scan(&self) -> usize;
}

// Each visited pair/key crosses a barrier, including all reverse results.
fn pair<K: Text, V: Text>(k: &K, v: &V) -> usize {
    black_box(k).as_ref().len() + black_box(v).as_ref().len()
}

impl<K: Text, V: Text, S: BuildHasher + Clone + Default> Map<K, V> for BiMap<K, V, S> {
    type Hasher = S;
    fn empty(n: usize, s: S) -> Self {
        Self::with_capacity_and_hasher(n, s)
    }
    fn insert(&mut self, k: K, v: V) {
        black_box(self.insert(k, v));
    }
    fn get(&self, k: &str) -> Option<&V> {
        self.get(k)
    }
    fn reverse(&self, v: &str) -> usize {
        self.get_key(v).map_or(0, |k| {
            black_box(k);
            1
        })
    }
    fn remove(&mut self, k: &str) {
        black_box(self.remove(k));
    }
    fn scan(&self) -> usize {
        self.iter().map(|(k, v)| pair(k, v)).sum()
    }
}
impl<K: Text, V: Text, S: BuildHasher + Clone + Default> Map<K, V> for BiHashMap<K, V, S, S> {
    type Hasher = S;
    fn empty(n: usize, s: S) -> Self {
        Self::with_capacity_and_hashers(n, s.clone(), s)
    }
    fn insert(&mut self, k: K, v: V) {
        black_box(self.insert(k, v));
    }
    fn get(&self, k: &str) -> Option<&V> {
        self.get_by_left(k)
    }
    fn reverse(&self, v: &str) -> usize {
        self.get_by_right(v).map_or(0, |k| {
            black_box(k);
            1
        })
    }
    fn remove(&mut self, k: &str) {
        black_box(self.remove_by_left(k));
    }
    fn scan(&self) -> usize {
        self.iter().map(|(k, v)| pair(k, v)).sum()
    }
}
impl<K: Text, V: Text, S: BuildHasher + Clone + Default> Map<K, V> for SurMap<K, V, S> {
    type Hasher = S;
    fn empty(n: usize, s: S) -> Self {
        Self::with_capacity_and_hasher(n, s)
    }
    fn insert(&mut self, k: K, v: V) {
        black_box(self.insert(k, v));
    }
    fn get(&self, k: &str) -> Option<&V> {
        self.get(k)
    }
    fn reverse(&self, v: &str) -> usize {
        self.get_keys(v)
            .map(|k| {
                black_box(k);
                1
            })
            .sum()
    }
    fn remove(&mut self, k: &str) {
        black_box(self.remove(k));
    }
    fn scan(&self) -> usize {
        self.iter().map(|(k, v)| pair(k, v)).sum()
    }
}

#[derive(Clone)]
struct TwoIndex<K, V, S> {
    forward: HashMap<K, V, S>,
    reverse: HashMap<V, HashSet<K, S>, S>,
}
impl<K: Text, V: Text, S: BuildHasher + Clone + Default> Map<K, V> for TwoIndex<K, V, S> {
    type Hasher = S;
    fn empty(n: usize, s: S) -> Self {
        Self {
            forward: HashMap::with_capacity_and_hasher(n, s.clone()),
            reverse: HashMap::with_capacity_and_hasher(n, s),
        }
    }
    fn insert(&mut self, k: K, v: V) {
        if let Some(old) = self.forward.insert(k.clone(), v.clone()) {
            if old == v {
                return;
            }
            let keys = self.reverse.get_mut(old.as_ref()).unwrap();
            keys.remove(k.as_ref());
            if keys.is_empty() {
                self.reverse.remove(old.as_ref());
            }
        }
        let s = self.forward.hasher().clone();
        self.reverse
            .entry(v)
            .or_insert_with(|| HashSet::with_hasher(s))
            .insert(k);
    }
    fn get(&self, k: &str) -> Option<&V> {
        self.forward.get(k)
    }
    fn reverse(&self, v: &str) -> usize {
        self.reverse.get(v).map_or(0, |keys| {
            keys.iter()
                .map(|k| {
                    black_box(k);
                    1
                })
                .sum()
        })
    }
    fn remove(&mut self, k: &str) {
        if let Some(v) = self.forward.remove(k) {
            let keys = self.reverse.get_mut(v.as_ref()).unwrap();
            keys.remove(k);
            if keys.is_empty() {
                self.reverse.remove(v.as_ref());
            }
        }
    }
    fn scan(&self) -> usize {
        self.forward.iter().map(|(k, v)| pair(k, v)).sum()
    }
}

#[derive(Clone)]
struct Multi<K: Eq + Hash, V: Eq + Hash>(multi_bimap::HashMultiBimap<K, V>);
impl<K: Text, V: Text> Map<K, V> for Multi<K, V> {
    type Hasher = RandomState;
    const PREALLOCATE: bool = false;
    fn empty(_: usize, _: RandomState) -> Self {
        Self(multi_bimap::MultiBimap::new())
    }
    fn insert(&mut self, k: K, v: V) {
        if let Some(old) = self.get(k.as_ref()).cloned() {
            if old == v {
                return;
            }
            black_box(self.0.remove(&k, &old));
        }
        black_box(self.0.insert(k, v));
    }
    fn get(&self, k: &str) -> Option<&V> {
        self.0
            .get_by_left(k)
            .and_then(|values| values.iter().next())
    }
    fn reverse(&self, v: &str) -> usize {
        self.0.get_by_right(v).map_or(0, |keys| {
            keys.iter()
                .map(|k| {
                    black_box(k);
                    1
                })
                .sum()
        })
    }
    fn remove(&mut self, k: &str) {
        // Pair removal needs owned key/value types. Rc makes these clones cheap.
        if let Some((key, values)) = self.0.left_to_right().get_key_value(k) {
            let key = key.clone();
            let value = values.iter().next().unwrap().clone();
            black_box(self.0.remove(&key, &value));
        }
    }
    fn scan(&self) -> usize {
        self.0
            .left_to_right()
            .iter()
            .map(|(k, values)| pair(k, values.iter().next().unwrap()))
            .sum()
    }
}

fn text(kind: char, id: usize, len: usize) -> String {
    let mut s = format!("{kind}/{id:08x}/");
    s.extend(std::iter::repeat_n('x', len - s.len()));
    s
}

fn validate<K: Text, V: Text, M: Map<K, V>>(
    original: &M,
    keys: &[K],
    values: &[V],
    fresh: &[V],
    queries: &[String],
    reverse: &[String],
    order: &[usize],
) {
    let n = keys.len();
    let distinct = values.len();
    let fanout = n / distinct;
    for k in 0..n {
        assert_eq!(
            original.get(&queries[k]).map(AsRef::as_ref),
            Some(values[k % distinct].as_ref())
        );
    }
    for v in reverse {
        assert_eq!(original.reverse(v), fanout);
    }
    assert_eq!(original.scan(), n * keys[0].as_ref().len() * 2);
    let mut updated = original.clone();
    // Check groups after partial updates, when old and new groups coexist.
    let mut moved = vec![0; distinct];
    for &k in order {
        updated.insert(keys[k].clone(), fresh[k % distinct].clone());
        let v = k % distinct;
        moved[v] += 1;
        assert_eq!(updated.reverse(&reverse[v]), fanout - moved[v]);
        assert_eq!(updated.reverse(fresh[v].as_ref()), moved[v]);
    }
    for k in 0..n {
        assert_eq!(
            updated.get(&queries[k]).map(AsRef::as_ref),
            Some(fresh[k % distinct].as_ref())
        );
    }
    for (v, old) in reverse.iter().enumerate() {
        assert_eq!(updated.reverse(old), 0);
        assert_eq!(updated.reverse(fresh[v].as_ref()), fanout);
    }
    for k in queries {
        updated.remove(k);
    }
    for k in queries {
        assert!(updated.get(k).is_none());
    }
    for v in fresh {
        assert_eq!(updated.reverse(v.as_ref()), 0);
    }
}

fn cases<K: Text, V: Text, M: Map<K, V>>(
    c: &mut Criterion,
    family: &str,
    name: &str,
    len: usize,
    fanout: usize,
    seed: &M::Hasher,
) {
    let n = 4096;
    let distinct = n / fanout;
    // One canonical allocation per key/value for Rc; String clones own their bytes.
    let keys: Vec<K> = (0..n).map(|k| K::from_string(text('k', k, len))).collect();
    let values: Vec<V> = (0..distinct)
        .map(|v| V::from_string(text('v', v, len)))
        .collect();
    let fresh: Vec<V> = (distinct..2 * distinct)
        .map(|v| V::from_string(text('v', v, len)))
        .collect();
    // Query buffers are separate from stored strings, including in the Rc cases.
    let queries: Vec<_> = (0..n).map(|k| text('k', k, len)).collect();
    let misses: Vec<_> = (n..2 * n).map(|k| text('k', k, len)).collect();
    let reverse: Vec<_> = (0..distinct).map(|v| text('v', v, len)).collect();
    let order: Vec<_> = (0..n).map(|i| (i * 4051) % n).collect();
    let build = |capacity| {
        let mut map = M::empty(capacity, seed.clone());
        for &k in &order {
            map.insert(keys[k].clone(), values[k % distinct].clone());
        }
        map
    };
    let original = build(n);
    validate(
        &original, &keys, &values, &fresh, &queries, &reverse, &order,
    );

    let mut group = c.benchmark_group(format!("{family}/bytes={len}/n={n}/fanout={fanout}"));
    group.throughput(Throughput::Elements(n as u64));
    for (op, capacity) in [("build_grow", 0), ("build_reserved", n)] {
        if capacity > 0 && !M::PREALLOCATE {
            continue;
        }
        group.bench_function(BenchmarkId::new(op, name), |b| {
            b.iter(|| black_box(build(capacity)));
        });
    }
    for (op, input) in [("get_hit", &queries), ("get_miss", &misses)] {
        group.bench_function(BenchmarkId::new(op, name), |b| {
            b.iter(|| {
                for &k in &order {
                    black_box(black_box(&original).get(black_box(input[k].as_str())));
                }
            });
        });
    }
    group.bench_function(BenchmarkId::new("reverse_all", name), |b| {
        b.iter(|| {
            for i in 0..distinct {
                black_box(
                    black_box(&original)
                        .reverse(black_box(reverse[(i * 4051) % distinct].as_str())),
                );
            }
        });
    });
    group.bench_function(BenchmarkId::new("iterate", name), |b| {
        b.iter(|| black_box(black_box(&original).scan()));
    });
    for op in ["reassign", "remove"] {
        group.bench_function(BenchmarkId::new(op, name), |b| {
            b.iter_batched_ref(
                || original.clone(),
                |map| {
                    for &k in &order {
                        if op == "remove" {
                            map.remove(black_box(queries[k].as_str()));
                        } else {
                            map.insert(
                                black_box(keys[k].clone()),
                                black_box(fresh[k % distinct].clone()),
                            );
                        }
                    }
                    black_box(map);
                },
                BatchSize::LargeInput,
            );
        });
    }
    group.finish();
}

fn hasher_cases<T: Text, S: BuildHasher + Clone + Default>(
    c: &mut Criterion,
    representation: &str,
    hasher: &str,
) {
    let seed = S::default();
    for len in [32, 256] {
        let bimap = format!("{representation}/{hasher}/bimap");
        let surmap = format!("{representation}/{hasher}/surmap");
        cases::<T, T, BiMap<T, T, S>>(c, &bimap, "surmap::BiMap", len, 1, &seed);
        cases::<T, T, BiHashMap<T, T, S, S>>(c, &bimap, "bimap::BiHashMap", len, 1, &seed);
        cases::<T, T, SurMap<T, T, S>>(c, &surmap, "surmap::SurMap", len, 8, &seed);
        cases::<T, T, TwoIndex<T, T, S>>(c, &surmap, "two_index", len, 8, &seed);
    }
}
fn representation<T: Text>(c: &mut Criterion, name: &str) {
    hasher_cases::<T, RandomState>(c, name, "std_random");
    hasher_cases::<T, foldhash::fast::RandomState>(c, name, "foldhash_fast");
    let seed = RandomState::new();
    for len in [32, 256] {
        cases::<T, T, Multi<T, T>>(
            c,
            &format!("{name}/std_random/surmap"),
            "multi_bimap::HashMultiBimap",
            len,
            8,
            &seed,
        );
    }
}
fn shared_values<S: BuildHasher + Clone + Default>(c: &mut Criterion, hasher: &str) {
    let seed = S::default();
    for len in [32, 256] {
        let family = format!("string_rc_str/{hasher}/surmap");
        cases::<String, Rc<str>, SurMap<String, Rc<str>, S>>(
            c,
            &family,
            "surmap::SurMap",
            len,
            8,
            &seed,
        );
        cases::<String, Rc<str>, TwoIndex<String, Rc<str>, S>>(
            c,
            &family,
            "two_index",
            len,
            8,
            &seed,
        );
    }
}
fn benchmarks(c: &mut Criterion) {
    representation::<String>(c, "string");
    representation::<Rc<str>>(c, "rc_str");
    shared_values::<RandomState>(c, "std_random");
    shared_values::<foldhash::fast::RandomState>(c, "foldhash_fast");
    let seed = RandomState::new();
    for len in [32, 256] {
        cases::<String, Rc<str>, Multi<String, Rc<str>>>(
            c,
            "string_rc_str/std_random/surmap",
            "multi_bimap::HashMultiBimap",
            len,
            8,
            &seed,
        );
    }
}
criterion_group!(benches, benchmarks);
criterion_main!(benches);
