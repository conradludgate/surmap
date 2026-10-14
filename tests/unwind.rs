use std::cell::Cell;
use std::hash::{BuildHasher, Hash, Hasher};
use std::panic::{catch_unwind, AssertUnwindSafe};
use std::rc::Rc;
use surmap::{BiMap, SurMap};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Callback {
    Hash,
    Eq,
    Build,
    Write,
    Finish,
}

#[derive(Default, Debug)]
struct Gate {
    armed: Cell<Option<(Callback, usize)>>,
    calls: Cell<usize>,
}
impl Gate {
    fn hit(&self, kind: Callback) {
        if let Some((expected, at)) = self.armed.get() {
            if expected == kind {
                let calls = self.calls.get() + 1;
                self.calls.set(calls);
                assert_ne!(calls, at, "injected {kind:?} panic");
            }
        }
    }
    fn arm(&self, kind: Callback, at: usize) {
        self.calls.set(0);
        self.armed.set(Some((kind, at)));
    }
    fn disarm(&self) {
        self.armed.set(None);
    }
}

#[derive(Clone, Debug)]
struct Bomb {
    id: u32,
    gate: Rc<Gate>,
}
impl PartialEq for Bomb {
    fn eq(&self, other: &Self) -> bool {
        self.gate.hit(Callback::Eq);
        self.id == other.id
    }
}
impl Eq for Bomb {}
impl Hash for Bomb {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.gate.hit(Callback::Hash);
        state.write_u32(self.id);
    }
}
impl std::borrow::Borrow<u32> for Bomb {
    fn borrow(&self) -> &u32 {
        &self.id
    }
}

#[derive(Clone)]
struct Builder(Rc<Gate>);
struct CollisionHasher(Rc<Gate>);
impl BuildHasher for Builder {
    type Hasher = CollisionHasher;
    fn build_hasher(&self) -> Self::Hasher {
        self.0.hit(Callback::Build);
        CollisionHasher(self.0.clone())
    }
}
impl Hasher for CollisionHasher {
    fn write(&mut self, _: &[u8]) {
        self.0.hit(Callback::Write);
    }
    fn finish(&self) -> u64 {
        self.0.hit(Callback::Finish);
        0
    }
}
fn bomb(id: u32, gate: &Rc<Gate>) -> Bomb {
    Bomb {
        id,
        gate: gate.clone(),
    }
}
fn pairs(map: &SurMap<Bomb, Bomb, Builder>) -> Vec<(u32, u32)> {
    map.iter().map(|(k, v)| (k.id, v.id)).collect()
}
fn bi_pairs(map: &BiMap<Bomb, Bomb, Builder>) -> Vec<(u32, u32)> {
    map.iter().map(|(k, v)| (k.id, v.id)).collect()
}

#[test]
fn surmap_insert_panics_leave_mappings_and_group_order_unchanged() {
    // Empty insertion, new/existing groups, replacing group head/middle/tail,
    // sole value, equal value, growth, and heavily deleted index storage.
    let scenarios = [
        (0, 0, 0, false),
        (3, 4, 0, false),
        (3, 4, 9, false),
        (7, 0, 9, false),
        (7, 3, 2, false),
        (7, 6, 1, false),
        (7, 1, 1, false),
        (3, 1, 9, false),
        (40, 100, 0, true),
        (40, 100, 99, true),
    ];
    for (count, key, value, deleted) in scenarios {
        for kind in [
            Callback::Hash,
            Callback::Eq,
            Callback::Build,
            Callback::Write,
            Callback::Finish,
        ] {
            let mut reached_success = false;
            for at in 1..=256 {
                let gate = Rc::new(Gate::default());
                let mut map = SurMap::with_hasher(Builder(gate.clone()));
                for id in 0..count {
                    map.insert(bomb(id, &gate), bomb(id % 3, &gate));
                }
                if deleted {
                    for id in (0..count).step_by(2) {
                        map.remove(&id);
                    }
                }
                let before = pairs(&map);
                let groups: Vec<Vec<_>> = (0..3)
                    .map(|v| map.get_keys(&v).map(|k| k.id).collect())
                    .collect();
                let distinct = map.value_len();
                gate.arm(kind, at);
                let outcome = catch_unwind(AssertUnwindSafe(|| {
                    map.insert(bomb(key, &gate), bomb(value, &gate))
                }));
                gate.disarm();
                if outcome.is_err() {
                    assert_eq!(
                        pairs(&map),
                        before,
                        "scenario count={count}, key={key}, value={value}, deleted={deleted}, {kind:?} #{at}"
                    );
                    assert_eq!(map.value_len(), distinct);
                    for v in 0..3 {
                        assert_eq!(
                            map.get_keys(&v)
                                .take(map.len() + 1)
                                .map(|k| k.id)
                                .collect::<Vec<_>>(),
                            groups[v as usize]
                        );
                    }
                } else {
                    reached_success = true;
                }
                for (k, v) in map.iter() {
                    assert_eq!(map.get(&k.id).map(|v| v.id), Some(v.id));
                    assert!(map
                        .get_keys(&v.id)
                        .take(map.len() + 1)
                        .any(|key| key.id == k.id));
                }
                map.insert(bomb(200, &gate), bomb(200, &gate));
                assert_eq!(map.remove(&200).map(|v| v.id), Some(200));
                if reached_success {
                    break;
                }
            }
            assert!(reached_success, "all callback positions must be exercised");
        }
    }
}

#[test]
fn bimap_insert_and_try_insert_panics_leave_both_indexes_and_mappings_unchanged() {
    let scenarios = [
        (0, 0, 100, false),
        (3, 9, 109, false),
        (7, 0, 100, false),
        (7, 0, 106, false),
        (7, 6, 100, false),
        (7, 5, 106, false),
        (7, 0, 109, false),
        (7, 9, 100, false),
        (40, 100, 200, true),
    ];
    for (count, key, value, deleted) in scenarios {
        for replace in [false, true] {
            for kind in [
                Callback::Hash,
                Callback::Eq,
                Callback::Build,
                Callback::Write,
                Callback::Finish,
            ] {
                let mut reached_success = false;
                for at in 1..=256 {
                    let gate = Rc::new(Gate::default());
                    let mut map = BiMap::with_hasher(Builder(gate.clone()));
                    for id in 0..count {
                        map.insert(bomb(id, &gate), bomb(id + 100, &gate));
                    }
                    if deleted {
                        for id in (0..count).step_by(2) {
                            map.remove(&id);
                        }
                    }
                    let before = bi_pairs(&map);
                    gate.arm(kind, at);
                    let outcome = catch_unwind(AssertUnwindSafe(|| {
                        if replace {
                            map.insert(bomb(key, &gate), bomb(value, &gate));
                        } else {
                            let _ = map.try_insert(bomb(key, &gate), bomb(value, &gate));
                        }
                    }));
                    gate.disarm();
                    if outcome.is_err() {
                        assert_eq!(bi_pairs(&map), before, "scenario count={count}, key={key}, value={value}, deleted={deleted}, replace={replace}, {kind:?} #{at}");
                    } else {
                        reached_success = true;
                    }
                    for (k, v) in &map {
                        assert_eq!(map.get(&k.id).map(|v| v.id), Some(v.id));
                        assert_eq!(map.get_key(&v.id).map(|k| k.id), Some(k.id));
                    }
                    if outcome.is_err() {
                        for (k, v) in &before {
                            assert_eq!(map.get(k).map(|v| v.id), Some(*v));
                            assert_eq!(map.get_key(v).map(|k| k.id), Some(*k));
                        }
                    }
                    map.insert(bomb(300, &gate), bomb(400, &gate));
                    assert_eq!(map.remove_value(&400).map(|k| k.id), Some(300));
                    if reached_success {
                        break;
                    }
                }
                assert!(reached_success, "all callback positions must be exercised");
            }
        }
    }
}
