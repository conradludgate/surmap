use std::hash::{BuildHasher, BuildHasherDefault, DefaultHasher, Hasher};

pub(crate) struct SeededHasher(pub(crate) u64);
impl BuildHasher for SeededHasher {
    type Hasher = DefaultHasher;
    fn build_hasher(&self) -> Self::Hasher {
        let mut hasher = DefaultHasher::new();
        hasher.write_u64(self.0);
        hasher
    }
}

#[derive(Default)]
pub(crate) struct CollisionHasher;
impl Hasher for CollisionHasher {
    fn finish(&self) -> u64 {
        0
    }
    fn write(&mut self, _: &[u8]) {}
}

pub(crate) type Collisions = BuildHasherDefault<CollisionHasher>;
