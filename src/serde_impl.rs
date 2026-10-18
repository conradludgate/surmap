use crate::{BiMap, SurMap};
use serde_core::de::{Error, MapAccess, Visitor};
use serde_core::ser::SerializeMap;
use serde_core::{Deserialize, Deserializer, Serialize, Serializer};
use std::fmt;
use std::hash::{BuildHasher, Hash};
use std::marker::PhantomData;

impl<K: Serialize, V: Serialize, S> Serialize for SurMap<K, V, S> {
    fn serialize<T: Serializer>(&self, serializer: T) -> Result<T::Ok, T::Error> {
        let mut map = serializer.serialize_map(Some(self.len()))?;
        self.serialize_entries(|key, value| map.serialize_entry(key, value))?;
        map.end()
    }
}

impl<'de, K, V, S> Deserialize<'de> for SurMap<K, V, S>
where
    K: Deserialize<'de> + Hash + Eq,
    V: Deserialize<'de> + Hash + Eq,
    S: BuildHasher + Default,
{
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        struct MapVisitor<K, V, S>(PhantomData<(K, V, S)>);
        impl<'de, K, V, S> Visitor<'de> for MapVisitor<K, V, S>
        where
            K: Deserialize<'de> + Hash + Eq,
            V: Deserialize<'de> + Hash + Eq,
            S: BuildHasher + Default,
        {
            type Value = SurMap<K, V, S>;
            fn expecting(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                f.write_str("a map of keys to values")
            }
            fn visit_map<A: MapAccess<'de>>(self, mut access: A) -> Result<Self::Value, A::Error> {
                let mut map = SurMap::with_capacity_and_hasher(
                    access.size_hint().unwrap_or(0).min(4096),
                    S::default(),
                );
                while let Some((key, value)) = access.next_entry()? {
                    map.insert(key, value);
                }
                Ok(map)
            }
        }
        deserializer.deserialize_map(MapVisitor(PhantomData))
    }
}

impl<K: Serialize, V: Serialize, S> Serialize for BiMap<K, V, S> {
    fn serialize<T: Serializer>(&self, serializer: T) -> Result<T::Ok, T::Error> {
        let mut map = serializer.serialize_map(Some(self.len()))?;
        for (key, value) in self {
            map.serialize_entry(key, value)?;
        }
        map.end()
    }
}
impl<'de, K, V, S> Deserialize<'de> for BiMap<K, V, S>
where
    K: Deserialize<'de> + Hash + Eq,
    V: Deserialize<'de> + Hash + Eq,
    S: BuildHasher + Default,
{
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        struct MapVisitor<K, V, S>(PhantomData<(K, V, S)>);
        impl<'de, K, V, S> Visitor<'de> for MapVisitor<K, V, S>
        where
            K: Deserialize<'de> + Hash + Eq,
            V: Deserialize<'de> + Hash + Eq,
            S: BuildHasher + Default,
        {
            type Value = BiMap<K, V, S>;
            fn expecting(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                f.write_str("a map with unique keys and unique values")
            }
            fn visit_map<A: MapAccess<'de>>(self, mut access: A) -> Result<Self::Value, A::Error> {
                let mut map = BiMap::with_capacity_and_hasher(
                    access.size_hint().unwrap_or(0).min(4096),
                    S::default(),
                );
                while let Some((key, value)) = access.next_entry()? {
                    if map.try_insert(key, value).is_err() {
                        return Err(A::Error::custom("duplicate key or value in bijective map"));
                    }
                }
                Ok(map)
            }
        }
        deserializer.deserialize_map(MapVisitor(PhantomData))
    }
}
