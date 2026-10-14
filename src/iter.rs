use crate::bidi_table::TableEntry;
use crate::surmap::Entry;
use crate::SurMap;
use std::iter::FusedIterator;

/// Shared iteration over mappings in storage order.
pub struct Iter<'a, K, V> {
    inner: IterInner<'a, K, V>,
}

enum IterInner<'a, K, V> {
    SurMap(std::slice::Iter<'a, Entry<K, V>>),
    BiMap(std::slice::Iter<'a, (K, V)>),
}

impl<'a, K, V> Iter<'a, K, V> {
    pub(crate) fn from_surmap(inner: std::slice::Iter<'a, Entry<K, V>>) -> Self {
        Self {
            inner: IterInner::SurMap(inner),
        }
    }
    pub(crate) fn from_bimap(inner: std::slice::Iter<'a, (K, V)>) -> Self {
        Self {
            inner: IterInner::BiMap(inner),
        }
    }
}

impl<K, V> Clone for Iter<'_, K, V> {
    fn clone(&self) -> Self {
        match &self.inner {
            IterInner::SurMap(inner) => Self::from_surmap(inner.clone()),
            IterInner::BiMap(inner) => Self::from_bimap(inner.clone()),
        }
    }
}

impl<'a, K, V> Iterator for Iter<'a, K, V> {
    type Item = (&'a K, &'a V);
    fn next(&mut self) -> Option<Self::Item> {
        match &mut self.inner {
            IterInner::SurMap(inner) => inner.next().map(|e| (&e.pair().0, &e.pair().1)),
            IterInner::BiMap(inner) => inner.next().map(|(k, v)| (k, v)),
        }
    }
    fn size_hint(&self) -> (usize, Option<usize>) {
        match &self.inner {
            IterInner::SurMap(inner) => inner.size_hint(),
            IterInner::BiMap(inner) => inner.size_hint(),
        }
    }
}
impl<K, V> DoubleEndedIterator for Iter<'_, K, V> {
    fn next_back(&mut self) -> Option<Self::Item> {
        match &mut self.inner {
            IterInner::SurMap(inner) => inner.next_back().map(|e| (&e.pair().0, &e.pair().1)),
            IterInner::BiMap(inner) => inner.next_back().map(|(k, v)| (k, v)),
        }
    }
}
impl<K, V> ExactSizeIterator for Iter<'_, K, V> {}
impl<K, V> FusedIterator for Iter<'_, K, V> {}

/// Owning iteration over mappings.
pub struct IntoIter<K, V> {
    inner: IntoIterInner<K, V>,
}

enum IntoIterInner<K, V> {
    SurMap(std::vec::IntoIter<Entry<K, V>>),
    BiMap(std::vec::IntoIter<(K, V)>),
}

impl<K, V> IntoIter<K, V> {
    pub(crate) fn from_surmap(inner: std::vec::IntoIter<Entry<K, V>>) -> Self {
        Self {
            inner: IntoIterInner::SurMap(inner),
        }
    }
    pub(crate) fn from_bimap(inner: std::vec::IntoIter<(K, V)>) -> Self {
        Self {
            inner: IntoIterInner::BiMap(inner),
        }
    }
}

impl<K, V> Iterator for IntoIter<K, V> {
    type Item = (K, V);
    fn next(&mut self) -> Option<Self::Item> {
        match &mut self.inner {
            IntoIterInner::SurMap(inner) => inner.next().map(TableEntry::into_pair),
            IntoIterInner::BiMap(inner) => inner.next(),
        }
    }
    fn size_hint(&self) -> (usize, Option<usize>) {
        match &self.inner {
            IntoIterInner::SurMap(inner) => inner.size_hint(),
            IntoIterInner::BiMap(inner) => inner.size_hint(),
        }
    }
}
impl<K, V> DoubleEndedIterator for IntoIter<K, V> {
    fn next_back(&mut self) -> Option<Self::Item> {
        match &mut self.inner {
            IntoIterInner::SurMap(inner) => inner.next_back().map(TableEntry::into_pair),
            IntoIterInner::BiMap(inner) => inner.next_back(),
        }
    }
}
impl<K, V> ExactSizeIterator for IntoIter<K, V> {}
impl<K, V> FusedIterator for IntoIter<K, V> {}

/// Draining iteration over owned mappings.
pub struct Drain<'a, K, V> {
    inner: DrainInner<'a, K, V>,
}

enum DrainInner<'a, K, V> {
    SurMap(std::vec::Drain<'a, Entry<K, V>>),
    BiMap(std::vec::Drain<'a, (K, V)>),
}

impl<'a, K, V> Drain<'a, K, V> {
    pub(crate) fn from_surmap(inner: std::vec::Drain<'a, Entry<K, V>>) -> Self {
        Self {
            inner: DrainInner::SurMap(inner),
        }
    }
    pub(crate) fn from_bimap(inner: std::vec::Drain<'a, (K, V)>) -> Self {
        Self {
            inner: DrainInner::BiMap(inner),
        }
    }
}

impl<'a, K, V> Iterator for Drain<'a, K, V> {
    type Item = (K, V);
    fn next(&mut self) -> Option<Self::Item> {
        match &mut self.inner {
            DrainInner::SurMap(inner) => inner.next().map(TableEntry::into_pair),
            DrainInner::BiMap(inner) => inner.next(),
        }
    }
    fn size_hint(&self) -> (usize, Option<usize>) {
        match &self.inner {
            DrainInner::SurMap(inner) => inner.size_hint(),
            DrainInner::BiMap(inner) => inner.size_hint(),
        }
    }
}
impl<K, V> DoubleEndedIterator for Drain<'_, K, V> {
    fn next_back(&mut self) -> Option<Self::Item> {
        match &mut self.inner {
            DrainInner::SurMap(inner) => inner.next_back().map(TableEntry::into_pair),
            DrainInner::BiMap(inner) => inner.next_back(),
        }
    }
}
impl<K, V> ExactSizeIterator for Drain<'_, K, V> {}
impl<K, V> FusedIterator for Drain<'_, K, V> {}

impl<'a, K, V, S> IntoIterator for &'a SurMap<K, V, S> {
    type Item = (&'a K, &'a V);
    type IntoIter = Iter<'a, K, V>;
    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

/// Iterates over the keys in one value group, newest first.
pub struct SurMapKeysIter<'a, K, V, S> {
    pub(crate) map: &'a SurMap<K, V, S>,
    pub(crate) entry: usize,
}

impl<'a, K, V, S> Iterator for SurMapKeysIter<'a, K, V, S> {
    type Item = &'a K;

    fn next(&mut self) -> Option<Self::Item> {
        let (key, next) = self.map.group_entry(self.entry)?;
        self.entry = next;
        Some(key)
    }
}

impl<K, V, S> Clone for SurMapKeysIter<'_, K, V, S> {
    fn clone(&self) -> Self {
        Self {
            map: self.map,
            entry: self.entry,
        }
    }
}

impl<K, V, S> std::iter::FusedIterator for SurMapKeysIter<'_, K, V, S> {}
