//! Immutable library prefixes with private, copy-on-write overrides and append-only
//! model tails. Cloning a prepared graph shares its large element/scope storage.
//!
//! The tables iterate by reference only. A pass that needs owned rows
//! copies the rows it selects, never a whole table, so the shared library
//! prefix is never duplicated behind a by-value loop.
use serde::{Deserialize, Deserializer, Serialize, Serializer};
use std::{
    collections::HashMap,
    hash::BuildHasherDefault,
    ops::{Index, IndexMut},
    sync::Arc,
};

/// A hasher for the keys the tables are indexed by — row indices, scope
/// indices, identities: a multiply-rotate fold of the key's words, cheap
/// where the standard hasher's keyed rounds cost a resolution pass a few
/// percent. Iteration order of a table hashed this way is as unspecified
/// as it was with the standard hasher, so nothing may read one.
#[derive(Clone, Copy, Default)]
pub(crate) struct IdHasher(u64);

impl IdHasher {
    #[inline]
    fn add(&mut self, word: u64) {
        self.0 = (self.0.rotate_left(5) ^ word).wrapping_mul(0x517c_c1b7_2722_0a95);
    }
}

impl std::hash::Hasher for IdHasher {
    #[inline]
    fn finish(&self) -> u64 {
        // The low bits of a short key's last product depend on few of
        // its bytes; fold the high half in for the bucket index.
        self.0 ^ (self.0 >> 32)
    }
    #[inline]
    fn write(&mut self, bytes: &[u8]) {
        for chunk in bytes.chunks(8) {
            let mut word = [0u8; 8];
            word[..chunk.len()].copy_from_slice(chunk);
            self.add(u64::from_le_bytes(word));
        }
    }
    #[inline]
    fn write_u8(&mut self, i: u8) {
        self.add(u64::from(i));
    }
    #[inline]
    fn write_u16(&mut self, i: u16) {
        self.add(u64::from(i));
    }
    #[inline]
    fn write_u32(&mut self, i: u32) {
        self.add(u64::from(i));
    }
    #[inline]
    fn write_u64(&mut self, i: u64) {
        self.add(i);
    }
    #[inline]
    fn write_usize(&mut self, i: usize) {
        self.add(i as u64);
    }
}

/// A hash map over the tables' keys (see [`IdHasher`]).
pub(crate) type IdMap<K, V> = HashMap<K, V, BuildHasherDefault<IdHasher>>;
/// A hash set over the tables' keys (see [`IdHasher`]).
pub(crate) type IdSet<K> = std::collections::HashSet<K, BuildHasherDefault<IdHasher>>;

#[cfg(test)]
thread_local! {
    static COPIED_ROWS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

/// Rows deep-copied on the current thread by whole-table clones and
/// prefix merges. Building a graph copies rows; a check pass over a
/// built graph must not.
#[cfg(test)]
pub(crate) fn copied_rows() -> usize {
    COPIED_ROWS.with(|c| c.get())
}

#[cfg(test)]
fn note_copied(rows: usize) {
    COPIED_ROWS.with(|c| c.set(c.get() + rows));
}

#[cfg(not(test))]
fn note_copied(_rows: usize) {}

/// Opaque content revision, allocated only when a reader observes a snapshot.
/// Mutable access clears the table's token, even if its length stays unchanged.
/// Pointer identity is safe because observers retain a strong reference.
#[derive(Clone, Default)]
pub(crate) struct Revision(Arc<()>);
impl Revision {
    pub(crate) fn same_as(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.0, &other.0)
    }
}

pub(crate) struct LayeredVec<T> {
    revision: Option<Revision>,
    base: Arc<Vec<T>>,
    changed: Vec<Option<Box<T>>>,
    tail: Vec<T>,
}
impl<T: Clone> Clone for LayeredVec<T> {
    fn clone(&self) -> Self {
        note_copied(self.changed.iter().flatten().count() + self.tail.len());
        Self {
            revision: self.revision.clone(),
            base: Arc::clone(&self.base),
            changed: self.changed.clone(),
            tail: self.tail.clone(),
        }
    }
}
impl<T> Default for LayeredVec<T> {
    fn default() -> Self {
        Self {
            revision: None,
            base: Arc::new(Vec::new()),
            changed: Vec::new(),
            tail: Vec::new(),
        }
    }
}
impl<T> LayeredVec<T> {
    pub(crate) fn revision(&self) -> Option<&Revision> {
        self.revision.as_ref()
    }
    pub(crate) fn observe_revision(&mut self) -> Revision {
        self.revision.get_or_insert_with(Revision::default).clone()
    }
    /// Install a fully staged append and the exact revision reserved by its
    /// semantic snapshot. No caller code runs between validation and append.
    pub(crate) fn append_staged(&mut self, rows: Vec<T>, expected: &Revision, next: Revision) {
        assert!(self.revision().is_some_and(|now| now.same_as(expected)));
        if rows.is_empty() {
            assert!(next.same_as(expected));
            return;
        }
        assert!(!next.same_as(expected));
        self.tail.extend(rows);
        self.revision = Some(next);
    }
    pub fn len(&self) -> usize {
        self.base.len() + self.tail.len()
    }
    /// The frozen rows this table shares with the table it was cloned from.
    pub(crate) fn base_arc(&self) -> &Arc<Vec<T>> {
        &self.base
    }
    pub(crate) fn base_len(&self) -> usize {
        self.base.len()
    }
    /// Whether no frozen row has been written since the freeze: a scan of
    /// the frozen rows then still describes them.
    pub(crate) fn base_untouched(&self) -> bool {
        self.changed.is_empty()
    }
    pub fn get(&self, i: usize) -> Option<&T> {
        (i < self.len()).then(|| &self[i])
    }
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
    /// Restrict removal to the mutable suffix; prepared/library rows remain.
    pub fn can_truncate_tail(&self, n: usize) -> bool {
        self.base.len() <= n && n <= self.len()
    }
    pub fn truncate_tail(&mut self, n: usize) {
        assert!(self.can_truncate_tail(n));
        if n == self.len() {
            return;
        }
        self.revision = None;
        self.tail.truncate(n - self.base.len());
    }
    pub fn push(&mut self, value: T) {
        self.revision = None;
        self.tail.push(value)
    }
    pub fn iter(&self) -> impl DoubleEndedIterator<Item = &T> {
        self.base
            .iter()
            .enumerate()
            .map(|(i, value)| {
                self.changed
                    .get(i)
                    .and_then(Option::as_deref)
                    .unwrap_or(value)
            })
            .chain(self.tail.iter())
    }
    pub fn freeze(&mut self)
    where
        T: Clone,
    {
        if self.tail.is_empty() && self.changed.is_empty() {
            return;
        }
        if self.base.is_empty() {
            self.base = Arc::new(std::mem::take(&mut self.tail));
        } else {
            note_copied(self.len());
            self.base = Arc::new(self.iter().cloned().collect());
            self.tail.clear();
        }
        self.changed.clear();
    }
}
impl<T> From<Vec<T>> for LayeredVec<T> {
    fn from(tail: Vec<T>) -> Self {
        Self {
            tail,
            ..Self::default()
        }
    }
}
impl<T> Index<usize> for LayeredVec<T> {
    type Output = T;
    fn index(&self, i: usize) -> &T {
        if i < self.base.len() {
            self.changed
                .get(i)
                .and_then(Option::as_deref)
                .unwrap_or(&self.base[i])
        } else {
            &self.tail[i - self.base.len()]
        }
    }
}
impl<T: Clone> IndexMut<usize> for LayeredVec<T> {
    fn index_mut(&mut self, i: usize) -> &mut T {
        self.revision = None;
        if i < self.base.len() {
            if self.changed.is_empty() {
                self.changed.resize_with(self.base.len(), || None);
            }
            self.changed[i].get_or_insert_with(|| Box::new(self.base[i].clone()))
        } else {
            &mut self.tail[i - self.base.len()]
        }
    }
}
impl<T: Serialize> Serialize for LayeredVec<T> {
    fn serialize<S: Serializer>(&self, s: S) -> Result<S::Ok, S::Error> {
        s.collect_seq(self.iter())
    }
}
impl<'de, T: Deserialize<'de>> Deserialize<'de> for LayeredVec<T> {
    fn deserialize<D: Deserializer<'de>>(d: D) -> Result<Self, D::Error> {
        Vec::deserialize(d).map(Self::from)
    }
}

impl<T: Clone> LayeredVec<T> {
    pub fn resize(&mut self, n: usize, value: T) {
        assert!(n >= self.len());
        if n != self.len() {
            self.revision = None;
        }
        self.tail.resize(n - self.base.len(), value);
    }
}

#[cfg(test)]
impl<T> LayeredVec<T> {
    pub fn shares_prefix(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.base, &other.base)
    }
}

/// Lookup table with an immutable library base and a private model table.
pub(crate) struct LayeredMap<K, V> {
    base: Arc<IdMap<K, V>>,
    local: IdMap<K, V>,
}
impl<K: Clone, V: Clone> Clone for LayeredMap<K, V> {
    fn clone(&self) -> Self {
        note_copied(self.local.len());
        Self {
            base: Arc::clone(&self.base),
            local: self.local.clone(),
        }
    }
}
impl<K, V> Default for LayeredMap<K, V> {
    fn default() -> Self {
        Self {
            base: Arc::new(IdMap::default()),
            local: IdMap::default(),
        }
    }
}
impl<K: Eq + std::hash::Hash, V> LayeredMap<K, V> {
    pub fn get(&self, key: &K) -> Option<&V> {
        self.local.get(key).or_else(|| self.base.get(key))
    }
    pub fn insert(&mut self, key: K, value: V) {
        self.local.insert(key, value);
    }
    pub fn freeze(&mut self)
    where
        K: Clone,
        V: Clone,
    {
        if self.local.is_empty() {
            return;
        }
        if self.base.is_empty() {
            self.base = Arc::new(std::mem::take(&mut self.local));
        } else {
            if Arc::get_mut(&mut self.base).is_none() {
                note_copied(self.base.len());
            }
            Arc::make_mut(&mut self.base).extend(std::mem::take(&mut self.local));
        }
    }
}
impl<K: Serialize + Eq + std::hash::Hash, V: Serialize> Serialize for LayeredMap<K, V> {
    fn serialize<S: Serializer>(&self, s: S) -> Result<S::Ok, S::Error> {
        use serde::ser::SerializeMap;
        let len = self.local.len()
            + self
                .base
                .keys()
                .filter(|k| !self.local.contains_key(k))
                .count();
        let mut map = s.serialize_map(Some(len))?;
        for (k, v) in self
            .base
            .iter()
            .filter(|(k, _)| !self.local.contains_key(k))
            .chain(self.local.iter())
        {
            map.serialize_entry(k, v)?;
        }
        map.end()
    }
}
impl<'de, K: Deserialize<'de> + Eq + std::hash::Hash, V: Deserialize<'de>> Deserialize<'de>
    for LayeredMap<K, V>
{
    fn deserialize<D: Deserializer<'de>>(d: D) -> Result<Self, D::Error> {
        Ok(Self {
            local: IdMap::deserialize(d)?,
            ..Self::default()
        })
    }
}

impl<K: Eq + std::hash::Hash, V> LayeredMap<K, V> {
    /// The frozen table, while no local row overlays it.
    pub(crate) fn frozen_arc(&self) -> Option<&Arc<IdMap<K, V>>> {
        self.local.is_empty().then_some(&self.base)
    }
    pub fn contains_key(&self, k: &K) -> bool {
        self.local.contains_key(k) || self.base.contains_key(k)
    }
    pub fn iter(&self) -> impl Iterator<Item = (&K, &V)> {
        self.base
            .iter()
            .filter(|(k, _)| !self.local.contains_key(k))
            .chain(self.local.iter())
    }
    pub fn keys(&self) -> impl Iterator<Item = &K> {
        self.iter().map(|(k, _)| k)
    }
    /// Whether both tables hold the same value for every key `admit`
    /// accepts. Tables sharing one base differ only in their private rows.
    pub fn agrees_on(&self, other: &Self, admit: impl Fn(&K) -> bool) -> bool
    where
        V: PartialEq,
    {
        let keys: Box<dyn Iterator<Item = &K>> = if Arc::ptr_eq(&self.base, &other.base) {
            Box::new(self.local.keys().chain(other.local.keys()))
        } else {
            Box::new(self.keys().chain(other.keys()))
        };
        keys.filter(|k| admit(k))
            .all(|k| self.get(k) == other.get(k))
    }
}
impl<K: Eq + std::hash::Hash + Clone, V: Clone> LayeredMap<K, V> {
    pub fn entry(&mut self, k: K) -> std::collections::hash_map::Entry<'_, K, V> {
        if !self.local.contains_key(&k) {
            if let Some(value) = self.base.get(&k) {
                self.local.insert(k.clone(), value.clone());
            }
        }
        self.local.entry(k)
    }
}
impl<K: Eq + std::hash::Hash, V> FromIterator<(K, V)> for LayeredMap<K, V> {
    fn from_iter<I: IntoIterator<Item = (K, V)>>(iter: I) -> Self {
        Self {
            local: iter.into_iter().collect(),
            ..Self::default()
        }
    }
}
impl<'a, K: Eq + std::hash::Hash, V> IntoIterator for &'a LayeredMap<K, V> {
    type Item = (&'a K, &'a V);
    type IntoIter = Box<dyn Iterator<Item = Self::Item> + 'a>;
    fn into_iter(self) -> Self::IntoIter {
        Box::new(self.iter())
    }
}
impl<'a, T> IntoIterator for &'a LayeredVec<T> {
    type Item = &'a T;
    type IntoIter = Box<dyn Iterator<Item = &'a T> + 'a>;
    fn into_iter(self) -> Self::IntoIter {
        Box::new(self.iter())
    }
}
impl<T> FromIterator<T> for LayeredVec<T> {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        Vec::from_iter(iter).into()
    }
}
impl<T> Extend<T> for LayeredVec<T> {
    fn extend<I: IntoIterator<Item = T>>(&mut self, iter: I) {
        self.revision = None;
        self.tail.extend(iter);
    }
}

#[cfg(test)]
mod overlay_tests {
    use super::*;
    #[test]
    fn deserialization_preserves_rows_without_reusing_snapshot_revision() {
        let mut rows: LayeredVec<_> = vec![1, 2].into();
        let observed = rows.observe_revision();
        let bytes = serde_json::to_vec(&rows).unwrap();
        let mut decoded: LayeredVec<i32> = serde_json::from_slice(&bytes).unwrap();
        assert_eq!(
            rows.iter().copied().collect::<Vec<_>>(),
            decoded.iter().copied().collect::<Vec<_>>()
        );
        assert!(decoded.revision().is_none());
        assert!(!observed.same_as(&decoded.observe_revision()));
    }

    #[test]
    fn revisions_follow_rows_across_clone_freeze_and_same_length_edits() {
        let mut rows: LayeredVec<_> = vec![1, 2].into();
        assert!(rows.revision().is_none());
        let original = rows.observe_revision();
        rows.freeze();
        assert!(original.same_as(rows.revision().unwrap()));
        let mut copy = rows.clone();
        assert!(original.same_as(copy.revision().unwrap()));
        copy[0] = 3;
        assert!(copy.revision().is_none());
        assert!(original.same_as(rows.revision().unwrap()));
        let edited = copy.observe_revision();
        assert!(!original.same_as(&edited));
        copy.freeze();
        assert!(edited.same_as(copy.revision().unwrap()));
        copy.push(4);
        assert!(copy.revision().is_none());
        let pushed = copy.observe_revision();
        copy.extend([5]);
        assert!(copy.revision().is_none());
        assert!(!pushed.same_as(&copy.observe_revision()));
        copy.resize(5, 6);
        assert!(copy.revision().is_none());
        let mut replaced: LayeredVec<_> = vec![1, 2].into();
        assert!(!original.same_as(&replaced.observe_revision()));
    }
    #[test]
    fn overrides_append_and_refreeze_do_not_change_shared_bases() {
        let mut a: LayeredVec<_> = vec![1, 2].into();
        a.freeze();
        let mut b = a.clone();
        b[0] = 3;
        b.push(4);
        b.freeze();
        assert_eq!(a.iter().copied().collect::<Vec<_>>(), vec![1, 2]);
        assert_eq!(b.iter().copied().collect::<Vec<_>>(), vec![3, 2, 4]);
        let mut a: LayeredMap<_, _> = [(1, 2)].into_iter().collect();
        a.freeze();
        let mut b = a.clone();
        *b.entry(1).or_default() = 3;
        b.insert(4, 5);
        b.freeze();
        assert_eq!(a.get(&1), Some(&2));
        assert_eq!(a.get(&4), None);
        assert_eq!(b.get(&1), Some(&3));
        assert_eq!(b.get(&4), Some(&5));
    }
    #[test]
    fn reference_iteration_copies_nothing_and_copies_are_counted() {
        let mut a: LayeredVec<_> = vec![1, 2].into();
        a.freeze();
        let mut b = a.clone();
        b.push(3);
        let before = copied_rows();
        assert_eq!(b.iter().sum::<i32>(), 6);
        assert_eq!((&b).into_iter().count(), 3);
        assert_eq!(copied_rows(), before, "reading a table copies no rows");
        let c = b.clone();
        assert_eq!(copied_rows(), before + 1, "a clone copies only the tail");
        drop(c);
        b.freeze();
        assert_eq!(
            copied_rows(),
            before + 4,
            "merging a shared prefix copies it"
        );
        let mut m: LayeredMap<_, _> = [(1, 2)].into_iter().collect();
        m.freeze();
        let mut n = m.clone();
        n.insert(3, 4);
        let before = copied_rows();
        assert_eq!(n.iter().count(), 2);
        assert_eq!(copied_rows(), before);
        let _ = n.clone();
        assert_eq!(copied_rows(), before + 1);
        n.freeze();
        assert_eq!(
            copied_rows(),
            before + 2,
            "merging a shared prefix copies it"
        );
    }
}

#[cfg(test)]
mod staged_revision_tests {
    use super::*;
    #[test]
    fn append_installs_exact_token_and_other_mutations_invalidate_it() {
        let mut rows: LayeredVec<_> = vec![1].into();
        let old = rows.observe_revision();
        let next = Revision::default();
        rows.append_staged(vec![2], &old, next.clone());
        assert!(!rows.revision().unwrap().same_as(&old));
        assert!(rows.observe_revision().same_as(&next));
        rows[0] = 3;
        assert!(rows.revision().is_none());
        let same = rows.observe_revision();
        rows.append_staged(Vec::new(), &same, same.clone());
        assert!(rows.observe_revision().same_as(&same));
    }
}
