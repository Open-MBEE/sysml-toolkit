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

/// Scratch marks over an index space — an element or a scope table's —
/// reused across the enumerations of a build. A mark is the stamp of the
/// set it belongs to, so a new set costs nothing to begin and an index is
/// marked with a load, a compare and a store; the storage grows to the
/// largest index marked and stays.
#[derive(Default)]
pub(crate) struct Marks {
    generation: u32,
    stamps: Vec<u32>,
}
impl Marks {
    /// Begin a new, empty set over the same storage.
    pub(crate) fn begin(&mut self) {
        if self.generation == u32::MAX {
            self.stamps.fill(0);
            self.generation = 0;
        }
        self.generation += 1;
    }
    /// Put `i` in the set: whether it was not in it yet.
    #[inline]
    pub(crate) fn mark(&mut self, i: usize) -> bool {
        if i >= self.stamps.len() {
            self.stamps.resize(i + 1, 0);
        }
        let stamp = &mut self.stamps[i];
        if *stamp == self.generation {
            false
        } else {
            *stamp = self.generation;
            true
        }
    }
    /// Whether `i` is in the set.
    #[inline]
    pub(crate) fn marked(&self, i: usize) -> bool {
        self.stamps.get(i).is_some_and(|&s| s == self.generation)
    }
}

#[cfg(test)]
mod marks_tests {
    use super::Marks;

    #[test]
    fn a_set_begins_empty_and_marks_once() {
        let mut m = Marks::default();
        m.begin();
        assert!(!m.marked(3));
        assert!(m.mark(3));
        assert!(!m.mark(3));
        assert!(m.marked(3));
        assert!(!m.marked(4));
        m.begin();
        assert!(!m.marked(3));
        assert!(m.mark(3));
    }

    #[test]
    fn the_stamps_survive_a_generation_wrap() {
        let mut m = Marks {
            generation: u32::MAX - 1,
            stamps: Vec::new(),
        };
        m.begin();
        assert!(m.mark(7));
        m.begin();
        assert_eq!(m.generation, 1);
        assert!(!m.marked(7));
        assert!(m.mark(7));
    }
}

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
pub(crate) fn note_copied(rows: usize) {
    COPIED_ROWS.with(|c| c.set(c.get() + rows));
}

#[cfg(not(test))]
pub(crate) fn note_copied(_rows: usize) {}

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
    /// Token of the rows as they stand, allocated only when a reader
    /// observes them ([`Self::observe_rows`]): an append keeps it, and a
    /// write to a row already there, a truncation or a cut of the base
    /// clears it. Unlike [`Self::revision`], it therefore says that every
    /// row the observer saw is still as it saw it, whatever was appended.
    rows: Option<Revision>,
    base: Arc<Vec<T>>,
    /// How many of the base's rows this vector reads: all of them, unless
    /// [`Self::limit_base`] cut it short.
    limit: usize,
    /// The rows above the base shared between forks of this vector
    /// ([`Self::share_tail`]), read at `limit..limit + upper.len()`; a
    /// write to one goes to `changed` like a write to a base row.
    upper: Option<Arc<Vec<T>>>,
    changed: Vec<Option<Box<T>>>,
    /// How many base rows `changed` holds a write of: the shared rows'
    /// writes are the vector's own rows changing, not the base's.
    base_written: usize,
    tail: Vec<T>,
}
impl<T: Clone> Clone for LayeredVec<T> {
    fn clone(&self) -> Self {
        note_copied(self.changed.iter().flatten().count() + self.tail.len());
        Self {
            revision: self.revision.clone(),
            rows: self.rows.clone(),
            base: Arc::clone(&self.base),
            limit: self.limit,
            upper: self.upper.clone(),
            changed: self.changed.clone(),
            base_written: self.base_written,
            tail: self.tail.clone(),
        }
    }
}
impl<T> Default for LayeredVec<T> {
    fn default() -> Self {
        Self {
            revision: None,
            rows: None,
            base: Arc::new(Vec::new()),
            limit: 0,
            upper: None,
            changed: Vec::new(),
            base_written: 0,
            tail: Vec::new(),
        }
    }
}
impl<T> LayeredVec<T> {
    /// How many rows are frozen: the base's read rows and the shared ones.
    fn frozen_len(&self) -> usize {
        self.limit + self.upper.as_ref().map_or(0, |upper| upper.len())
    }
    /// The frozen row `i`, from the shared rows or the base.
    fn frozen(&self, i: usize) -> &T {
        if i < self.limit {
            &self.base[i]
        } else {
            &self.upper.as_ref().expect("a shared row")[i - self.limit]
        }
    }
    pub(crate) fn revision(&self) -> Option<&Revision> {
        self.revision.as_ref()
    }
    pub(crate) fn observe_revision(&mut self) -> Revision {
        self.revision.get_or_insert_with(Revision::default).clone()
    }
    /// A token for the rows as they stand now (see [`Self::rows_kept_since`]).
    pub(crate) fn observe_rows(&mut self) -> Revision {
        self.rows.get_or_insert_with(Revision::default).clone()
    }
    /// Whether every row there was when `token` was observed is still there
    /// and unwritten: rows appended since are allowed.
    pub(crate) fn rows_kept_since(&self, token: &Revision) -> bool {
        self.rows.as_ref().is_some_and(|rows| rows.same_as(token))
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
        self.frozen_len() + self.tail.len()
    }
    /// The frozen rows this table shares with the table it was cloned from.
    pub(crate) fn base_arc(&self) -> &Arc<Vec<T>> {
        &self.base
    }
    pub(crate) fn base_len(&self) -> usize {
        self.limit
    }
    /// Read only the first `limit` rows of the shared base from here on: a
    /// view of a frozen prefix cut short, over the same rows in memory.
    /// Only for a vector with nothing written or appended.
    pub(crate) fn limit_base(&mut self, limit: usize) {
        assert!(
            limit <= self.base.len()
                && self.tail.is_empty()
                && self.changed.is_empty()
                && self.upper.is_none()
        );
        self.limit = limit;
        self.revision = None;
        self.rows = None;
    }
    /// Whether no frozen row has been written since the freeze: a scan of
    /// the frozen rows then still describes them.
    pub(crate) fn base_untouched(&self) -> bool {
        self.base_written == 0
    }
    /// The frozen rows written since the freeze.
    pub(crate) fn written_rows(&self) -> impl Iterator<Item = usize> + '_ {
        self.changed
            .iter()
            .take(self.limit)
            .enumerate()
            .filter_map(|(i, row)| row.is_some().then_some(i))
    }
    pub fn get(&self, i: usize) -> Option<&T> {
        (i < self.len()).then(|| &self[i])
    }
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
    /// Restrict removal to the mutable suffix; prepared/library rows remain.
    pub fn can_truncate_tail(&self, n: usize) -> bool {
        self.limit <= n && n <= self.len()
    }
    pub fn truncate_tail(&mut self, n: usize)
    where
        T: Clone,
    {
        assert!(self.can_truncate_tail(n));
        if n == self.len() {
            return;
        }
        if n < self.frozen_len() {
            self.unshare_tail();
        }
        self.revision = None;
        self.rows = None;
        self.tail.truncate(n - self.frozen_len());
    }
    /// Share the rows above the base: a clone of this vector then shares
    /// them instead of copying them, as it does the base. The rows read
    /// and write as before (a write copies the row to `changed`).
    #[cfg(any(not(target_family = "wasm"), test))]
    pub(crate) fn share_tail(&mut self)
    where
        T: Clone,
    {
        if self.tail.is_empty() {
            return;
        }
        let mut rows = match self.upper.take() {
            None => Vec::new(),
            Some(upper) => {
                note_copied(upper.len());
                let rows: Vec<T> = upper
                    .iter()
                    .enumerate()
                    .map(|(j, row)| {
                        self.changed
                            .get(self.limit + j)
                            .and_then(Option::as_deref)
                            .unwrap_or(row)
                            .clone()
                    })
                    .collect();
                self.changed.truncate(self.limit);
                rows
            }
        };
        rows.append(&mut self.tail);
        self.upper = Some(Arc::new(rows));
    }
    /// Take the shared rows back as rows of this vector's own, copied.
    pub(crate) fn unshare_tail(&mut self)
    where
        T: Clone,
    {
        let Some(upper) = self.upper.take() else {
            return;
        };
        note_copied(upper.len());
        let mut rows: Vec<T> = upper
            .iter()
            .enumerate()
            .map(|(j, row)| {
                self.changed
                    .get(self.limit + j)
                    .and_then(Option::as_deref)
                    .unwrap_or(row)
                    .clone()
            })
            .collect();
        self.changed.truncate(self.limit);
        rows.append(&mut self.tail);
        self.tail = rows;
    }
    pub fn push(&mut self, value: T) {
        self.revision = None;
        self.tail.push(value)
    }
    pub fn iter<'a>(&'a self) -> impl DoubleEndedIterator<Item = &'a T> + 'a {
        let upper: &'a [T] = self.upper.as_deref().map_or(&[], Vec::as_slice);
        let written = move |i: usize, value: &'a T| -> &'a T {
            self.changed
                .get(i)
                .and_then(Option::as_deref)
                .unwrap_or(value)
        };
        self.base[..self.limit]
            .iter()
            .enumerate()
            .map(move |(i, value)| written(i, value))
            .chain(
                upper
                    .iter()
                    .enumerate()
                    .map(move |(j, value)| written(self.limit + j, value)),
            )
            .chain(self.tail.iter())
    }
    pub fn freeze(&mut self)
    where
        T: Clone,
    {
        if self.tail.is_empty() && self.changed.is_empty() && self.upper.is_none() {
            return;
        }
        if self.base.is_empty() && self.upper.is_none() {
            self.base = Arc::new(std::mem::take(&mut self.tail));
        } else {
            note_copied(self.len());
            self.base = Arc::new(self.iter().cloned().collect());
            self.tail.clear();
            self.upper = None;
        }
        self.limit = self.base.len();
        self.changed.clear();
        self.base_written = 0;
    }
}
impl<T> LayeredVec<T> {
    /// A table over the frozen rows `base`, with no rows of its own yet.
    pub(crate) fn over(base: Arc<Vec<T>>) -> Self {
        Self {
            limit: base.len(),
            base,
            ..Self::default()
        }
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
        let frozen = self.frozen_len();
        if i < frozen {
            self.changed
                .get(i)
                .and_then(Option::as_deref)
                .unwrap_or_else(|| self.frozen(i))
        } else {
            &self.tail[i - frozen]
        }
    }
}
impl<T: Clone> IndexMut<usize> for LayeredVec<T> {
    fn index_mut(&mut self, i: usize) -> &mut T {
        self.revision = None;
        self.rows = None;
        let frozen = self.frozen_len();
        if i < frozen {
            if self.changed.len() < frozen {
                self.changed.resize_with(frozen, || None);
            }
            if self.changed[i].is_none() {
                let row = Box::new(self.frozen(i).clone());
                self.changed[i] = Some(row);
                if i < self.limit {
                    self.base_written += 1;
                }
            }
            self.changed[i].as_deref_mut().expect("written")
        } else {
            &mut self.tail[i - frozen]
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
        let frozen = self.frozen_len();
        self.tail.resize(n - frozen, value);
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
    /// How many private rows hold a key the frozen table holds too, so
    /// that [`Self::len`] counts each key once without a walk.
    shadowed: usize,
}
impl<K: Clone, V: Clone> Clone for LayeredMap<K, V> {
    fn clone(&self) -> Self {
        note_copied(self.local.len());
        Self {
            base: Arc::clone(&self.base),
            local: self.local.clone(),
            shadowed: self.shadowed,
        }
    }
}
impl<K, V> Default for LayeredMap<K, V> {
    fn default() -> Self {
        Self {
            base: Arc::new(IdMap::default()),
            local: IdMap::default(),
            shadowed: 0,
        }
    }
}
impl<K: Eq + std::hash::Hash, V> LayeredMap<K, V> {
    pub fn get(&self, key: &K) -> Option<&V> {
        self.local.get(key).or_else(|| self.base.get(key))
    }
    pub fn insert(&mut self, key: K, value: V) {
        match self.local.entry(key) {
            std::collections::hash_map::Entry::Occupied(mut row) => {
                row.insert(value);
            }
            // the frozen table is read only for a key new to the private one
            std::collections::hash_map::Entry::Vacant(row) => {
                self.shadowed += usize::from(self.base.contains_key(row.key()));
                row.insert(value);
            }
        }
    }
    /// Drop the private rows; the frozen table stays.
    pub fn clear_local(&mut self) {
        self.local.clear();
        self.shadowed = 0;
    }
    pub fn freeze(&mut self)
    where
        K: Clone,
        V: Clone,
    {
        if self.local.is_empty() {
            return;
        }
        self.shadowed = 0;
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
        // Written in the tables' own order, which is byte-stable from one
        // process to the next: the hasher is unseeded and the inserts that
        // made the tables happen in the same order every time, so the same
        // map is laid out, and so written, the same way (a snapshot's
        // bytes depend on it).
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
    /// A table over the frozen table `base`, with no rows of its own yet.
    pub(crate) fn over(base: Arc<IdMap<K, V>>) -> Self {
        Self {
            base,
            local: IdMap::default(),
            shadowed: 0,
        }
    }
    pub fn is_empty(&self) -> bool {
        self.base.is_empty() && self.local.is_empty()
    }
    /// How many keys the table holds, a private row over a frozen one of
    /// the same key counting once.
    pub fn len(&self) -> usize {
        self.base.len() + self.local.len() - self.shadowed
    }
    /// The shared frozen table, overlaid or not.
    pub(crate) fn base_arc(&self) -> &Arc<IdMap<K, V>> {
        &self.base
    }
    /// The private table's rows: those written over the frozen table.
    pub(crate) fn local_iter(&self) -> impl Iterator<Item = (&K, &V)> {
        self.local.iter()
    }
    pub(crate) fn local_contains_key(&self, k: &K) -> bool {
        self.local.contains_key(k)
    }
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
impl<K: Eq + std::hash::Hash, V: Clone> LayeredMap<K, V> {
    /// [`Self::insert`], answering the value the table held at `key`
    /// before: its private one, else its frozen one.
    pub fn replace(&mut self, key: K, value: V) -> Option<V> {
        match self.local.entry(key) {
            std::collections::hash_map::Entry::Occupied(mut row) => Some(row.insert(value)),
            std::collections::hash_map::Entry::Vacant(row) => {
                let frozen = self.base.get(row.key()).cloned();
                self.shadowed += usize::from(frozen.is_some());
                row.insert(value);
                frozen
            }
        }
    }
}
impl<K: Eq + std::hash::Hash + Clone, V: Clone> LayeredMap<K, V> {
    /// The private row at `k`, to fill in place: a copy of the frozen row
    /// there, when the private table has none and the frozen one has.
    pub fn entry(&mut self, k: K) -> Entry<'_, K, V> {
        if !self.local.contains_key(&k) {
            if let Some(value) = self.base.get(&k) {
                self.local.insert(k.clone(), value.clone());
                self.shadowed += 1;
            }
        }
        Entry(self.local.entry(k))
    }
}

/// A private row's slot, from [`LayeredMap::entry`]: the row is filled in
/// place and never taken out, so that the count of private rows over frozen
/// ones behind [`LayeredMap::len`] stays right.
pub(crate) struct Entry<'a, K, V>(std::collections::hash_map::Entry<'a, K, V>);
impl<'a, K, V> Entry<'a, K, V> {
    pub fn or_insert(self, default: V) -> &'a mut V {
        self.0.or_insert(default)
    }
    pub fn or_insert_with(self, default: impl FnOnce() -> V) -> &'a mut V {
        self.0.or_insert_with(default)
    }
    pub fn or_default(self) -> &'a mut V
    where
        V: Default,
    {
        self.0.or_default()
    }
}
impl<K: Eq + std::hash::Hash, V> From<IdMap<K, V>> for LayeredMap<K, V> {
    /// A table of these rows alone, over no frozen table.
    fn from(local: IdMap<K, V>) -> Self {
        Self {
            local,
            ..Self::default()
        }
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

/// A row per scope, the rows below `floor` — a prepared library's scopes,
/// under a build on it — kept only once written: a build reads few of the
/// library's scopes, and a row for each of them cost every build the
/// library's size. A row never written reads as the default.
#[derive(Clone, Default)]
pub(crate) struct ScopeTable<T> {
    floor: usize,
    sparse: IdMap<usize, T>,
    dense: Vec<T>,
    unwritten: T,
}
impl<T: Clone + Default> ScopeTable<T> {
    /// `n` default rows, those below `floor` kept sparse.
    pub(crate) fn new(floor: usize, n: usize) -> Self {
        let floor = floor.min(n);
        Self {
            floor,
            sparse: IdMap::default(),
            dense: vec![T::default(); n - floor],
            unwritten: T::default(),
        }
    }
    pub(crate) fn len(&self) -> usize {
        self.floor + self.dense.len()
    }
    pub(crate) fn push(&mut self, value: T) {
        self.dense.push(value);
    }
    pub(crate) fn get(&self, s: usize) -> Option<&T> {
        if s < self.floor {
            Some(self.sparse.get(&s).unwrap_or(&self.unwritten))
        } else {
            self.dense.get(s - self.floor)
        }
    }
    /// Grow to `n` rows, the new ones `value`.
    pub(crate) fn resize(&mut self, n: usize, value: T) {
        if n > self.len() {
            self.dense.resize(n - self.floor, value);
        }
    }
    /// Every row `value`.
    #[cfg(test)]
    pub(crate) fn fill(&mut self, value: T) {
        self.sparse.clear();
        self.dense.fill(value.clone());
        self.unwritten = value;
    }
}
impl<T> Index<usize> for ScopeTable<T> {
    type Output = T;
    fn index(&self, s: usize) -> &T {
        if s < self.floor {
            self.sparse.get(&s).unwrap_or(&self.unwritten)
        } else {
            &self.dense[s - self.floor]
        }
    }
}
impl<T: Clone> IndexMut<usize> for ScopeTable<T> {
    fn index_mut(&mut self, s: usize) -> &mut T {
        if s < self.floor {
            let Self {
                sparse, unwritten, ..
            } = self;
            sparse.entry(s).or_insert_with(|| unwritten.clone())
        } else {
            &mut self.dense[s - self.floor]
        }
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

    /// The keys a table holds, counted as its rows are read.
    fn counted(map: &LayeredMap<i32, i32>) -> usize {
        map.keys().count()
    }

    #[test]
    fn an_entry_fills_its_row_in_place_and_counts_it_once() {
        let frozen: LayeredMap<_, _> = [(1, 10), (2, 20)].into_iter().collect();
        let mut map = frozen.clone();
        map.freeze();
        *map.entry(1).or_default() += 1;
        *map.entry(1).or_insert(0) += 1;
        *map.entry(2).or_insert_with(|| 0) += 2;
        *map.entry(3).or_insert(30) += 1;
        *map.entry(3).or_insert_with(|| 0) += 0;
        assert_eq!(
            map.get(&1),
            Some(&12),
            "a frozen row is copied, then filled"
        );
        assert_eq!(map.get(&2), Some(&22));
        assert_eq!(map.get(&3), Some(&31), "a new row is made, then filled");
        assert_eq!((map.len(), counted(&map)), (3, 3));
        assert_eq!(frozen.get(&1), Some(&10), "the frozen table is as it was");
        map.freeze();
        assert_eq!((map.len(), counted(&map)), (3, 3));
    }

    #[test]
    fn a_private_row_over_a_frozen_key_counts_once() {
        let frozen: LayeredMap<_, _> = [(1, 10), (2, 20)].into_iter().collect();
        let mut map = frozen.clone();
        map.freeze();
        assert_eq!((map.len(), counted(&map)), (2, 2));
        map.insert(1, 11);
        map.insert(1, 12);
        map.insert(3, 30);
        assert_eq!(
            (map.len(), counted(&map)),
            (3, 3),
            "an overwrite counts once"
        );
        assert_eq!(map.replace(2, 21), Some(20), "the frozen value answers");
        assert_eq!(map.replace(2, 22), Some(21), "then the private one");
        assert_eq!(map.replace(4, 40), None);
        assert_eq!((map.len(), counted(&map)), (4, 4));
        let copy = map.clone();
        assert_eq!(copy.len(), 4, "a clone counts as its source");
        map.clear_local();
        assert_eq!((map.len(), counted(&map)), (2, 2), "the frozen rows stay");
        map.entry(1).or_insert(0);
        *map.entry(2).or_insert(0) += 1;
        map.entry(5).or_insert(50);
        assert_eq!(
            (map.len(), counted(&map)),
            (3, 3),
            "an entry on a frozen key counts once"
        );
        assert_eq!(map.get(&2), Some(&21));
        map.freeze();
        assert_eq!(
            (map.len(), counted(&map)),
            (3, 3),
            "a freeze merges the rows"
        );
        map.insert(1, 13);
        assert_eq!((map.len(), counted(&map)), (3, 3));
        let unlayered: LayeredMap<_, _> = [(1, 1), (2, 2)].into_iter().collect();
        assert_eq!(unlayered.len(), 2);
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

#[cfg(test)]
mod rows_token_tests {
    use super::*;

    fn rows() -> LayeredVec<i32> {
        let mut rows = LayeredVec::over(Arc::new(vec![1, 2]));
        rows.push(3);
        rows
    }

    #[test]
    fn appends_keep_the_token_and_a_clone_shares_it() {
        let mut rows = rows();
        let token = rows.observe_rows();
        assert!(rows.rows_kept_since(&token));
        rows.push(4);
        rows.resize(6, 0);
        let staged = rows.observe_revision();
        rows.append_staged(vec![7], &staged, Revision::default());
        assert!(rows.rows_kept_since(&token), "appends leave every row");
        assert!(rows.observe_rows().same_as(&token));
        let copy = rows.clone();
        assert!(copy.rows_kept_since(&token));
        assert!(!rows.rows_kept_since(&Revision::default()));
    }

    #[test]
    fn a_write_a_truncation_or_a_cut_base_retires_the_token() {
        let mut rows = rows();
        let token = rows.observe_rows();
        let copy = rows.clone();
        let row = &mut rows[2];
        *row += 0;
        assert!(
            !rows.rows_kept_since(&token),
            "a write, even of the same value"
        );
        assert!(copy.rows_kept_since(&token), "the clone's rows are its own");
        assert!(!rows.observe_rows().same_as(&token));

        let mut rows = self::rows();
        let token = rows.observe_rows();
        rows.truncate_tail(2);
        assert!(!rows.rows_kept_since(&token));

        let mut rows = LayeredVec::over(Arc::new(vec![1, 2]));
        let token = rows.observe_rows();
        rows.limit_base(1);
        assert!(!rows.rows_kept_since(&token));

        let mut rows: LayeredVec<i32> = vec![1].into();
        assert!(!rows.rows_kept_since(&Revision::default()));
        let token = rows.observe_rows();
        rows[0] = 2;
        assert!(!rows.rows_kept_since(&token));
    }
}

#[cfg(test)]
mod upper_tests {
    use super::LayeredVec;
    use std::sync::Arc;

    fn rows() -> LayeredVec<i32> {
        let mut rows = LayeredVec::over(Arc::new(vec![1, 2]));
        rows.push(3);
        rows.push(4);
        rows
    }

    #[test]
    fn shared_rows_read_and_count_as_before_and_a_clone_shares_them() {
        let mut rows = rows();
        let before = super::copied_rows();
        rows.share_tail();
        assert_eq!(super::copied_rows(), before, "sharing copies nothing");
        assert_eq!(rows.len(), 4);
        assert_eq!(rows.iter().copied().collect::<Vec<_>>(), [1, 2, 3, 4]);
        assert_eq!((rows[0], rows[2], rows[3]), (1, 3, 4));
        let copy = rows.clone();
        assert_eq!(super::copied_rows(), before, "a clone shares the rows");
        assert!(Arc::ptr_eq(
            copy.upper.as_ref().unwrap(),
            rows.upper.as_ref().unwrap()
        ));
    }

    #[test]
    fn a_write_to_a_shared_row_is_this_vectors_own() {
        let mut rows = rows();
        rows.share_tail();
        let copy = rows.clone();
        rows[2] = 30;
        rows[0] = 10;
        assert_eq!(rows.iter().copied().collect::<Vec<_>>(), [10, 2, 30, 4]);
        assert_eq!(copy.iter().copied().collect::<Vec<_>>(), [1, 2, 3, 4]);
        // Only the base row counts as a frozen row written: the shared
        // rows are the vector's own.
        assert_eq!(rows.written_rows().collect::<Vec<_>>(), [0]);
        assert!(!rows.base_untouched());
        let mut only_shared = LayeredVec::over(Arc::new(vec![1, 2]));
        only_shared.push(3);
        only_shared.share_tail();
        only_shared[2] = 30;
        assert!(only_shared.base_untouched());
        assert_eq!(only_shared.written_rows().count(), 0);
    }

    #[test]
    fn rows_pushed_after_sharing_are_shared_again_with_the_writes_kept() {
        let mut rows = rows();
        rows.share_tail();
        rows[3] = 40;
        rows.push(5);
        assert_eq!(rows.len(), 5);
        rows.share_tail();
        assert_eq!(rows.iter().copied().collect::<Vec<_>>(), [1, 2, 3, 40, 5]);
        assert_eq!(
            rows.written_rows().count(),
            0,
            "the write is in the shared rows now"
        );
        assert_eq!(rows.upper.as_ref().unwrap().len(), 3);
    }

    #[test]
    fn truncating_into_the_shared_rows_takes_them_back_and_freezing_folds_them() {
        let mut rows = rows();
        rows.share_tail();
        rows.push(5);
        assert!(rows.can_truncate_tail(3));
        rows.truncate_tail(3);
        assert!(rows.upper.is_none());
        assert_eq!(rows.iter().copied().collect::<Vec<_>>(), [1, 2, 3]);
        rows.push(6);
        rows.share_tail();
        rows[1] = 20;
        rows.freeze();
        assert!(rows.upper.is_none());
        assert_eq!(rows.base_len(), 4);
        assert_eq!(rows.iter().copied().collect::<Vec<_>>(), [1, 20, 3, 6]);
        assert!(rows.base_untouched());
    }

    #[test]
    fn resizing_and_serializing_see_the_shared_rows() {
        let mut rows = rows();
        rows.share_tail();
        rows.resize(6, 0);
        assert_eq!(rows.iter().copied().collect::<Vec<_>>(), [1, 2, 3, 4, 0, 0]);
        let bytes = serde_json::to_vec(&rows).unwrap();
        assert_eq!(bytes, b"[1,2,3,4,0,0]");
    }
}
