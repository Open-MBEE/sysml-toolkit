//! A specialization graph by id — each element's id to the ids of the
//! elements it specializes — as the implied planners and the materializer
//! read and extend it: a frozen graph shared by every build on a prepared
//! library, the rows a library's own materialized edges change in it, shared
//! the same way, and a build's own rows over both.
use crate::layered::note_copied;
use std::{collections::HashMap, hash::BuildHasherDefault, sync::Arc};
use uuid::Uuid;

/// A hasher for ids: one multiply of an id's two halves folded together.
/// An id's bits are a hash's already (a name-based id's are a digest's, a
/// random one's are random), and a read through the graph's layers hashes
/// its key once per layer, so the hash is kept to the least that spreads
/// them. A key of another length is folded a word at a time. Iteration
/// order of a table hashed this way is unspecified, so nothing may read
/// one.
#[derive(Clone, Copy, Default)]
pub(crate) struct UuidHasher(u64);

impl std::hash::Hasher for UuidHasher {
    #[inline]
    fn finish(&self) -> u64 {
        self.0 ^ (self.0 >> 32)
    }
    #[inline]
    fn write(&mut self, bytes: &[u8]) {
        if let Ok(id) = <&[u8; 16]>::try_from(bytes) {
            let (low, high) = id.split_at(8);
            let low = u64::from_le_bytes(low.try_into().expect("eight bytes"));
            let high = u64::from_le_bytes(high.try_into().expect("eight bytes"));
            self.0 = (self.0 ^ low ^ high.rotate_left(29)).wrapping_mul(0x9e37_79b9_7f4a_7c15);
            return;
        }
        for chunk in bytes.chunks(8) {
            let mut word = [0u8; 8];
            word[..chunk.len()].copy_from_slice(chunk);
            self.0 = (self.0.rotate_left(5) ^ u64::from_le_bytes(word))
                .wrapping_mul(0x9e37_79b9_7f4a_7c15);
        }
    }
}

/// A hash map by id (see [`UuidHasher`]).
pub(crate) type IdMap<K, V> = HashMap<K, V, BuildHasherDefault<UuidHasher>>;

/// A graph's frozen rows, laid out once: every key's targets in one vector,
/// cut by an offset per row, and a table from each key to its row. A row
/// costs the table's entry of a key and a four-byte row number, and its
/// offset, where a table of the rows themselves holds a vector's three
/// words and its allocation for each.
#[derive(Default)]
pub(crate) struct Frozen {
    /// Each key's row.
    rows: IdMap<Uuid, u32>,
    /// Row `k`'s targets are `targets[offsets[k]..offsets[k + 1]]`.
    offsets: Vec<u32>,
    targets: Vec<Uuid>,
}

impl Frozen {
    /// The rows `rows`, each key once; `None` when a key is there twice, or
    /// the rows or their targets are too many to count in thirty-two bits.
    pub(crate) fn from_rows(
        rows: impl ExactSizeIterator<Item = (Uuid, Vec<Uuid>)>,
    ) -> Option<Self> {
        u32::try_from(rows.len()).ok()?;
        let mut index = IdMap::with_capacity_and_hasher(rows.len(), Default::default());
        let mut offsets = Vec::with_capacity(rows.len() + 1);
        let mut targets = Vec::new();
        offsets.push(0);
        for (key, row) in rows {
            let k = u32::try_from(offsets.len() - 1).ok()?;
            if index.insert(key, k).is_some() {
                return None;
            }
            targets.extend(row);
            offsets.push(u32::try_from(targets.len()).ok()?);
        }
        targets.shrink_to_fit();
        Some(Self {
            rows: index,
            offsets,
            targets,
        })
    }
    /// The rows `keys[k]` → the next `lengths[k]` targets, as a snapshot's
    /// columns carry them, the targets kept as they are; `None` when a key
    /// is there twice, the lengths do not cover the targets, or the rows or
    /// their targets are too many to count in thirty-two bits.
    pub(crate) fn from_columns(
        keys: &[Uuid],
        lengths: &[usize],
        targets: Vec<Uuid>,
    ) -> Option<Self> {
        u32::try_from(keys.len()).ok()?;
        if keys.len() != lengths.len() {
            return None;
        }
        let mut index = IdMap::with_capacity_and_hasher(keys.len(), Default::default());
        let mut offsets = Vec::with_capacity(keys.len() + 1);
        let mut at = 0u32;
        offsets.push(at);
        for (k, (&key, &len)) in keys.iter().zip(lengths).enumerate() {
            if index.insert(key, k as u32).is_some() {
                return None;
            }
            at = at.checked_add(u32::try_from(len).ok()?)?;
            offsets.push(at);
        }
        if at as usize != targets.len() {
            return None;
        }
        Some(Self {
            rows: index,
            offsets,
            targets,
        })
    }
    /// Row `k`'s targets.
    #[inline(always)]
    fn row(&self, k: u32) -> &[Uuid] {
        let k = k as usize;
        &self.targets[self.offsets[k] as usize..self.offsets[k + 1] as usize]
    }
    #[inline]
    pub(crate) fn get(&self, key: &Uuid) -> Option<&[Uuid]> {
        self.rows.get(key).map(|&k| self.row(k))
    }
    /// The row number of `key`.
    #[inline(always)]
    fn find(&self, key: &Uuid) -> Option<u32> {
        self.rows.get(key).copied()
    }
    pub(crate) fn len(&self) -> usize {
        self.rows.len()
    }
    /// Every row, in no particular order.
    #[cfg(test)]
    pub(crate) fn iter(&self) -> impl Iterator<Item = (&Uuid, &[Uuid])> {
        self.numbered().map(|(key, _, row)| (key, row))
    }
    /// Every row with its row number, in no particular order.
    fn numbered(&self) -> impl Iterator<Item = (&Uuid, u32, &[Uuid])> {
        self.rows.iter().map(|(key, &k)| (key, k, self.row(k)))
    }
}

/// Rows laid over a frozen graph and shared between the graphs over it: each
/// replaces the frozen row of its key, or adds a key the frozen graph lacks.
/// Made for one frozen graph, and read only over it.
#[derive(Default)]
pub(crate) struct Overlay {
    rows: IdMap<Uuid, Vec<Uuid>>,
    /// A bit per row of the frozen graph, set for each row replaced here: a
    /// read finds its key's frozen row first and looks here only when that
    /// row's bit is set, so a read through the overlay hashes its key once,
    /// as a read of the frozen graph alone does.
    replaced: Box<[u64]>,
    /// Whether a row here holds a key the frozen graph lacks: a read of a
    /// key the frozen graph lacks looks here only then.
    adds: bool,
}

impl Overlay {
    /// The rows `rows` over `frozen`.
    pub(crate) fn new(frozen: &Frozen, rows: IdMap<Uuid, Vec<Uuid>>) -> Self {
        let mut replaced = vec![0u64; frozen.len().div_ceil(64)].into_boxed_slice();
        let mut adds = false;
        for key in rows.keys() {
            match frozen.find(key) {
                Some(k) => replaced[k as usize / 64] |= 1 << (k % 64),
                None => adds = true,
            }
        }
        Self {
            rows,
            replaced,
            adds,
        }
    }
    pub(crate) fn get(&self, key: &Uuid) -> Option<&Vec<Uuid>> {
        self.rows.get(key)
    }
    /// Whether the frozen row `k` is replaced here.
    #[inline(always)]
    fn replaces(&self, k: u32) -> bool {
        self.replaced[k as usize / 64] & (1 << (k % 64)) != 0
    }
}

/// A specialization graph: a build's own rows over the shared rows of an
/// overlay, if any, over a shared frozen graph. A read takes a key's row
/// from the first layer that has one; a write goes to the build's own rows.
#[derive(Default)]
pub(crate) struct IdGraph {
    frozen: Arc<Frozen>,
    over: Option<Arc<Overlay>>,
    local: IdMap<Uuid, Vec<Uuid>>,
}

impl Clone for IdGraph {
    fn clone(&self) -> Self {
        note_copied(self.local.len());
        Self {
            frozen: Arc::clone(&self.frozen),
            over: self.over.clone(),
            local: self.local.clone(),
        }
    }
}

impl IdGraph {
    /// A graph over `over` laid over the frozen graph `frozen`, with no rows
    /// of its own yet.
    pub(crate) fn overlaid(frozen: Arc<Frozen>, over: Arc<Overlay>) -> Self {
        Self {
            frozen,
            over: Some(over),
            ..Self::default()
        }
    }
    /// The row at `key` the shared layers give.
    #[inline(always)]
    fn shared(&self, key: &Uuid) -> Option<&[Uuid]> {
        let Some(over) = &self.over else {
            return self.frozen.get(key);
        };
        match self.frozen.find(key) {
            Some(k) if over.replaces(k) => over.get(key).map(Vec::as_slice),
            Some(k) => Some(self.frozen.row(k)),
            None if over.adds => over.get(key).map(Vec::as_slice),
            None => None,
        }
    }
    #[inline(always)]
    pub(crate) fn get(&self, key: &Uuid) -> Option<&[Uuid]> {
        match self.local.get(key) {
            Some(row) => Some(row),
            None => self.shared(key),
        }
    }
    pub(crate) fn insert(&mut self, key: Uuid, value: Vec<Uuid>) {
        self.local.insert(key, value);
    }
    /// The own row at `key`, to fill in place: a copy of the shared row
    /// there, when the own rows have none and a shared layer has.
    pub(crate) fn entry(&mut self, key: Uuid) -> Entry<'_> {
        if !self.local.contains_key(&key) {
            if let Some(value) = self.shared(&key).map(<[Uuid]>::to_vec) {
                self.local.insert(key, value);
            }
        }
        Entry(self.local.entry(key))
    }
    /// The shared frozen graph, overlaid or not.
    pub(crate) fn frozen_arc(&self) -> &Arc<Frozen> {
        &self.frozen
    }
    /// The own rows: those written over the shared layers.
    pub(crate) fn local_iter(&self) -> impl Iterator<Item = (&Uuid, &Vec<Uuid>)> {
        self.local.iter()
    }
    /// The capacity of the own rows: what dropping this graph frees (the
    /// shared layers are shared).
    pub(crate) fn local_capacity(&self) -> usize {
        self.local.capacity()
    }
    /// Every key's row, each key once: the frozen graph's rows no other
    /// layer replaces, the overlay's no own row replaces, then the own rows.
    pub(crate) fn iter(&self) -> impl Iterator<Item = (&Uuid, &[Uuid])> {
        let over = self.over.as_deref();
        self.frozen
            .numbered()
            .filter(move |(key, k, _)| {
                !self.local.contains_key(key) && over.is_none_or(|over| !over.replaces(*k))
            })
            .map(|(key, _, row)| (key, row))
            .chain(
                over.into_iter()
                    .flat_map(|over| over.rows.iter())
                    .filter(|(k, _)| !self.local.contains_key(k))
                    .map(|(k, v)| (k, v.as_slice())),
            )
            .chain(self.local.iter().map(|(k, v)| (k, v.as_slice())))
    }
    /// Fold every layer into one frozen graph that the graphs cloned from
    /// this one from here on share.
    pub(crate) fn freeze(&mut self) {
        if self.local.is_empty() && self.over.is_none() {
            return;
        }
        note_copied(self.frozen.len());
        let rows: Vec<(Uuid, Vec<Uuid>)> = self.iter().map(|(k, v)| (*k, v.to_vec())).collect();
        self.frozen =
            Arc::new(Frozen::from_rows(rows.into_iter()).expect("a graph's rows lay out"));
        self.over = None;
        self.local = IdMap::default();
    }
    /// A graph of the frozen rows `frozen` alone.
    pub(crate) fn frozen(frozen: Frozen) -> Self {
        Self {
            frozen: Arc::new(frozen),
            ..Self::default()
        }
    }
}

/// An own row's slot, from [`IdGraph::entry`].
pub(crate) struct Entry<'a>(std::collections::hash_map::Entry<'a, Uuid, Vec<Uuid>>);
impl<'a> Entry<'a> {
    pub(crate) fn or_insert_with(self, default: impl FnOnce() -> Vec<Uuid>) -> &'a mut Vec<Uuid> {
        self.0.or_insert_with(default)
    }
    pub(crate) fn or_default(self) -> &'a mut Vec<Uuid> {
        self.0.or_default()
    }
}

impl From<IdMap<Uuid, Vec<Uuid>>> for IdGraph {
    /// A graph of these rows alone, over no shared layer.
    fn from(local: IdMap<Uuid, Vec<Uuid>>) -> Self {
        Self {
            local,
            ..Self::default()
        }
    }
}

impl FromIterator<(Uuid, Vec<Uuid>)> for IdGraph {
    fn from_iter<I: IntoIterator<Item = (Uuid, Vec<Uuid>)>>(iter: I) -> Self {
        Self {
            local: iter.into_iter().collect(),
            ..Self::default()
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn id(n: u128) -> Uuid {
        Uuid::from_u128(n)
    }

    fn rows(pairs: &[(u128, &[u128])]) -> IdMap<Uuid, Vec<Uuid>> {
        pairs
            .iter()
            .map(|&(k, v)| (id(k), v.iter().map(|&n| id(n)).collect()))
            .collect()
    }

    fn sorted(graph: &IdGraph) -> Vec<(Uuid, Vec<Uuid>)> {
        let mut all: Vec<_> = graph.iter().map(|(k, v)| (*k, v.to_vec())).collect();
        all.sort();
        all
    }

    #[test]
    fn a_read_takes_the_row_of_the_first_layer_that_has_one() {
        let frozen = Arc::new(
            Frozen::from_rows(rows(&[(1, &[10]), (2, &[20]), (3, &[30])]).into_iter()).unwrap(),
        );
        let over = Arc::new(Overlay::new(&frozen, rows(&[(2, &[20, 21]), (4, &[40])])));
        let mut graph = IdGraph::overlaid(Arc::clone(&frozen), over);
        assert_eq!(graph.iter().count(), 4);
        graph.insert(id(3), vec![id(31)]);
        graph.entry(id(2)).or_default().push(id(22));
        graph.entry(id(5)).or_default().push(id(50));
        assert_eq!(graph.get(&id(1)), Some(&[id(10)][..]));
        assert_eq!(graph.get(&id(2)), Some(&[id(20), id(21), id(22)][..]));
        assert_eq!(graph.get(&id(3)), Some(&[id(31)][..]));
        assert_eq!(graph.get(&id(4)), Some(&[id(40)][..]));
        assert_eq!(graph.get(&id(6)), None);
        let only_replacing = Overlay::new(&frozen, rows(&[(3, &[32])]));
        assert!(!only_replacing.adds);
        let over_frozen = IdGraph::overlaid(Arc::clone(&frozen), Arc::new(only_replacing));
        assert_eq!(over_frozen.get(&id(3)), Some(&[id(32)][..]));
        assert_eq!(over_frozen.get(&id(1)), Some(&[id(10)][..]));
        assert_eq!(over_frozen.get(&id(4)), None);
        assert_eq!(graph.iter().count(), 5, "each key once");
        assert_eq!(graph.local_iter().count(), 3);
        let expected = sorted(&graph);
        let shared = graph.clone();
        graph.freeze();
        assert_eq!(sorted(&graph), expected);
        assert_eq!(graph.local_iter().count(), 0);
        assert_eq!(sorted(&shared), expected, "a clone keeps its layers");
        assert_eq!(frozen.len(), 3, "the frozen graph is shared, not written");
    }

    #[test]
    fn frozen_rows_answer_each_key() {
        let pairs = vec![
            (id(3), vec![id(30), id(31)]),
            (id(1), vec![]),
            (id(2), vec![id(20)]),
        ];
        let frozen = Frozen::from_rows(pairs.clone().into_iter()).unwrap();
        assert_eq!(frozen.len(), 3);
        for (key, targets) in &pairs {
            assert_eq!(frozen.get(key), Some(targets.as_slice()));
        }
        assert_eq!(frozen.get(&id(4)), None);
        assert_eq!(frozen.iter().count(), 3);
        assert!(Frozen::from_rows(vec![(id(1), vec![]), (id(1), vec![])].into_iter()).is_none());
        assert_eq!(Frozen::default().get(&id(1)), None);
        let columns = Frozen::from_columns(&[id(3), id(1)], &[2, 0], vec![id(30), id(31)]).unwrap();
        assert_eq!(columns.get(&id(3)), Some(&[id(30), id(31)][..]));
        assert_eq!(columns.get(&id(1)), Some(&[][..]));
        assert!(Frozen::from_columns(&[id(1)], &[2], vec![id(30)]).is_none());
        assert!(Frozen::from_columns(&[id(1), id(1)], &[0, 0], vec![]).is_none());
    }
}
