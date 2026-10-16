//! Immutable rows over shared contiguous storage, with row-local copy-on-write.
//! Snapshot tables decode their values in bulk; no pointer fixups or unsafe
//! ownership tricks are needed, and changing one row cannot affect a neighbour.
mod rows;
pub(crate) use rows::{Rows, index_rows};

use serde::{Deserialize, Deserializer, Serialize, Serializer};
use std::{ops::Deref, sync::Arc};

#[derive(Clone, Debug)]
pub(crate) enum Row<T> {
    Owned(Vec<T>),
    Shared {
        values: Arc<Vec<T>>,
        start: usize,
        end: usize,
    },
}
impl<T> Default for Row<T> {
    fn default() -> Self {
        Self::Owned(Vec::new())
    }
}
impl<T> From<Vec<T>> for Row<T> {
    fn from(v: Vec<T>) -> Self {
        Self::Owned(v)
    }
}
impl<T> Deref for Row<T> {
    type Target = [T];
    fn deref(&self) -> &[T] {
        match self {
            Self::Owned(v) => v,
            Self::Shared { values, start, end } => &values[*start..*end],
        }
    }
}
impl<T: Clone> Row<T> {
    pub fn make_mut(&mut self) -> &mut Vec<T> {
        if matches!(self, Self::Shared { .. }) {
            *self = Self::Owned(self.to_vec());
        }
        match self {
            Self::Owned(v) => v,
            _ => unreachable!(),
        }
    }
    pub fn push(&mut self, v: T) {
        self.make_mut().push(v);
    }
}
impl<'a, T> IntoIterator for &'a Row<T> {
    type Item = &'a T;
    type IntoIter = std::slice::Iter<'a, T>;
    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}
impl<T: Clone> IntoIterator for Row<T> {
    type Item = T;
    type IntoIter = std::vec::IntoIter<T>;
    fn into_iter(self) -> Self::IntoIter {
        match self {
            Self::Owned(v) => v,
            other => other.to_vec(),
        }
        .into_iter()
    }
}
impl<T> FromIterator<T> for Row<T> {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        Self::Owned(iter.into_iter().collect())
    }
}
impl<T: PartialEq> PartialEq for Row<T> {
    fn eq(&self, rhs: &Self) -> bool {
        **self == **rhs
    }
}
impl<T: Serialize> Serialize for Row<T> {
    fn serialize<S: Serializer>(&self, s: S) -> Result<S::Ok, S::Error> {
        self.deref().serialize(s)
    }
}
impl<'de, T: Deserialize<'de>> Deserialize<'de> for Row<T> {
    fn deserialize<D: Deserializer<'de>>(d: D) -> Result<Self, D::Error> {
        Vec::deserialize(d).map(Self::Owned)
    }
}

/// Rows over one shared value vector, cut by their lengths: the prefix sums
/// must cover the values exactly.
pub(crate) fn rows_from_lengths<T, E: serde::de::Error>(
    lengths: &[usize],
    values: Vec<T>,
) -> Result<Vec<Row<T>>, E> {
    let mut offsets = Vec::with_capacity(lengths.len() + 1);
    offsets.push(0usize);
    for &length in lengths {
        let end = offsets
            .last()
            .unwrap()
            .checked_add(length)
            .ok_or_else(|| E::custom("flat row length overflow"))?;
        if end > values.len() {
            return Err(E::custom("flat row outside values"));
        }
        offsets.push(end);
    }
    if offsets.last() != Some(&values.len()) {
        return Err(E::custom("invalid flat row offsets"));
    }
    let values = Arc::new(values);
    Ok(offsets
        .windows(2)
        .map(|r| {
            if r[0] == r[1] {
                Row::default()
            } else {
                Row::Shared {
                    values: values.clone(),
                    start: r[0],
                    end: r[1],
                }
            }
        })
        .collect())
}

/// Lists by row over a dense row range, with a presence mark per row:
/// `get(i)` is row `i`'s list, `None` for a row that has none, as against
/// an empty one. Laid out in one pass from lists sorted by row, with one
/// allocation for every list and no table to hash — a snapshot's
/// index-keyed plans are read back this way — and read by index. A row
/// costs four bytes, its rank among the rows with a list, and a list four
/// more, its offset into the one value vector: a table of a few thousand
/// lists over a hundred thousand rows is the size of its values.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct ListsByRow<T> {
    /// Row `i`'s list is list `ranks[i]`; [`NO_LIST`] for a row that has
    /// none. The ranks ascend with the rows, so tables laid out over the
    /// same rows with lists on the same rows rank them the same way and
    /// share one vector ([`Self::share_ranks_with`]).
    ranks: Arc<Vec<u32>>,
    /// List `k` is `values[offsets[k]..offsets[k + 1]]`.
    offsets: Vec<u32>,
    values: Vec<T>,
}

/// The rank of a row without a list.
const NO_LIST: u32 = u32::MAX;

impl<T> Default for ListsByRow<T> {
    fn default() -> Self {
        Self {
            ranks: Arc::default(),
            offsets: vec![0],
            values: Vec::new(),
        }
    }
}
impl<T> ListsByRow<T> {
    /// The lists `keys[k]` → the next `lengths[k]` values, laid out over
    /// `rows` rows: the keys strictly ascending and below the rows, the
    /// lengths covering the values exactly, and the rows and values few
    /// enough to count in thirty-two bits; `None` otherwise.
    pub(crate) fn from_sorted(
        rows: usize,
        keys: &[usize],
        lengths: &[usize],
        values: Vec<T>,
    ) -> Option<Self> {
        if keys.len() != lengths.len() || rows >= NO_LIST as usize {
            return None;
        }
        let count = u32::try_from(values.len()).ok()?;
        let mut ranks = vec![NO_LIST; rows];
        let mut offsets = Vec::with_capacity(keys.len() + 1);
        offsets.push(0u32);
        let (mut at, mut last) = (0u32, None);
        for (k, (&key, &len)) in keys.iter().zip(lengths).enumerate() {
            if key >= rows || last.is_some_and(|last| key <= last) {
                return None;
            }
            at = at.checked_add(u32::try_from(len).ok()?)?;
            if at > count {
                return None;
            }
            offsets.push(at);
            ranks[key] = u32::try_from(k).ok()?;
            last = Some(key);
        }
        if at != count {
            return None;
        }
        Some(Self {
            ranks: Arc::new(ranks),
            offsets,
            values,
        })
    }
    /// The rows laid out over.
    pub(crate) fn rows(&self) -> usize {
        self.ranks.len()
    }
    /// Row `i`'s rank among the rows with a list, when it has one.
    fn rank(&self, i: usize) -> Option<usize> {
        match self.ranks.get(i) {
            Some(&NO_LIST) | None => None,
            Some(&rank) => Some(rank as usize),
        }
    }
    /// Whether row `i` has a list.
    pub(crate) fn contains(&self, i: usize) -> bool {
        self.rank(i).is_some()
    }
    /// Row `i`'s list, when it has one.
    pub(crate) fn get(&self, i: usize) -> Option<&[T]> {
        let k = self.rank(i)?;
        Some(&self.values[self.offsets[k] as usize..self.offsets[k + 1] as usize])
    }
    /// Every row with a list, ascending.
    pub(crate) fn iter(&self) -> impl Iterator<Item = (usize, &[T])> {
        (0..self.rows()).filter_map(move |i| Some((i, self.get(i)?)))
    }
    /// Every list's values, row after row.
    pub(crate) fn values(&self) -> &[T] {
        &self.values
    }
    /// Share `other`'s ranks when they are this table's — the two have
    /// lists on the same rows — so that the two hold one vector of them.
    pub(crate) fn share_ranks_with<U>(&mut self, other: &ListsByRow<U>) {
        if !Arc::ptr_eq(&self.ranks, &other.ranks) && self.ranks == other.ranks {
            self.ranks = Arc::clone(&other.ranks);
        }
    }
}
impl<T: Clone> ListsByRow<T> {
    /// The lists of `map` laid out over `rows` rows; a key past the rows
    /// has no row to lie in and is left out.
    pub(crate) fn from_map(rows: usize, map: &crate::layered::IdMap<usize, Vec<T>>) -> Self {
        let mut keys: Vec<usize> = map.keys().copied().filter(|&k| k < rows).collect();
        debug_assert_eq!(keys.len(), map.len(), "every key lies within the rows");
        keys.sort_unstable();
        let lengths: Vec<usize> = keys.iter().map(|k| map[k].len()).collect();
        let values: Vec<T> = keys.iter().flat_map(|k| map[k].iter().cloned()).collect();
        Self::from_sorted(rows, &keys, &lengths, values)
            .expect("sorted keys within the rows lay out")
    }
    /// The lists as a table by row.
    pub(crate) fn to_map(&self) -> crate::layered::IdMap<usize, Vec<T>> {
        self.iter().map(|(i, list)| (i, list.to_vec())).collect()
    }
    /// The lists `keys[k]` → the next `lengths[k]` values, laid out on
    /// `other`'s rows, sharing its ranks: a row with a list there and no key
    /// here gets an empty list. The keys strictly ascending, each a row with
    /// a list there, and the lengths covering the values; `None` otherwise.
    /// The values stay as they are: the ranks ascend with the rows, so the
    /// lists lie in the keys' order.
    pub(crate) fn from_sorted_on<U>(
        other: &ListsByRow<U>,
        keys: &[usize],
        lengths: &[usize],
        values: Vec<T>,
    ) -> Option<Self> {
        if keys.len() != lengths.len() || keys.windows(2).any(|pair| pair[0] >= pair[1]) {
            return None;
        }
        let lists = other.offsets.len() - 1;
        let mut sizes = vec![0u32; lists];
        for (&key, &len) in keys.iter().zip(lengths) {
            sizes[other.rank(key)?] = u32::try_from(len).ok()?;
        }
        let mut offsets = Vec::with_capacity(lists + 1);
        let mut at = 0u32;
        offsets.push(at);
        for size in sizes {
            at = at.checked_add(size)?;
            offsets.push(at);
        }
        if at as usize != values.len() {
            return None;
        }
        Some(Self {
            ranks: Arc::clone(&other.ranks),
            offsets,
            values,
        })
    }
    /// These lists laid out on `other`'s rows, sharing its ranks: a row with
    /// a list there and none here gets an empty one. `None` when a row with
    /// a list here has none there.
    pub(crate) fn laid_on<U>(&self, other: &ListsByRow<U>) -> Option<Self> {
        if self.iter().any(|(i, _)| !other.contains(i)) {
            return None;
        }
        let mut offsets = Vec::with_capacity(other.offsets.len());
        let mut values = Vec::with_capacity(self.values.len());
        offsets.push(0u32);
        for (i, _) in other.iter() {
            values.extend_from_slice(self.get(i).unwrap_or_default());
            offsets.push(u32::try_from(values.len()).ok()?);
        }
        Some(Self {
            ranks: Arc::clone(&other.ranks),
            offsets,
            values,
        })
    }
}

/// [`table`] for rows of indices: both columns as [`crate::bulk::Ints`].
pub(crate) mod index_table {
    use super::*;
    use crate::bulk::Ints;
    pub fn serialize<S: Serializer>(rows: &[Row<usize>], s: S) -> Result<S::Ok, S::Error> {
        let lengths = Ints(rows.iter().map(|r| r.len()).collect());
        let values = Ints(rows.iter().flat_map(|r| r.iter().copied()).collect());
        (lengths, values).serialize(s)
    }
    pub fn deserialize<'de, D: Deserializer<'de>>(d: D) -> Result<Vec<Row<usize>>, D::Error> {
        let (Ints(lengths), Ints(values)): (Ints, Ints) = Deserialize::deserialize(d)?;
        rows_from_lengths(&lengths, values)
    }
}

/// Two contiguous vectors: row lengths and values. Checked prefix sums form
/// offsets with exact coverage of the values vector before rows are exposed.
pub(crate) mod table {
    use super::*;
    #[cfg(test)]
    pub fn serialize<T: Serialize, S: Serializer>(
        rows: &[Row<T>],
        s: S,
    ) -> Result<S::Ok, S::Error> {
        Slices(rows.iter().map(|r| &**r).collect()).serialize(s)
    }
    pub fn deserialize<'de, T: Deserialize<'de>, D: Deserializer<'de>>(
        d: D,
    ) -> Result<Vec<Row<T>>, D::Error> {
        let (lengths, values): (Vec<usize>, Vec<T>) = Deserialize::deserialize(d)?;
        rows_from_lengths(&lengths, values)
    }
}

pub(crate) struct Slices<'a, T>(pub Vec<&'a [T]>);
impl<T: Serialize> Serialize for Slices<'_, T> {
    fn serialize<S: Serializer>(&self, s: S) -> Result<S::Ok, S::Error> {
        use serde::ser::{SerializeSeq, SerializeTuple};
        let lengths: Vec<_> = self.0.iter().map(|r| r.len()).collect();
        let count = lengths
            .iter()
            .try_fold(0usize, |n, &length| n.checked_add(length))
            .ok_or_else(|| serde::ser::Error::custom("flat table length overflow"))?;
        struct Values<'a, T>(&'a [&'a [T]], usize);
        impl<T: Serialize> Serialize for Values<'_, T> {
            fn serialize<S: Serializer>(&self, s: S) -> Result<S::Ok, S::Error> {
                let mut seq = s.serialize_seq(Some(self.1))?;
                for value in self.0.iter().flat_map(|r| r.iter()) {
                    seq.serialize_element(value)?;
                }
                seq.end()
            }
        }
        let mut tuple = s.serialize_tuple(2)?;
        tuple.serialize_element(&lengths)?;
        tuple.serialize_element(&Values(&self.0, count))?;
        tuple.end()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::cache_codec;
    #[test]
    fn lists_by_row_answer_each_row_and_share_ranks_over_the_same_rows() {
        let lists = ListsByRow::from_sorted(6, &[1, 4], &[2, 0], vec![7usize, 8]).unwrap();
        assert_eq!(lists.rows(), 6);
        assert_eq!(lists.get(1), Some(&[7usize, 8][..]));
        assert_eq!(lists.get(4), Some(&[][..]));
        assert!(!lists.contains(0) && !lists.contains(5) && !lists.contains(6));
        assert_eq!(
            lists.iter().map(|(i, l)| (i, l.len())).collect::<Vec<_>>(),
            [(1, 2), (4, 0)]
        );
        let mut other = ListsByRow::from_sorted(6, &[1, 4], &[1, 1], vec!['a', 'b']).unwrap();
        other.share_ranks_with(&lists);
        assert!(Arc::ptr_eq(&other.ranks, &lists.ranks));
        let mut elsewhere = ListsByRow::from_sorted(6, &[1, 5], &[1, 1], vec!['a', 'b']).unwrap();
        elsewhere.share_ranks_with(&lists);
        assert!(!Arc::ptr_eq(&elsewhere.ranks, &lists.ranks));
        assert_eq!(elsewhere.get(5), Some(&['b'][..]));
        // a key past the rows, out of order, or lengths not covering the values
        assert!(ListsByRow::from_sorted(6, &[6], &[0], Vec::<u8>::new()).is_none());
        assert!(ListsByRow::from_sorted(6, &[4, 1], &[0, 0], Vec::<u8>::new()).is_none());
        assert!(ListsByRow::from_sorted(6, &[1], &[1], Vec::<u8>::new()).is_none());
        assert!(ListsByRow::from_sorted(6, &[1], &[0], vec![1u8]).is_none());
        assert_eq!(ListsByRow::<u8>::default().rows(), 0);
    }
    #[test]
    fn lists_laid_on_another_tables_rows_share_its_ranks() {
        let wide = ListsByRow::from_sorted(6, &[1, 3, 4], &[1, 1, 1], vec![7usize, 8, 9]).unwrap();
        let narrow = ListsByRow::from_sorted(6, &[3], &[2], vec!['a', 'b']).unwrap();
        let laid = narrow.laid_on(&wide).unwrap();
        assert!(Arc::ptr_eq(&laid.ranks, &wide.ranks));
        assert_eq!(laid.get(3), Some(&['a', 'b'][..]));
        assert_eq!(
            laid.get(1),
            Some(&[][..]),
            "a row of the other's gets an empty list"
        );
        assert_eq!(laid.get(2), None);
        assert_eq!(laid.values(), &['a', 'b']);
        let direct = ListsByRow::from_sorted_on(&wide, &[3], &[2], vec!['a', 'b']).unwrap();
        assert_eq!(direct, laid);
        assert!(ListsByRow::from_sorted_on(&wide, &[2], &[1], vec!['c']).is_none());
        assert!(ListsByRow::from_sorted_on(&wide, &[3, 1], &[0, 0], Vec::<char>::new()).is_none());
        assert!(ListsByRow::from_sorted_on(&wide, &[3], &[1], vec!['a', 'b']).is_none());
        let elsewhere = ListsByRow::from_sorted(6, &[2], &[1], vec!['c']).unwrap();
        assert!(
            elsewhere.laid_on(&wide).is_none(),
            "a row the other has no list on"
        );
    }
    #[derive(Serialize, Deserialize)]
    struct Table(#[serde(with = "table")] Vec<Row<u32>>);
    #[test]
    fn decoded_rows_share_storage_and_mutations_are_isolated() {
        let original = Table(vec![vec![1, 2].into(), vec![3].into(), Row::default()]);
        let bytes = cache_codec::encode(&original).unwrap();
        let mut decoded: Table = cache_codec::decode(&bytes).unwrap();
        let (Row::Shared { values: a, .. }, Row::Shared { values: b, .. }) =
            (&decoded.0[0], &decoded.0[1])
        else {
            panic!("rows must decode in bulk")
        };
        assert!(Arc::ptr_eq(a, b));
        let retained = decoded.0[0].clone();
        decoded.0[0].make_mut()[0] = 9;
        decoded.0[1].push(4);
        assert_eq!(&*retained, &[1, 2]);
        assert_eq!(&*decoded.0[0], &[9, 2]);
        assert_eq!(&*decoded.0[1], &[3, 4]);
        assert!(decoded.0[2].is_empty());
        for cut in 0..bytes.len() {
            assert!(cache_codec::decode::<Table>(&bytes[..cut]).is_err());
        }
    }
    #[test]
    fn invalid_offsets_cannot_create_out_of_bounds_rows() {
        for offsets in [vec![], vec![1], vec![3], vec![1, 2], vec![usize::MAX, 2]] {
            let bytes = cache_codec::encode(&((offsets, vec![1u32, 2]),)).unwrap();
            assert!(cache_codec::decode::<Table>(&bytes).is_err());
        }
        let empty = Table(Vec::new());
        let restored: Table = cache_codec::decode(&cache_codec::encode(&empty).unwrap()).unwrap();
        assert!(restored.0.is_empty());
    }
}

#[cfg(test)]
mod lists_by_row_tests {
    use super::ListsByRow;

    #[test]
    fn lists_lay_out_by_row_and_read_by_index() {
        let lists = ListsByRow::from_sorted(5, &[1, 3], &[2, 0], vec![10, 11]).unwrap();
        assert_eq!(lists.rows(), 5);
        assert_eq!(lists.get(0), None);
        assert_eq!(lists.get(1), Some(&[10, 11][..]));
        assert_eq!(lists.get(3), Some(&[][..]), "an empty list is present");
        assert!(lists.contains(3) && !lists.contains(4) && !lists.contains(9));
        assert_eq!(lists.get(9), None, "past the rows");
        assert_eq!(
            lists.iter().collect::<Vec<_>>(),
            vec![(1, &[10, 11][..]), (3, &[][..])]
        );
        assert_eq!(lists.values(), &[10, 11]);
        assert_eq!(ListsByRow::from_map(5, &lists.to_map()), lists);
        let none = ListsByRow::<usize>::from_sorted(0, &[], &[], Vec::new()).unwrap();
        assert_eq!(none.rows(), 0);
        assert_eq!(none, ListsByRow::default());
    }

    #[test]
    fn lists_that_do_not_lay_out_are_refused() {
        let refused = |rows, keys: &[usize], lengths: &[usize], values: Vec<usize>| {
            ListsByRow::from_sorted(rows, keys, lengths, values).is_none()
        };
        assert!(refused(5, &[3, 1], &[1, 1], vec![1, 2]), "keys descending");
        assert!(refused(5, &[1, 1], &[1, 1], vec![1, 2]), "a key twice");
        assert!(refused(5, &[5], &[1], vec![1]), "a key past the rows");
        assert!(refused(5, &[1], &[2], vec![1]), "lengths past the values");
        assert!(
            refused(5, &[1], &[1], vec![1, 2]),
            "values past the lengths"
        );
        assert!(refused(5, &[1, 2], &[1], vec![1]), "a length short");
        assert!(
            refused(5, &[1], &[usize::MAX], vec![1]),
            "a length overflowing"
        );
    }
}
