//! Checked adjacency rows over one shared offsets/value table. Only private
//! edits allocate rows; replay does not reconstruct a handle for every row.
use super::Slices;
use serde::{Deserialize, Deserializer, Serialize, Serializer};
use std::{ops::Index, sync::Arc};

#[derive(Clone)]
pub(crate) struct Rows<T> {
    base: Arc<Table<T>>,
    // Box the few edited row headers to keep the dense directory one pointer
    // per library row, rather than three words per row for an inline Vec.
    #[allow(clippy::box_collection)]
    edits: Vec<Option<Box<Vec<T>>>>,
    tail: Vec<Vec<T>>,
}
struct Table<T> {
    offsets: Vec<usize>,
    values: Vec<T>,
}
impl<T> Default for Rows<T> {
    fn default() -> Self {
        Self {
            base: Arc::new(Table {
                offsets: vec![0],
                values: Vec::new(),
            }),
            edits: Vec::new(),
            tail: Vec::new(),
        }
    }
}
impl<T> Rows<T> {
    fn base_len(&self) -> usize {
        self.base.offsets.len() - 1
    }
    pub fn len(&self) -> usize {
        self.base_len() + self.tail.len()
    }
    pub fn iter(&self) -> impl Iterator<Item = &[T]> {
        self.base
            .offsets
            .windows(2)
            .enumerate()
            .map(|(i, range)| {
                self.edits
                    .get(i)
                    .and_then(Option::as_deref)
                    .map(Vec::as_slice)
                    .unwrap_or_else(|| &self.base.values[range[0]..range[1]])
            })
            .chain(self.tail.iter().map(Vec::as_slice))
    }
    pub fn push(&mut self, row: Vec<T>) {
        self.tail.push(row);
    }
    pub fn resize(&mut self, len: usize) {
        assert!(len >= self.len(), "adjacency rows only grow");
        self.tail.resize_with(len - self.base_len(), Vec::new);
    }
    pub fn set(&mut self, i: usize, row: Vec<T>) {
        if i < self.base_len() {
            if self.edits.is_empty() {
                self.edits.resize_with(self.base_len(), || None);
            }
            self.edits[i] = Some(Box::new(row));
        } else {
            let j = i - self.base_len();
            self.tail[j] = row;
        }
    }
}
impl<T: Clone> Rows<T> {
    pub fn row_mut(&mut self, i: usize) -> &mut Vec<T> {
        if i < self.base_len() {
            if self.edits.is_empty() {
                self.edits.resize_with(self.base_len(), || None);
            }
            self.edits[i].get_or_insert_with(|| {
                Box::new(self.base.values[self.base.offsets[i]..self.base.offsets[i + 1]].to_vec())
            })
        } else {
            let j = i - self.base_len();
            &mut self.tail[j]
        }
    }
    pub fn freeze(&mut self) {
        if self.edits.is_empty() && self.tail.is_empty() {
            return;
        }
        let mut offsets = Vec::with_capacity(self.len() + 1);
        let mut values = Vec::new();
        offsets.push(0);
        for row in self.iter() {
            values.extend_from_slice(row);
            offsets.push(values.len());
        }
        self.base = Arc::new(Table { offsets, values });
        self.edits = Vec::new();
        self.tail = Vec::new();
    }
}
impl<T> Index<usize> for Rows<T> {
    type Output = [T];
    fn index(&self, i: usize) -> &[T] {
        if i >= self.base_len() {
            return &self.tail[i - self.base_len()];
        }
        if let Some(row) = self.edits.get(i).and_then(Option::as_deref) {
            return row;
        }
        &self.base.values[self.base.offsets[i]..self.base.offsets[i + 1]]
    }
}
impl<T: Serialize> Serialize for Rows<T> {
    fn serialize<S: Serializer>(&self, s: S) -> Result<S::Ok, S::Error> {
        Slices(self.iter().collect()).serialize(s)
    }
}
impl<'de, T: Deserialize<'de>> Deserialize<'de> for Rows<T> {
    fn deserialize<D: Deserializer<'de>>(d: D) -> Result<Self, D::Error> {
        let (lengths, values): (Vec<usize>, Vec<T>) = Deserialize::deserialize(d)?;
        let mut offsets = Vec::with_capacity(lengths.len() + 1);
        offsets.push(0usize);
        for length in lengths {
            let end = offsets
                .last()
                .unwrap()
                .checked_add(length)
                .ok_or_else(|| serde::de::Error::custom("adjacency row length overflow"))?;
            if end > values.len() {
                return Err(serde::de::Error::custom("adjacency row outside values"));
            }
            offsets.push(end);
        }
        if offsets.last() != Some(&values.len()) {
            return Err(serde::de::Error::custom("unused adjacency values"));
        }
        Ok(Self {
            base: Arc::new(Table { offsets, values }),
            edits: Vec::new(),
            tail: Vec::new(),
        })
    }
}
#[cfg(test)]
mod tests {
    use super::*;
    use crate::cache_codec;
    #[test]
    fn replay_edits_and_refreeze_preserve_order_and_isolation() {
        let mut rows = Rows::default();
        rows.push(vec![1u32, 2]);
        rows.push(vec![]);
        rows.push(vec![3]);
        let bytes = cache_codec::encode(&rows).unwrap();
        let mut replay: Rows<u32> = cache_codec::decode(&bytes).unwrap();
        assert!(replay.tail.is_empty());
        assert!(replay.edits.is_empty());
        let retained = replay.clone();
        assert!(Arc::ptr_eq(&replay.base, &retained.base));
        replay.row_mut(0).push(4);
        replay.set(1, vec![5]);
        replay.resize(5);
        replay.row_mut(3).push(6);
        replay.set(4, vec![7]);
        let expected = vec![vec![1, 2, 4], vec![5], vec![3], vec![6], vec![7]];
        assert_eq!(
            replay.iter().map(<[_]>::to_vec).collect::<Vec<_>>(),
            expected
        );
        assert_eq!(&retained[0], &[1, 2]);
        assert!(retained[1].is_empty());
        let edited: Rows<u32> =
            cache_codec::decode(&cache_codec::encode(&replay).unwrap()).unwrap();
        replay.freeze();
        assert_eq!(
            replay.iter().collect::<Vec<_>>(),
            edited.iter().collect::<Vec<_>>()
        );
        assert!(replay.tail.is_empty());
        assert!(replay.edits.is_empty());
        let base = replay.base.clone();
        replay.freeze();
        assert!(Arc::ptr_eq(&base, &replay.base));
        for cut in 0..bytes.len() {
            assert!(cache_codec::decode::<Rows<u32>>(&bytes[..cut]).is_err());
        }
    }
    #[test]
    fn malformed_lengths_reject_overflow_gaps_and_out_of_bounds() {
        for lengths in [vec![], vec![1], vec![3], vec![1, 2], vec![1, usize::MAX]] {
            let bytes = cache_codec::encode(&(lengths, vec![1u32, 2])).unwrap();
            assert!(cache_codec::decode::<Rows<u32>>(&bytes).is_err());
        }
        let rows: Rows<u32> = cache_codec::decode(
            &cache_codec::encode(&(vec![0usize; 3], Vec::<u32>::new())).unwrap(),
        )
        .unwrap();
        assert_eq!(rows.len(), 3);
        assert!(rows.iter().all(<[_]>::is_empty));
        let empty: Rows<u32> =
            cache_codec::decode(&cache_codec::encode(&Rows::<u32>::default()).unwrap()).unwrap();
        assert_eq!(empty.len(), 0);
    }
}
