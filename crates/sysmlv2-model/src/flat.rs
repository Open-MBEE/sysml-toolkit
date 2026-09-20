//! Immutable rows over shared contiguous storage, with row-local copy-on-write.
//! Snapshot tables decode their values in bulk; no pointer fixups or unsafe
//! ownership tricks are needed, and changing one row cannot affect a neighbour.
mod rows;
pub(crate) use rows::Rows;

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
        let mut offsets = Vec::with_capacity(lengths.len() + 1);
        offsets.push(0usize);
        for length in lengths {
            let end = offsets
                .last()
                .unwrap()
                .checked_add(length)
                .ok_or_else(|| serde::de::Error::custom("flat row length overflow"))?;
            if end > values.len() {
                return Err(serde::de::Error::custom("flat row outside values"));
            }
            offsets.push(end);
        }
        if offsets.first() != Some(&0)
            || offsets.last() != Some(&values.len())
            || offsets.windows(2).any(|r| r[0] > r[1])
        {
            return Err(serde::de::Error::custom("invalid flat row offsets"));
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
}

/// A serialization-only view; values are borrowed without cloning the graph.
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
