//! Bulk columns: a run of fixed-width values the snapshot carries as one
//! byte record, so a decode is one read and a widening loop instead of a
//! tagged varint and a visitor call per value.
use serde::{Deserialize, Deserializer, Serialize, Serializer, de};
use uuid::Uuid;

/// Unsigned integers at the width of the largest: a width byte (1, 2, 4
/// or 8), then every value little-endian at that width.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct Ints(pub Vec<usize>);

/// [`Ints`] for sixty-four-bit words (the property flag sets).
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct Words(pub Vec<u64>);

/// Identifiers as their sixteen bytes each.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct Ids(pub Vec<Uuid>);

/// Bytes as they are: a kind or a flag per row.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct Bytes(pub Vec<u8>);

fn width(max: u64) -> usize {
    match max {
        0..=0xFF => 1,
        0x100..=0xFFFF => 2,
        0x1_0000..=0xFFFF_FFFF => 4,
        _ => 8,
    }
}

fn pack(values: &[u64]) -> Vec<u8> {
    let w = width(values.iter().copied().max().unwrap_or(0));
    let mut out = Vec::with_capacity(1 + values.len() * w);
    out.push(w as u8);
    for v in values {
        out.extend_from_slice(&v.to_le_bytes()[..w]);
    }
    out
}

/// The column's values widened into `T` in one pass over the bytes, a
/// loop per width so each is a plain widening the compiler can vectorize;
/// `from` refuses a value the target cannot hold.
fn unpack<T, E: de::Error>(bytes: &[u8], from: impl Fn(u64) -> Option<T>) -> Result<Vec<T>, E> {
    let Some((&w, rest)) = bytes.split_first() else {
        return Err(E::custom("an integer column has no width"));
    };
    let w = w as usize;
    if !matches!(w, 1 | 2 | 4 | 8) || !rest.len().is_multiple_of(w) {
        return Err(E::custom("malformed integer column"));
    }
    let too_wide = || E::custom("an integer column exceeds this target's integers");
    let mut out = Vec::with_capacity(rest.len() / w);
    match w {
        1 => {
            for &b in rest {
                out.push(from(u64::from(b)).ok_or_else(too_wide)?);
            }
        }
        2 => {
            for c in rest.as_chunks::<2>().0 {
                out.push(from(u64::from(u16::from_le_bytes(*c))).ok_or_else(too_wide)?);
            }
        }
        4 => {
            for c in rest.as_chunks::<4>().0 {
                out.push(from(u64::from(u32::from_le_bytes(*c))).ok_or_else(too_wide)?);
            }
        }
        _ => {
            for c in rest.as_chunks::<8>().0 {
                out.push(from(u64::from_le_bytes(*c)).ok_or_else(too_wide)?);
            }
        }
    }
    Ok(out)
}

struct Blob<F>(F);
impl<'de, T, F: FnOnce(&[u8]) -> Result<T, String>> de::Visitor<'de> for Blob<F> {
    type Value = T;
    fn expecting(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        f.write_str("a byte column")
    }
    fn visit_bytes<E: de::Error>(self, v: &[u8]) -> Result<T, E> {
        (self.0)(v).map_err(E::custom)
    }
}

impl Serialize for Ints {
    fn serialize<S: Serializer>(&self, s: S) -> Result<S::Ok, S::Error> {
        let words: Vec<u64> = self.0.iter().map(|&v| v as u64).collect();
        s.serialize_bytes(&pack(&words))
    }
}
impl<'de> Deserialize<'de> for Ints {
    fn deserialize<D: Deserializer<'de>>(d: D) -> Result<Self, D::Error> {
        d.deserialize_bytes(Blob(|bytes: &[u8]| {
            unpack::<usize, D::Error>(bytes, |v| usize::try_from(v).ok())
                .map(Ints)
                .map_err(|e| e.to_string())
        }))
    }
}
impl Serialize for Words {
    fn serialize<S: Serializer>(&self, s: S) -> Result<S::Ok, S::Error> {
        s.serialize_bytes(&pack(&self.0))
    }
}
impl<'de> Deserialize<'de> for Words {
    fn deserialize<D: Deserializer<'de>>(d: D) -> Result<Self, D::Error> {
        d.deserialize_bytes(Blob(|bytes: &[u8]| {
            unpack::<u64, D::Error>(bytes, Some)
                .map(Words)
                .map_err(|e| e.to_string())
        }))
    }
}
impl Serialize for Ids {
    fn serialize<S: Serializer>(&self, s: S) -> Result<S::Ok, S::Error> {
        let mut out = Vec::with_capacity(self.0.len() * 16);
        for id in &self.0 {
            out.extend_from_slice(id.as_bytes());
        }
        s.serialize_bytes(&out)
    }
}
impl<'de> Deserialize<'de> for Ids {
    fn deserialize<D: Deserializer<'de>>(d: D) -> Result<Self, D::Error> {
        d.deserialize_bytes(Blob(|bytes: &[u8]| {
            if !bytes.len().is_multiple_of(16) {
                return Err("malformed identifier column".to_string());
            }
            Ok(Ids(bytes
                .as_chunks::<16>()
                .0
                .iter()
                .map(|c| Uuid::from_bytes(*c))
                .collect()))
        }))
    }
}
impl Serialize for Bytes {
    fn serialize<S: Serializer>(&self, s: S) -> Result<S::Ok, S::Error> {
        s.serialize_bytes(&self.0)
    }
}
impl<'de> Deserialize<'de> for Bytes {
    fn deserialize<D: Deserializer<'de>>(d: D) -> Result<Self, D::Error> {
        d.deserialize_bytes(Blob(|bytes: &[u8]| Ok(Bytes(bytes.to_vec()))))
    }
}

/// Index-keyed lists of indices as three columns: the keys, each list's
/// length, the values.
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct IndexLists {
    keys: Ints,
    lengths: Ints,
    values: Ints,
}
impl From<Vec<(usize, Vec<usize>)>> for IndexLists {
    fn from(lists: Vec<(usize, Vec<usize>)>) -> Self {
        Self {
            keys: Ints(lists.iter().map(|l| l.0).collect()),
            lengths: Ints(lists.iter().map(|l| l.1.len()).collect()),
            values: Ints(lists.into_iter().flat_map(|l| l.1).collect()),
        }
    }
}
impl IndexLists {
    /// The lists back; `None` when the lengths do not cover the values.
    pub(crate) fn into_lists(self) -> Option<Vec<(usize, Vec<usize>)>> {
        split_lists(self.keys.0, &self.lengths.0, self.values.0)
    }
    /// The keys, as written.
    pub(crate) fn keys(&self) -> &[usize] {
        &self.keys.0
    }
    /// The lists laid out by row over `rows` rows, in one pass (see
    /// [`crate::flat::ListsByRow::from_sorted`]); `None` when the keys are
    /// not ascending below the rows or the lengths do not cover the values.
    pub(crate) fn into_rows(self, rows: usize) -> Option<crate::flat::ListsByRow<usize>> {
        crate::flat::ListsByRow::from_sorted(rows, &self.keys.0, &self.lengths.0, self.values.0)
    }
}
impl From<&crate::flat::ListsByRow<usize>> for IndexLists {
    fn from(lists: &crate::flat::ListsByRow<usize>) -> Self {
        Self {
            keys: Ints(lists.iter().map(|(k, _)| k).collect()),
            lengths: Ints(lists.iter().map(|(_, l)| l.len()).collect()),
            values: Ints(lists.values().to_vec()),
        }
    }
}
/// The three columns as they are: the keys, the lengths and the values;
/// `None` when the lengths do not cover the values.
fn checked_columns<K, V>(
    keys: Vec<K>,
    lengths: Vec<usize>,
    values: Vec<V>,
) -> Option<(Vec<K>, Vec<usize>, Vec<V>)> {
    (keys.len() == lengths.len()
        && lengths.iter().try_fold(0usize, |n, &l| n.checked_add(l))? == values.len())
    .then_some((keys, lengths, values))
}
fn split_lists<K, V>(keys: Vec<K>, lengths: &[usize], values: Vec<V>) -> Option<Vec<(K, Vec<V>)>> {
    if keys.len() != lengths.len()
        || lengths.iter().try_fold(0usize, |n, &l| n.checked_add(l))? != values.len()
    {
        return None;
    }
    let mut values = values.into_iter();
    Some(
        keys.into_iter()
            .zip(lengths)
            .map(|(k, &len)| (k, values.by_ref().take(len).collect()))
            .collect(),
    )
}

/// Id-keyed lists of ids as three columns.
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct IdLists {
    keys: Ids,
    lengths: Ints,
    values: Ids,
}
impl From<Vec<(Uuid, Vec<Uuid>)>> for IdLists {
    fn from(lists: Vec<(Uuid, Vec<Uuid>)>) -> Self {
        Self {
            keys: Ids(lists.iter().map(|l| l.0).collect()),
            lengths: Ints(lists.iter().map(|l| l.1.len()).collect()),
            values: Ids(lists.into_iter().flat_map(|l| l.1).collect()),
        }
    }
}
impl IdLists {
    /// The lists back; `None` when the lengths do not cover the values.
    #[cfg(test)]
    pub(crate) fn into_lists(self) -> Option<Vec<(Uuid, Vec<Uuid>)>> {
        split_lists(self.keys.0, &self.lengths.0, self.values.0)
    }
    /// The columns as they are — the keys, each list's length, every list's
    /// values in turn — without a vector per list; `None` when the lengths
    /// do not cover the values.
    pub(crate) fn into_columns(self) -> Option<(Vec<Uuid>, Vec<usize>, Vec<Uuid>)> {
        checked_columns(self.keys.0, self.lengths.0, self.values.0)
    }
}

/// Index-keyed lists of ids as three columns.
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct IndexIdLists {
    keys: Ints,
    lengths: Ints,
    values: Ids,
}
impl From<Vec<(usize, Vec<Uuid>)>> for IndexIdLists {
    fn from(lists: Vec<(usize, Vec<Uuid>)>) -> Self {
        Self {
            keys: Ints(lists.iter().map(|l| l.0).collect()),
            lengths: Ints(lists.iter().map(|l| l.1.len()).collect()),
            values: Ids(lists.into_iter().flat_map(|l| l.1).collect()),
        }
    }
}
impl IndexIdLists {
    /// The lists back; `None` when the lengths do not cover the values.
    #[cfg(test)]
    pub(crate) fn into_lists(self) -> Option<Vec<(usize, Vec<Uuid>)>> {
        split_lists(self.keys.0, &self.lengths.0, self.values.0)
    }
    /// The columns as they are (see [`IdLists::into_columns`]).
    pub(crate) fn into_columns(self) -> Option<(Vec<usize>, Vec<usize>, Vec<Uuid>)> {
        checked_columns(self.keys.0, self.lengths.0, self.values.0)
    }
}

/// Pairs of indices as two columns.
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct Pairs {
    first: Ints,
    second: Ints,
}
impl From<Vec<(usize, usize)>> for Pairs {
    fn from(pairs: Vec<(usize, usize)>) -> Self {
        Self {
            first: Ints(pairs.iter().map(|p| p.0).collect()),
            second: Ints(pairs.iter().map(|p| p.1).collect()),
        }
    }
}
impl Pairs {
    /// The pairs back; `None` for columns of unequal length.
    pub(crate) fn into_pairs(self) -> Option<Vec<(usize, usize)>> {
        if self.first.0.len() != self.second.0.len() {
            return None;
        }
        Some(self.first.0.into_iter().zip(self.second.0).collect())
    }
}

/// Truth values as a byte each.
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct Flags(Bytes);
impl From<Vec<bool>> for Flags {
    fn from(flags: Vec<bool>) -> Self {
        Self(Bytes(flags.into_iter().map(u8::from).collect()))
    }
}
impl Flags {
    /// The truth values back; `None` for a byte that is neither 0 nor 1.
    pub(crate) fn into_flags(self) -> Option<Vec<bool>> {
        if self.0.0.iter().any(|&b| b > 1) {
            return None;
        }
        Some(self.0.0.into_iter().map(|b| b == 1).collect())
    }
}

/// A vector of optional indices as one column: the vector's length stands
/// for `None`, since an index is always below it.
pub(crate) mod opt_index_vec {
    use super::*;
    use crate::layered::LayeredVec;
    pub fn serialize<S: Serializer>(
        v: &LayeredVec<Option<usize>>,
        s: S,
    ) -> Result<S::Ok, S::Error> {
        let n = v.len();
        let values = v
            .iter()
            .map(|o| match o {
                Some(i) if *i >= n => Err(serde::ser::Error::custom("an index past its rows")),
                Some(i) => Ok(*i),
                None => Ok(n),
            })
            .collect::<Result<Vec<_>, S::Error>>()?;
        Ints(values).serialize(s)
    }
    pub fn deserialize<'de, D: Deserializer<'de>>(
        d: D,
    ) -> Result<LayeredVec<Option<usize>>, D::Error> {
        let Ints(values) = Ints::deserialize(d)?;
        let n = values.len();
        if values.iter().any(|&v| v > n) {
            return Err(de::Error::custom(
                "an optional index column points past its rows",
            ));
        }
        Ok(values
            .into_iter()
            .map(|v| (v < n).then_some(v))
            .collect::<Vec<_>>()
            .into())
    }
}

/// An index-keyed map of indices as two columns, keys ascending.
pub(crate) mod index_map {
    use super::*;
    use crate::layered::LayeredMap;
    pub fn serialize<S: Serializer>(m: &LayeredMap<usize, usize>, s: S) -> Result<S::Ok, S::Error> {
        let mut pairs: Vec<(usize, usize)> = m.iter().map(|(&k, &v)| (k, v)).collect();
        pairs.sort_unstable();
        let keys = Ints(pairs.iter().map(|p| p.0).collect());
        let values = Ints(pairs.iter().map(|p| p.1).collect());
        (keys, values).serialize(s)
    }
    pub fn deserialize<'de, D: Deserializer<'de>>(
        d: D,
    ) -> Result<LayeredMap<usize, usize>, D::Error> {
        let (Ints(keys), Ints(values)): (Ints, Ints) = Deserialize::deserialize(d)?;
        if keys.len() != values.len() || keys.windows(2).any(|w| w[0] >= w[1]) {
            return Err(de::Error::custom("malformed index map"));
        }
        Ok(keys.into_iter().zip(values).collect())
    }
}

/// A set of indices as one ascending column.
pub(crate) mod index_set {
    use super::*;
    use crate::layered::IdSet;
    pub fn serialize<S: Serializer>(set: &IdSet<usize>, s: S) -> Result<S::Ok, S::Error> {
        let mut values: Vec<usize> = set.iter().copied().collect();
        values.sort_unstable();
        Ints(values).serialize(s)
    }
    pub fn deserialize<'de, D: Deserializer<'de>>(d: D) -> Result<IdSet<usize>, D::Error> {
        let Ints(values) = Ints::deserialize(d)?;
        if values.windows(2).any(|w| w[0] >= w[1]) {
            return Err(de::Error::custom("malformed index set"));
        }
        Ok(values.into_iter().collect())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::cache_codec;

    #[test]
    fn integer_columns_take_the_width_of_their_largest_value() {
        for (values, w) in [
            (vec![], 1usize),
            (vec![0, 255], 1),
            (vec![256, 3], 2),
            (vec![70_000], 4),
            (vec![1 << 40, 1], 8),
        ] {
            let bytes = cache_codec::encode(&Ints(values.clone())).unwrap();
            let back: Ints = cache_codec::decode(&bytes).unwrap();
            assert_eq!(back.0, values);
            // an empty string table (one byte), the tag, a one-byte count, the
            // width byte, the values
            assert_eq!(bytes.len(), 1 + 1 + 1 + 1 + values.len() * w);
        }
        let words = Words(vec![u64::MAX, 0]);
        let back: Words = cache_codec::decode(&cache_codec::encode(&words).unwrap()).unwrap();
        assert_eq!(back, words);
    }

    #[test]
    fn malformed_columns_are_rejected() {
        for bytes in [
            vec![],
            vec![3u8, 1, 2, 3],
            vec![2u8, 1],
            vec![4u8, 1, 2, 3, 4, 5],
        ] {
            let encoded = cache_codec::encode(&Bytes(bytes)).unwrap();
            assert!(cache_codec::decode::<Ints>(&encoded).is_err());
        }
        let odd = cache_codec::encode(&Bytes(vec![0u8; 17])).unwrap();
        assert!(cache_codec::decode::<Ids>(&odd).is_err());
    }

    #[test]
    fn identifier_and_byte_columns_round_trip() {
        let ids = Ids(vec![
            Uuid::nil(),
            Uuid::from_u128(0x1234_5678_9abc_def0_1234_5678_9abc_def0),
        ]);
        let back: Ids = cache_codec::decode(&cache_codec::encode(&ids).unwrap()).unwrap();
        assert_eq!(back, ids);
        let bytes = Bytes(vec![0, 7, 255]);
        let back: Bytes = cache_codec::decode(&cache_codec::encode(&bytes).unwrap()).unwrap();
        assert_eq!(back, bytes);
    }

    #[test]
    fn list_columns_round_trip_and_refuse_short_values() {
        let lists = vec![(3usize, vec![1usize, 2]), (5, vec![]), (9, vec![4])];
        let back = cache_codec::decode::<IndexLists>(
            &cache_codec::encode(&IndexLists::from(lists.clone())).unwrap(),
        )
        .unwrap()
        .into_lists()
        .unwrap();
        assert_eq!(back, lists);
        let short = IndexLists {
            keys: Ints(vec![1, 2]),
            lengths: Ints(vec![2, 1]),
            values: Ints(vec![7]),
        };
        assert!(short.into_lists().is_none());
        let a = Uuid::from_u128(1);
        let b = Uuid::from_u128(2);
        let ids = vec![(a, vec![b, a]), (b, vec![])];
        let back = cache_codec::decode::<IdLists>(
            &cache_codec::encode(&IdLists::from(ids.clone())).unwrap(),
        )
        .unwrap()
        .into_lists()
        .unwrap();
        assert_eq!(back, ids);
        let mixed = vec![(4usize, vec![a])];
        let back = cache_codec::decode::<IndexIdLists>(
            &cache_codec::encode(&IndexIdLists::from(mixed.clone())).unwrap(),
        )
        .unwrap()
        .into_lists()
        .unwrap();
        assert_eq!(back, mixed);
        let pairs = vec![(1usize, 2usize), (3, 4)];
        let back = cache_codec::decode::<Pairs>(
            &cache_codec::encode(&Pairs::from(pairs.clone())).unwrap(),
        )
        .unwrap()
        .into_pairs()
        .unwrap();
        assert_eq!(back, pairs);
        assert!(
            Pairs {
                first: Ints(vec![1]),
                second: Ints(vec![])
            }
            .into_pairs()
            .is_none()
        );
        let flags = vec![true, false, true];
        let back = cache_codec::decode::<Flags>(
            &cache_codec::encode(&Flags::from(flags.clone())).unwrap(),
        )
        .unwrap()
        .into_flags()
        .unwrap();
        assert_eq!(back, flags);
        assert!(Flags(Bytes(vec![2])).into_flags().is_none());
    }

    #[test]
    fn optional_index_columns_and_index_maps_round_trip() {
        #[derive(Serialize, Deserialize)]
        struct T(
            #[serde(with = "opt_index_vec")] crate::layered::LayeredVec<Option<usize>>,
            #[serde(with = "index_map")] crate::layered::LayeredMap<usize, usize>,
            #[serde(with = "index_set")] crate::layered::IdSet<usize>,
        );
        let owners: crate::layered::LayeredVec<Option<usize>> =
            vec![None, Some(0), Some(2), None].into();
        let map: crate::layered::LayeredMap<usize, usize> = [(5, 1), (2, 9)].into_iter().collect();
        let set: crate::layered::IdSet<usize> = [7, 3].into_iter().collect();
        let t = T(owners, map, set);
        let back: T = cache_codec::decode(&cache_codec::encode(&t).unwrap()).unwrap();
        assert_eq!(
            back.0.iter().copied().collect::<Vec<_>>(),
            vec![None, Some(0), Some(2), None]
        );
        assert_eq!(back.1.get(&5), Some(&1));
        assert_eq!(back.1.get(&2), Some(&9));
        assert_eq!(back.1.iter().count(), 2);
        assert!(back.2.contains(&7) && back.2.contains(&3) && back.2.len() == 2);
        // a pointer past the rows is refused
        let bad =
            cache_codec::encode(&(Ints(vec![5, 0]), (Ints(vec![]), Ints(vec![])), Ints(vec![])))
                .unwrap();
        assert!(cache_codec::decode::<T>(&bad).is_err());
    }
}
