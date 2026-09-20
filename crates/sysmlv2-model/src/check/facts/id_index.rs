//! Sorted immutable identity table with private additions. Snapshot reads check
//! ordering once and query the stored rows without rehashing library identities.
use serde::{Deserialize, Deserializer, Serialize, Serializer};
use std::{collections::HashMap, sync::Arc};
use uuid::Uuid;

// Restrict a lookup to one of 4096 ordered UUID-prefix ranges. This keeps
// direct-table lookup short without reconstructing a hash map on every load.
const BUCKETS: usize = 4096;
fn bucket(id: &Uuid) -> usize {
    (id.as_u128() >> 116) as usize
}
fn offsets(rows: &[(Uuid, usize)]) -> Vec<usize> {
    let mut offsets = vec![0; BUCKETS + 1];
    let mut i = 0;
    for (bucket_index, offset) in offsets.iter_mut().enumerate().skip(1) {
        while i < rows.len() && bucket(&rows[i].0) < bucket_index {
            i += 1;
        }
        *offset = i;
    }
    offsets
}
#[derive(Serialize, Deserialize)]
struct Table {
    rows: Vec<(Uuid, usize)>,
    offsets: Vec<usize>,
}
impl Table {
    fn new(rows: Vec<(Uuid, usize)>) -> Self {
        Self {
            offsets: offsets(&rows),
            rows,
        }
    }
}
impl Default for Table {
    fn default() -> Self {
        Self::new(Vec::new())
    }
}

#[derive(Clone, Default)]
pub(super) struct IdIndex {
    base: Arc<Table>,
    local: HashMap<Uuid, usize>,
}
impl IdIndex {
    pub(super) fn get(&self, id: &Uuid) -> Option<&usize> {
        self.local.get(id).or_else(|| {
            let bucket = bucket(id);
            let rows = &self.base.rows[self.base.offsets[bucket]..self.base.offsets[bucket + 1]];
            rows.binary_search_by_key(id, |(id, _)| *id)
                .ok()
                .map(|i| &rows[i].1)
        })
    }
    pub(super) fn insert(&mut self, id: Uuid, index: usize) {
        self.local.insert(id, index);
    }
    pub(super) fn values(&self) -> impl Iterator<Item = &usize> {
        self.base
            .rows
            .iter()
            .map(|(_, i)| i)
            .chain(self.local.values())
    }
    fn rows(&self) -> Vec<(Uuid, usize)> {
        let mut rows: Vec<_> = self
            .base
            .rows
            .iter()
            .copied()
            .filter(|(id, _)| !self.local.contains_key(id))
            .chain(self.local.iter().map(|(&id, &i)| (id, i)))
            .collect();
        rows.sort_unstable_by_key(|&(id, _)| id);
        rows
    }
    pub(super) fn freeze(&mut self) {
        if !self.local.is_empty() {
            self.base = Arc::new(Table::new(self.rows()));
            self.local.clear();
            self.local.shrink_to_fit();
        }
    }
}
impl Serialize for IdIndex {
    fn serialize<S: Serializer>(&self, s: S) -> Result<S::Ok, S::Error> {
        if self.local.is_empty() {
            self.base.serialize(s)
        } else {
            Table::new(self.rows()).serialize(s)
        }
    }
}
impl<'de> Deserialize<'de> for IdIndex {
    fn deserialize<D: Deserializer<'de>>(d: D) -> Result<Self, D::Error> {
        let table = Table::deserialize(d)?;
        if table.rows.windows(2).any(|r| r[0].0 >= r[1].0) {
            return Err(serde::de::Error::custom("unsorted or duplicate identities"));
        }
        if table.offsets != offsets(&table.rows) {
            return Err(serde::de::Error::custom("invalid identity prefix offsets"));
        }
        Ok(Self {
            base: Arc::new(table),
            local: HashMap::new(),
        })
    }
}
#[cfg(test)]
mod tests {
    use super::*;
    use crate::cache_codec;
    #[test]
    fn identity_table_preserves_overrides_and_shared_prefix() {
        let mut index = IdIndex::default();
        for n in 1..=100 {
            index.insert(Uuid::from_u128(n), n as usize);
        }
        index.freeze();
        let mut decoded: IdIndex =
            cache_codec::decode(&cache_codec::encode(&index).unwrap()).unwrap();
        let retained = decoded.clone();
        assert!(Arc::ptr_eq(&decoded.base, &retained.base));
        decoded.insert(Uuid::from_u128(2), 202);
        decoded.insert(Uuid::from_u128(101), 101);
        for n in 1..=101 {
            assert_eq!(
                decoded.get(&Uuid::from_u128(n)),
                Some(&(if n == 2 { 202 } else { n as usize }))
            );
        }
        assert!(decoded.get(&Uuid::nil()).is_none());
        let replay: IdIndex = cache_codec::decode(&cache_codec::encode(&decoded).unwrap()).unwrap();
        assert_eq!(replay.get(&Uuid::from_u128(2)), Some(&202));
        decoded.freeze();
        assert_eq!(decoded.base.rows.len(), 101);
        assert_eq!(retained.get(&Uuid::from_u128(2)), Some(&2));
        assert!(retained.get(&Uuid::from_u128(101)).is_none());
    }
    #[test]
    fn identity_prefix_bounds_cover_empty_ranges_and_both_extremes() {
        let mut index = IdIndex::default();
        let ids = [
            Uuid::nil(),
            Uuid::from_u128(3 << 116),
            Uuid::from_u128((3 << 116) + 9),
            Uuid::from_u128(u128::MAX),
        ];
        for (i, id) in ids.iter().enumerate() {
            index.insert(*id, i);
        }
        index.freeze();
        let bytes = cache_codec::encode(&index).unwrap();
        let replay: IdIndex = cache_codec::decode(&bytes).unwrap();
        for (i, id) in ids.iter().enumerate() {
            assert_eq!(replay.get(id), Some(&i));
        }
        assert!(replay.get(&Uuid::from_u128(2 << 116)).is_none());
        assert!(replay.get(&Uuid::from_u128((3 << 116) + 5)).is_none());
        let mut table: Table = cache_codec::decode(&bytes).unwrap();
        table.offsets[3] = usize::MAX;
        assert!(cache_codec::decode::<IdIndex>(&cache_codec::encode(&table).unwrap()).is_err());
        table.offsets.clear();
        assert!(cache_codec::decode::<IdIndex>(&cache_codec::encode(&table).unwrap()).is_err());
    }
    #[test]
    fn malformed_identity_order_is_rejected() {
        for rows in [
            vec![(Uuid::from_u128(2), 0usize), (Uuid::from_u128(1), 1)],
            vec![(Uuid::nil(), 0), (Uuid::nil(), 1)],
        ] {
            assert!(
                cache_codec::decode::<IdIndex>(&cache_codec::encode(&Table::new(rows)).unwrap())
                    .is_err()
            );
        }
    }
}
