//! Immutable scope lookup tables. Names are sorted string-table entries and
//! bindings are checked ranges into one shared vector. Only edited scopes
//! rebuild a hash map; lookup and candidate enumeration read the table directly.
use super::{Binding, Scope};
use crate::{
    flat::{Row, Slices},
    layered::LayeredVec,
};
use serde::{Deserialize, Deserializer, Serialize, Serializer};
use std::{collections::HashMap, sync::Arc};

#[derive(Clone)]
pub(super) enum Names {
    Owned(HashMap<String, Vec<Binding>>),
    Table {
        rows: Row<Name>,
        bindings: Arc<Vec<Binding>>,
    },
}
impl Default for Names {
    fn default() -> Self {
        Self::Owned(HashMap::new())
    }
}
#[derive(Clone, Serialize, Deserialize)]
pub(super) struct Name {
    #[serde(deserialize_with = "crate::cache_codec::shared_string")]
    text: Arc<str>,
    start: usize,
    end: usize,
}
impl Names {
    pub(super) fn get(&self, name: &str) -> Option<&[Binding]> {
        match self {
            Self::Owned(map) => map.get(name).map(Vec::as_slice),
            Self::Table { rows, bindings } => {
                let row = if rows.len() <= 8 {
                    rows.iter().find(|row| row.text.as_ref() == name)?
                } else {
                    &rows[rows
                        .binary_search_by(|row| row.text.as_ref().cmp(name))
                        .ok()?]
                };
                Some(&bindings[row.start..row.end])
            }
        }
    }
    pub(super) fn push(&mut self, name: String, binding: Binding) {
        if matches!(self, Self::Table { .. }) {
            *self = Self::Owned(
                self.iter()
                    .map(|(n, b)| (n.to_owned(), b.to_vec()))
                    .collect(),
            );
        }
        if let Self::Owned(map) = self {
            map.entry(name).or_default().push(binding);
        }
    }
    pub(super) fn iter(&self) -> NamesIter<'_> {
        match self {
            Self::Owned(map) => NamesIter::Owned(map.iter()),
            Self::Table { rows, bindings } => NamesIter::Table(rows.iter(), bindings),
        }
    }
    pub(super) fn values(&self) -> impl Iterator<Item = &[Binding]> {
        self.iter().map(|(_, b)| b)
    }
}
pub(super) enum NamesIter<'a> {
    Owned(std::collections::hash_map::Iter<'a, String, Vec<Binding>>),
    Table(std::slice::Iter<'a, Name>, &'a [Binding]),
}
impl<'a> Iterator for NamesIter<'a> {
    type Item = (&'a str, &'a [Binding]);
    fn next(&mut self) -> Option<Self::Item> {
        match self {
            Self::Owned(it) => it.next().map(|(n, b)| (n.as_str(), b.as_slice())),
            Self::Table(it, bindings) => it
                .next()
                .map(|n| (n.text.as_ref(), &bindings[n.start..n.end])),
        }
    }
}

pub(super) fn serialize<S: Serializer>(
    scopes: &LayeredVec<Scope>,
    s: S,
) -> Result<S::Ok, S::Error> {
    use serde::ser::SerializeTuple;
    let mut bindings = Vec::new();
    let mut rows = Vec::new();
    for scope in scopes {
        for names in [&scope.names, &scope.effective_names] {
            let mut entries: Vec<_> = names.iter().collect();
            entries.sort_unstable_by_key(|&(name, _)| name);
            let mut row = Vec::with_capacity(entries.len());
            for (text, values) in entries {
                let start = bindings.len();
                bindings.extend_from_slice(values);
                row.push(Name {
                    text: text.into(),
                    start,
                    end: bindings.len(),
                });
            }
            rows.push(row);
        }
    }
    let mut out = s.serialize_tuple(3)?;
    out.serialize_element(scopes)?;
    out.serialize_element(&Slices(rows.iter().map(Vec::as_slice).collect()))?;
    out.serialize_element(&bindings)?;
    out.end()
}

pub(super) fn deserialize<'de, D: Deserializer<'de>>(d: D) -> Result<LayeredVec<Scope>, D::Error> {
    #[derive(Deserialize)]
    struct Wire {
        scopes: Vec<Scope>,
        #[serde(with = "crate::flat::table")]
        names: Vec<Row<Name>>,
        bindings: Vec<Binding>,
    }
    let Wire {
        mut scopes,
        names,
        bindings,
    } = Wire::deserialize(d)?;
    if scopes.len().checked_mul(2) != Some(names.len()) {
        return Err(serde::de::Error::custom("scope/name row count mismatch"));
    }
    let mut end = 0;
    for row in &names {
        if row.windows(2).any(|pair| pair[0].text >= pair[1].text) {
            return Err(serde::de::Error::custom(
                "unsorted or duplicate scope names",
            ));
        }
        for name in row {
            if name.start != end || name.end < name.start || name.end > bindings.len() {
                return Err(serde::de::Error::custom("invalid scope binding range"));
            }
            end = name.end;
        }
    }
    if end != bindings.len() {
        return Err(serde::de::Error::custom("unused scope bindings"));
    }
    let bindings = Arc::new(bindings);
    for (i, scope) in scopes.iter_mut().enumerate() {
        scope.names = Names::Table {
            rows: names[2 * i].clone(),
            bindings: bindings.clone(),
        };
        scope.effective_names = Names::Table {
            rows: names[2 * i + 1].clone(),
            bindings: bindings.clone(),
        };
    }
    Ok(scopes.into())
}

#[cfg(test)]
mod tests {
    use super::super::LookupAccess;
    use super::*;
    use crate::cache_codec;
    #[derive(Serialize, Deserialize)]
    struct Table(#[serde(with = "super")] LayeredVec<Scope>);
    fn binding(elem: usize) -> Binding {
        Binding {
            elem,
            sub_scope: None,
            visibility: LookupAccess::Public,
        }
    }
    #[test]
    fn lookup_tables_share_storage_and_preserve_all_candidates_on_edit() {
        let mut scope = Scope::default();
        scope.names.push("z".into(), binding(2));
        scope.names.push("a".into(), binding(0));
        scope.names.push("a".into(), binding(1));
        scope.effective_names.push("z".into(), binding(3));
        let encoded = cache_codec::encode(&Table(vec![scope.clone(), scope].into())).unwrap();
        let table: Table = cache_codec::decode(&encoded).unwrap();
        let (
            Names::Table {
                rows: a,
                bindings: ab,
            },
            Names::Table {
                rows: b,
                bindings: bb,
            },
        ) = (&table.0[0].names, &table.0[1].names)
        else {
            panic!("expected shared lookup table")
        };
        assert!(Arc::ptr_eq(ab, bb));
        let (Row::Shared { values: av, .. }, Row::Shared { values: bv, .. }) = (a, b) else {
            panic!("expected shared name rows")
        };
        assert!(Arc::ptr_eq(av, bv));
        assert!(Arc::ptr_eq(&a[0].text, &b[0].text));
        assert_eq!(
            table.0[0].names.get("a"),
            Some([binding(0), binding(1)].as_slice())
        );
        assert!(table.0[0].names.get("missing").is_none());
        let mut changed = table.0[0].clone();
        changed.names.push("a".into(), binding(4));
        changed.names.push("b".into(), binding(5));
        assert_eq!(changed.names.get("a").unwrap().len(), 3);
        assert_eq!(table.0[0].names.get("a").unwrap().len(), 2);
        assert!(table.0[1].names.get("b").is_none());
        assert_eq!(
            changed.effective_names.get("z"),
            Some([binding(3)].as_slice())
        );
        let edited = Table(vec![changed].into());
        let replay: Table = cache_codec::decode(&cache_codec::encode(&edited).unwrap()).unwrap();
        assert_eq!(replay.0[0].names.get("a"), edited.0[0].names.get("a"));
    }
    #[test]
    fn malformed_scope_tables_are_rejected_before_lookup() {
        let name = |text: &str, start, end| Name {
            text: text.into(),
            start,
            end,
        };
        let cases = [
            (vec![vec![name("a", 0, 1)]], vec![binding(0)]), // wrong scope count
            (
                vec![vec![name("a", 1, 2)], vec![]],
                vec![binding(0), binding(1)],
            ),
            (vec![vec![name("a", 0, 2)], vec![]], vec![binding(0)]),
            (
                vec![vec![name("a", 0, 1), name("a", 1, 2)], vec![]],
                vec![binding(0), binding(1)],
            ),
            (
                vec![vec![name("b", 0, 1), name("a", 1, 2)], vec![]],
                vec![binding(0), binding(1)],
            ),
            (vec![vec![name("a", 0, 0)], vec![]], vec![binding(0)]),
            (vec![vec![name("a", 0, usize::MAX)], vec![]], vec![]),
        ];
        for (rows, bindings) in cases {
            let wire = (
                vec![Scope::default()],
                Slices(rows.iter().map(Vec::as_slice).collect()),
                bindings,
            );
            let bytes = cache_codec::encode(&(wire,)).unwrap();
            assert!(cache_codec::decode::<Table>(&bytes).is_err());
        }
    }
}
