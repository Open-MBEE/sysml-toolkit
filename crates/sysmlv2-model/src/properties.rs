//! Typed semantic properties. JSON objects are constructed only for interchange
//! and reflection. References retain binary identities; booleans use bitsets.
use serde::{Deserialize, Deserializer, Serialize, Serializer};
use serde_json::{Map, Value};
use std::{
    borrow::Borrow,
    collections::{BTreeMap, HashMap},
    sync::{Arc, OnceLock},
};
use uuid::Uuid;

#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd)]
pub(crate) struct Key(Arc<str>);
impl Key {
    pub fn name(&self) -> &str {
        &self.0
    }
}
impl Borrow<str> for Key {
    fn borrow(&self) -> &str {
        &self.0
    }
}
impl Serialize for Key {
    fn serialize<S: Serializer>(&self, s: S) -> Result<S::Ok, S::Error> {
        s.serialize_str(&self.0)
    }
}
impl<'de> Deserialize<'de> for Key {
    fn deserialize<D: Deserializer<'de>>(d: D) -> Result<Self, D::Error> {
        struct Visitor;
        impl serde::de::Visitor<'_> for Visitor {
            type Value = Key;
            fn expecting(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
                f.write_str("a property name")
            }
            fn visit_str<E: serde::de::Error>(self, v: &str) -> Result<Key, E> {
                Ok(key(v))
            }
        }
        d.deserialize_str(Visitor)
    }
}
fn key(name: &str) -> Key {
    static KEYS: OnceLock<HashMap<&'static str, Arc<str>>> = OnceLock::new();
    let keys = KEYS.get_or_init(|| {
        let mut keys = HashMap::new();
        for (_, props) in crate::schema_props::METACLASS_PROPS {
            for &(name, _) in *props {
                keys.entry(name).or_insert_with(|| Arc::from(name));
            }
        }
        for name in ["@id", "@ref", "@type", "kind"] {
            keys.entry(name).or_insert_with(|| Arc::from(name));
        }
        keys
    });
    Key(keys.get(name).cloned().unwrap_or_else(|| name.into()))
}
const FLAGS: &[&str] = &[
    "isAbstract",
    "isComposite",
    "isConstant",
    "isDerived",
    "isEnd",
    "isImplied",
    "isImpliedIncluded",
    "isIndividual",
    "isOrdered",
    "isPortion",
    "isReference",
    "isSufficient",
    "isUnique",
    "isVariable",
    "isVariation",
];
fn flag(key: &str) -> Option<u64> {
    if !key.starts_with("is") {
        return None;
    }
    FLAGS.iter().position(|&s| s == key).map(|i| 1 << i)
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub(crate) struct Reference {
    pub id: Uuid,
    #[serde(skip)]
    spelling: OnceLock<Box<Atom>>,
}
#[derive(Clone, Debug, Serialize, Deserialize)]
pub(crate) enum Atom {
    Null,
    Bool(bool),
    Number(serde_json::Number),
    String(#[serde(deserialize_with = "crate::cache_codec::shared_string")] Arc<str>),
    Reference(Reference),
    Array(Vec<Atom>),
    Object(BTreeMap<Key, Atom>),
}
impl PartialEq for Atom {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Null, Self::Null) => true,
            (Self::Bool(a), Self::Bool(b)) => a == b,
            (Self::String(a), Self::String(b)) => a == b,
            (Self::Number(a), Self::Number(b)) => a == b,
            (Self::Reference(a), Self::Reference(b)) => a.id == b.id,
            (Self::Array(a), Self::Array(b)) => a == b,
            (Self::Object(a), Self::Object(b)) => a == b,
            _ => false,
        }
    }
}
impl Atom {
    pub fn from_json(v: Value) -> Self {
        match v {
            Value::Null => Self::Null,
            Value::Bool(v) => Self::Bool(v),
            Value::Number(v) => Self::Number(v),
            Value::String(v) => Self::String(v.into()),
            Value::Array(v) => Self::Array(v.into_iter().map(Self::from_json).collect()),
            Value::Object(v) => {
                // A lone `@id` is an element reference. Its spelling is not
                // retained: any parseable UUID form re-emits in the canonical
                // hyphenated lowercase form. Every identity reaching here is
                // builder-generated in that form already.
                if v.len() == 1 {
                    if let Some(id) = v
                        .get("@id")
                        .and_then(Value::as_str)
                        .and_then(|s| Uuid::parse_str(s).ok())
                    {
                        return Self::Reference(Reference {
                            id,
                            spelling: OnceLock::new(),
                        });
                    }
                }
                Self::Object(
                    v.into_iter()
                        .map(|(k, v)| (key(&k), Self::from_json(v)))
                        .collect(),
                )
            }
        }
    }
    pub fn to_json(&self) -> Value {
        match self {
            Self::Null => Value::Null,
            Self::Bool(v) => Value::Bool(*v),
            Self::Number(v) => Value::Number(v.clone()),
            Self::String(v) => Value::String(v.to_string()),
            Self::Reference(r) => serde_json::json!({"@id":r.id.to_string()}),
            Self::Array(v) => Value::Array(v.iter().map(Self::to_json).collect()),
            Self::Object(v) => Value::Object(
                v.iter()
                    .map(|(k, v)| (k.0.to_string(), v.to_json()))
                    .collect(),
            ),
        }
    }
    pub fn as_reference(&self) -> Option<Uuid> {
        if let Self::Reference(r) = self {
            Some(r.id)
        } else {
            None
        }
    }
    pub fn as_str(&self) -> Option<&str> {
        if let Self::String(s) = self {
            Some(s)
        } else {
            None
        }
    }
    pub fn as_bool(&self) -> Option<bool> {
        if let Self::Bool(b) = self {
            Some(*b)
        } else {
            None
        }
    }
    pub fn is_string(&self) -> bool {
        matches!(self, Self::String(_))
    }
    pub fn is_null(&self) -> bool {
        matches!(self, Self::Null)
    }
    pub fn as_array(&self) -> Option<&Vec<Self>> {
        if let Self::Array(a) = self {
            Some(a)
        } else {
            None
        }
    }
    // Compatibility for uncommon graph/reflection queries. Semantic edge
    // indexes use as_reference() and never materialize UUID strings.
    pub fn get(&self, k: &str) -> Option<&Self> {
        match self {
            Self::Object(v) => v.get(k),
            Self::Reference(r) if k == "@id" => Some(
                r.spelling
                    .get_or_init(|| Box::new(Self::String(r.id.to_string().into()))),
            ),
            _ => None,
        }
    }
    pub fn remap(&mut self, ids: &HashMap<Uuid, Uuid>) {
        match self {
            Self::Reference(r) => {
                if let Some(id) = ids.get(&r.id) {
                    r.id = *id;
                    r.spelling = OnceLock::new();
                }
            }
            Self::Array(v) => {
                for v in v {
                    v.remap(ids);
                }
            }
            Self::Object(v) => {
                for v in v.values_mut() {
                    v.remap(ids);
                }
            }
            _ => {}
        }
    }
}
#[derive(Clone, Default, Serialize, Deserialize)]
pub(crate) struct Properties {
    pub(crate) present: u64,
    pub(crate) flags: u64,
    pub(crate) entries: crate::flat::Row<(Key, Atom)>,
}
impl Properties {
    pub fn new() -> Self {
        Self::default()
    }
    pub fn get(&self, k: &str) -> Option<&Atom> {
        if let Some(bit) = flag(k) {
            if self.present & bit != 0 {
                return Some(if self.flags & bit != 0 {
                    &Atom::Bool(true)
                } else {
                    &Atom::Bool(false)
                });
            }
        }
        self.entries
            .binary_search_by(|(key, _)| key.name().cmp(k))
            .ok()
            .map(|i| &self.entries[i].1)
    }
    pub fn insert(&mut self, k: &str, v: Value) {
        if let Some(bit) = flag(k) {
            if let Value::Bool(b) = v {
                self.present |= bit;
                if b {
                    self.flags |= bit;
                } else {
                    self.flags &= !bit;
                }
                if let Ok(i) = self.entries.binary_search_by(|(key, _)| key.name().cmp(k)) {
                    self.entries.make_mut().remove(i);
                }
                return;
            }
            self.present &= !bit;
            self.flags &= !bit;
        }
        let value = (key(k), Atom::from_json(v));
        match self.entries.binary_search_by(|(key, _)| key.name().cmp(k)) {
            Ok(i) => self.entries.make_mut()[i] = value,
            Err(i) => self.entries.make_mut().insert(i, value),
        }
    }
    pub fn append(&mut self, k: &str, value: Value) {
        let i = match self.entries.binary_search_by(|(key, _)| key.name().cmp(k)) {
            Ok(i) => i,
            Err(i) => {
                self.entries
                    .make_mut()
                    .insert(i, (key(k), Atom::Array(Vec::new())));
                i
            }
        };
        if let Atom::Array(a) = &mut self.entries.make_mut()[i].1 {
            a.push(Atom::from_json(value));
        }
    }
    pub fn references(&self) -> impl Iterator<Item = (Key, Uuid)> + '_ {
        self.entries
            .iter()
            .filter_map(|(k, v)| Some((k.clone(), v.as_reference()?)))
    }
    pub fn values_mut(&mut self) -> impl Iterator<Item = &mut Atom> {
        self.entries.make_mut().iter_mut().map(|(_, v)| v)
    }
    pub fn to_json(&self) -> Map<String, Value> {
        let mut map: Map<_, _> = self
            .entries
            .iter()
            .map(|(k, v)| (k.0.to_string(), v.to_json()))
            .collect();
        for (i, &name) in FLAGS.iter().enumerate() {
            if self.present & (1 << i) != 0 {
                map.insert(name.into(), Value::Bool(self.flags & (1 << i) != 0));
            }
        }
        map
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;
    #[test]
    fn typed_properties_preserve_presence_numbers_and_reference_remapping() {
        let a = Uuid::from_u128(1);
        let b = Uuid::from_u128(2);
        let mut p = Properties::new();
        assert!(p.get("isAbstract").is_none());
        for v in [json!(false), json!(true), Value::Null, json!(false)] {
            p.insert("isAbstract", v.clone());
            assert_eq!(p.get("isAbstract").unwrap().to_json(), v);
            assert_eq!(p.to_json()["isAbstract"], v);
        }
        p.insert("target", json!({"@id":a}));
        p.append("relatedElement", json!({"@id":a}));
        p.insert("value", json!(u64::MAX));
        // Populate the compatibility spelling before remapping its identity.
        assert_eq!(
            p.get("target").unwrap().get("@id").unwrap().as_str(),
            Some(a.to_string().as_str())
        );
        for v in p.values_mut() {
            v.remap(&HashMap::from([(a, b)]));
        }
        let expected = json!({"isAbstract":false,"target":{"@id":b},"relatedElement":[{"@id":b}],"value":u64::MAX});
        assert_eq!(Value::Object(p.to_json()), expected);
        let restored: Properties =
            crate::cache_codec::decode(&crate::cache_codec::encode(&p).unwrap()).unwrap();
        assert_eq!(Value::Object(restored.to_json()), expected);
        assert_eq!(restored.get("target").unwrap().as_reference(), Some(b));
        let first = key("declaredName");
        let second = key("declaredName");
        assert!(Arc::ptr_eq(&first.0, &second.0));
    }
}
