//! Compact-form canonicalization: materialize every element of a
//! compact interchange document through its metaclass field table and
//! re-emit with each absent property spelled at its metaclass-specific
//! default. Producers that wire-elide schema defaults (`isUnique:
//! true`, `isAbstract: false`, `visibility: "public"`, empty lists,
//! nulls, the `elementId` mirror of `@id`) and producers that spell
//! them explicitly land on the same canonical document, so digest
//! comparison across the two spellings becomes sound. The CBOR
//! round-trip deliberately does NOT do this — encode/decode is
//! presence-faithful (an absent default stays absent) — which is
//! exactly why this entry point exists.
//!
//! [`graph_normalize`] is the mirror twin in the opposite direction:
//! it re-spells a compact document the way a graph-backed store
//! materializes it from triples (defaults elided, `elementId` and
//! first-claimant ownership backpointers spelled, each literal's number
//! spelled as its value type spells it, elements id-sorted), so
//! `state_digest` over the two spellings can meet in one domain.

use std::collections::HashMap;

use serde_json::{Map, Value};

use crate::encode::{ctx, default_value, is_default_value};
use crate::tables::{CborField, FULL_METACLASS_FIELDS, K_ELEMENT_ID, K_LITERAL, METACLASS_FIELDS};
use crate::{Error, ordinal};

/// Canonicalize a compact interchange document (the flat element array
/// of KerML 10.4.4): every absent non-derived property of each
/// element's concrete metaclass is inserted at its default value from
/// the generated field tables. Literal-valued fields have no default
/// and stay absent. Present values and `@id`s are preserved verbatim,
/// element order is untouched, and the result is independent of the
/// input's key order and of its default elision/spelling split —
/// canonicalization is idempotent. Strict like the encoder: an unknown
/// `@type`, a missing `@id`, or a key outside the metaclass's
/// compact-form property set is an error, never silently passed
/// through.
pub fn canonicalize_compact(text: &str) -> Result<String, Error> {
    let doc: Value =
        serde_json::from_str(text).map_err(|e| Error::new(format!("invalid JSON: {e}")))?;
    let arr = doc
        .as_array()
        .ok_or_else(|| Error::new("interchange payload is a flat element array"))?;
    let mut out = Vec::with_capacity(arr.len());
    for e in arr {
        out.push(canonicalize_element(e)?);
    }
    serde_json::to_string(&Value::Array(out)).map_err(|e| Error::new(e.to_string()))
}

fn canonicalize_element(e: &Value) -> Result<Value, Error> {
    let obj = e
        .as_object()
        .ok_or_else(|| Error::new("element is an object"))?;
    let ty = obj
        .get("@type")
        .and_then(Value::as_str)
        .ok_or_else(|| Error::new("element has a string @type"))?;
    let fields = METACLASS_FIELDS
        .binary_search_by(|(n, _)| n.cmp(&ty))
        .map(|i| METACLASS_FIELDS[i].1)
        .map_err(|_| Error::new(format!("unknown @type `{ty}`")))?;
    let id = obj
        .get("@id")
        .and_then(Value::as_str)
        .ok_or_else(|| Error::new(format!("{ty}: element has a string @id")))?;
    let mut canon = Map::new();
    canon.insert("@id".into(), Value::String(id.to_owned()));
    canon.insert("@type".into(), Value::String(ty.to_owned()));
    for (key, value) in obj {
        if key == "@id" || key == "@type" {
            continue;
        }
        if ordinal(fields, key).is_none() {
            return Err(ctx(ty, key, "not a compact-form property"));
        }
        canon.insert(key.clone(), value.clone());
    }
    for field in fields {
        if !canon.contains_key(field.0) {
            if let Some(d) = default_value(field, id) {
                canon.insert(field.0.to_owned(), d);
            }
        }
    }
    Ok(Value::Object(canon))
}

/// The mirror twin of [`canonicalize_compact`]: re-spell a compact
/// interchange document in the **graph-normal** (stored/wire-normal)
/// form — the spelling a graph-backed store reconstructs after
/// materializing the document as triples and projecting it back:
///
/// - wire-schema keys only: a *derived* canonical property (`owner`,
///   `qualifiedName`, … — any full-form-only key) is dropped, exactly
///   as such a store accepts-and-drops it on ingest; a key outside
///   even the full schema is an error, never silently passed through;
/// - every property sitting at its metaclass default is **elided**
///   (`isUnique: true`, `isAbstract: false`, default enum values,
///   empty lists, `null` scalars/refs) — the inverse of
///   [`canonicalize_compact`], which spells them all;
/// - `elementId` is always spelled (a store derives it from the
///   element identity, so the stored form always carries it);
/// - absent ownership backpointers (`owningRelationship`,
///   `owningRelatedElement`) are completed by **first-claimant
///   derivation** from the forward ownership lists in element order —
///   the same rule the wire-elision flag and a store's read-side
///   reconstruction use; explicitly spelled backpointers stay
///   verbatim;
/// - each literal's number is spelled as its metaclass's value type
///   spells it: a `LiteralRational`'s whole value as a float (`150.0`,
///   which a JSON round trip through JavaScript prints `150`), a
///   `LiteralInteger`'s as an integer (`150`, however written), so
///   every spelling of one value digests alike;
/// - elements are sorted by `@id`, the deterministic listing order a
///   store serves (root order is digest-relevant).
///
/// The point of the twin: `state_digest(graph_normalize(doc))` equals
/// the digest such a store reconstructs after ingesting `doc`, so a
/// producer that encodes the graph-normal spelling (and declares
/// digests in the same domain) passes the store's end-to-end snapshot
/// verification. Idempotent; strict like the encoder on unknown
/// `@type`s and missing `@id`s.
pub fn graph_normalize(doc: &Value) -> Result<Value, Error> {
    normalize(doc, true)
}

/// [`graph_normalize`] with each literal's number kept as the document
/// spells it, as graph normalization left it before every spelling of
/// a value was one. A digest recorded then over a document that spells
/// a whole real without its fraction is reproduced here, and only
/// here: the way to check such a record.
pub fn graph_normalize_as_spelled(doc: &Value) -> Result<Value, Error> {
    normalize(doc, false)
}

fn normalize(doc: &Value, respell: bool) -> Result<Value, Error> {
    let arr = doc
        .as_array()
        .ok_or_else(|| Error::new("interchange payload is a flat element array"))?;
    let mut out = Vec::with_capacity(arr.len());
    for e in arr {
        out.push(normalize_element(e, respell)?);
    }
    // First-claimant ownership backpointer derivation, in payload
    // element order: a member of some `ownedRelatedElement` list is
    // owned by that relationship; a member of some
    // `ownedRelationship` list is contained by that element.
    let refs = |e: &Value, key: &str| -> Vec<String> {
        e[key]
            .as_array()
            .map(|a| {
                a.iter()
                    .filter_map(|r| r["@id"].as_str().map(str::to_owned))
                    .collect()
            })
            .unwrap_or_default()
    };
    let mut owning_relationship: HashMap<String, String> = HashMap::new();
    let mut owning_related_element: HashMap<String, String> = HashMap::new();
    for element in &out {
        let id = element["@id"].as_str().unwrap_or_default().to_owned();
        for owned in refs(element, "ownedRelatedElement") {
            owning_relationship
                .entry(owned)
                .or_insert_with(|| id.clone());
        }
        for rel in refs(element, "ownedRelationship") {
            owning_related_element
                .entry(rel)
                .or_insert_with(|| id.clone());
        }
    }
    for element in &mut out {
        let id = element["@id"].as_str().unwrap_or_default().to_owned();
        let ty = element["@type"].as_str().unwrap_or_default().to_owned();
        let fields = compact_fields(&ty);
        let obj = match element.as_object_mut() {
            Some(o) => o,
            None => continue,
        };
        for (key, claims) in [
            ("owningRelationship", &owning_relationship),
            ("owningRelatedElement", &owning_related_element),
        ] {
            if !obj.contains_key(key) && fields.is_some_and(|f| ordinal(f, key).is_some()) {
                if let Some(owner) = claims.get(&id) {
                    obj.insert(key.into(), serde_json::json!({ "@id": owner }));
                }
            }
        }
    }
    out.sort_by(|a, b| a["@id"].as_str().cmp(&b["@id"].as_str()));
    Ok(Value::Array(out))
}

/// String-level [`graph_normalize`], the ergonomic twin of
/// [`canonicalize_compact`].
pub fn graph_normalize_compact(text: &str) -> Result<String, Error> {
    normalize_text(text, true)
}

/// String-level [`graph_normalize_as_spelled`].
pub fn graph_normalize_compact_as_spelled(text: &str) -> Result<String, Error> {
    normalize_text(text, false)
}

fn normalize_text(text: &str, respell: bool) -> Result<String, Error> {
    let doc: Value =
        serde_json::from_str(text).map_err(|e| Error::new(format!("invalid JSON: {e}")))?;
    serde_json::to_string(&normalize(&doc, respell)?).map_err(|e| Error::new(e.to_string()))
}

fn compact_fields(ty: &str) -> Option<&'static [CborField]> {
    METACLASS_FIELDS
        .binary_search_by(|(n, _)| n.cmp(&ty))
        .ok()
        .map(|i| METACLASS_FIELDS[i].1)
}

fn normalize_element(e: &Value, respell: bool) -> Result<Value, Error> {
    let obj = e
        .as_object()
        .ok_or_else(|| Error::new("element is an object"))?;
    let ty = obj
        .get("@type")
        .and_then(Value::as_str)
        .ok_or_else(|| Error::new("element has a string @type"))?;
    let fields = compact_fields(ty).ok_or_else(|| Error::new(format!("unknown @type `{ty}`")))?;
    let full_fields = FULL_METACLASS_FIELDS
        .binary_search_by(|(n, _)| n.cmp(&ty))
        .ok()
        .map(|i| FULL_METACLASS_FIELDS[i].1)
        .unwrap_or(&[]);
    let id = obj
        .get("@id")
        .and_then(Value::as_str)
        .ok_or_else(|| Error::new(format!("{ty}: element has a string @id")))?;
    let mut wire = Map::new();
    wire.insert("@id".into(), Value::String(id.to_owned()));
    wire.insert("@type".into(), Value::String(ty.to_owned()));
    for (key, value) in obj {
        if key == "@id" || key == "@type" {
            continue;
        }
        match ordinal(fields, key) {
            Some(i) => {
                let field = &fields[i as usize];
                if !is_wire_default(field, value) {
                    let spelled = match field.1 {
                        K_LITERAL if respell => literal_number(ty, value),
                        _ => None,
                    };
                    wire.insert(key.clone(), spelled.unwrap_or_else(|| value.clone()));
                }
            }
            // A derived canonical property (present in the full form
            // only) drops, as a store's ingest accepts-and-drops it.
            None if ordinal(full_fields, key).is_some() => {}
            None => return Err(ctx(ty, key, "not an interchange property")),
        }
    }
    // The stored spelling always carries the `elementId` mirror.
    for field in fields {
        if field.1 == K_ELEMENT_ID && !wire.contains_key(field.0) {
            wire.insert(field.0.to_owned(), Value::String(id.to_owned()));
        }
    }
    Ok(Value::Object(wire))
}

/// A literal's number as its metaclass's value type spells it, where
/// the document spells it otherwise: a `LiteralRational`'s value is a
/// real, so a whole number written as an integer is the float the
/// kernel emits; a `LiteralInteger`'s written as a float (`150.0`,
/// `1.5e2`) is the integer. `None` keeps the value as written: a number
/// spelled so already, one the other spelling does not hold exactly,
/// and anything not a number (a decimal no float holds is text).
// Each float-to-integer cast is of a whole number its range check pins
// inside the target type, or is compared back against the integer it
// came from — the narrowing is exact or refused.
#[allow(clippy::cast_possible_truncation)]
fn literal_number(ty: &str, value: &Value) -> Option<Value> {
    // 2^63 and 2^64, exactly: the integer ranges' ends as floats
    const I64_END: f64 = 9_223_372_036_854_775_808.0;
    const U64_END: f64 = 18_446_744_073_709_551_616.0;
    let n = value.as_number()?;
    match ty {
        "LiteralRational" if !n.is_f64() => {
            // the float only where it is the integer exactly
            let x = match (n.as_u64(), n.as_i64()) {
                (Some(u), _) => Some(u as f64).filter(|&x| x < U64_END && x as u64 == u),
                (None, Some(i)) => Some(i as f64).filter(|&x| x as i64 == i),
                (None, None) => None,
            }?;
            serde_json::Number::from_f64(x).map(Value::Number)
        }
        "LiteralInteger" if n.is_f64() => {
            let x = n.as_f64().filter(|x| x.fract() == 0.0)?;
            if (-I64_END..0.0).contains(&x) {
                Some(Value::from(x as i64))
            } else if (0.0..U64_END).contains(&x) {
                Some(Value::from(x as u64))
            } else {
                None
            }
        }
        _ => None,
    }
}

/// Is `value` the metaclass default the graph-normal spelling elides?
/// The metaclass defaults themselves are the encoder's rule; this
/// spelling parts from it exactly twice, and says so.
fn is_wire_default(field: &CborField, value: &Value) -> bool {
    match field.1 {
        // A store derives `elementId` from the element identity, so
        // the stored form always carries it.
        K_ELEMENT_ID => false,
        // A literal-valued field has no metaclass default, but the
        // stored form still elides a null one.
        K_LITERAL => value.is_null(),
        _ => is_default_value(field, "", value),
    }
}
