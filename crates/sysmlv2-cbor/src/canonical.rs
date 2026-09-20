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
//! first-claimant ownership backpointers spelled, elements id-sorted),
//! so `state_digest` over the two spellings can meet in one domain.

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
    let arr = doc
        .as_array()
        .ok_or_else(|| Error::new("interchange payload is a flat element array"))?;
    let mut out = Vec::with_capacity(arr.len());
    for e in arr {
        out.push(normalize_element(e)?);
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
    let doc: Value =
        serde_json::from_str(text).map_err(|e| Error::new(format!("invalid JSON: {e}")))?;
    serde_json::to_string(&graph_normalize(&doc)?).map_err(|e| Error::new(e.to_string()))
}

fn compact_fields(ty: &str) -> Option<&'static [CborField]> {
    METACLASS_FIELDS
        .binary_search_by(|(n, _)| n.cmp(&ty))
        .ok()
        .map(|i| METACLASS_FIELDS[i].1)
}

fn normalize_element(e: &Value) -> Result<Value, Error> {
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
                if !is_wire_default(&fields[i as usize], value) {
                    wire.insert(key.clone(), value.clone());
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
