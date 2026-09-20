//! Structural identity of one member's text:
//! `member_structure_digest` parses a member standalone, serializes its
//! compact-JSON subtree, normalizes every identity to a local ordinal,
//! and hashes the result — a pure function of the member's canonical
//! text, independent of where it lives, what surrounds it, or which
//! session produced it. Provenance records persist the digest and
//! integrity checks recompute it, so there is deliberately exactly one
//! implementation; hosts that cannot link this crate call it through
//! the wasm module surface instead of reimplementing it.
//!
//! Normalization contract:
//! - visitation order: the member root, then each `ownedRelationship`
//!   and its `ownedRelatedElement` children, depth-first in document
//!   order — every visited element gets `$<ordinal>`;
//! - `@id`/`elementId` spellings inside the subtree rewrite to their
//!   ordinal; identities outside it spell `external:<id>` (standalone
//!   parses have none — unresolved names ride `@ref` text untouched);
//! - the root's `owningRelationship` is dropped (the synthetic wrapper
//!   is not part of the member's structure);
//! - the digest is `sha256:` + SHA-256 over the serialized node array.

use serde_json::{Map, Value};
use sysmlv2_syntax::ast::Dialect;
use sysmlv2_syntax::parser::parse_source;

/// SHA-256 (FIPS 180-4), lowercase hex — small and dependency-free;
/// these digests are persisted in model provenance records.
pub fn sha256_hex(data: &[u8]) -> String {
    const K: [u32; 64] = [
        0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4,
        0xab1c5ed5, 0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe,
        0x9bdc06a7, 0xc19bf174, 0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f,
        0x4a7484aa, 0x5cb0a9dc, 0x76f988da, 0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7,
        0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967, 0x27b70a85, 0x2e1b2138, 0x4d2c6dfc,
        0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85, 0xa2bfe8a1, 0xa81a664b,
        0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070, 0x19a4c116,
        0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
        0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7,
        0xc67178f2,
    ];
    let mut h: [u32; 8] = [
        0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab,
        0x5be0cd19,
    ];
    let mut msg = data.to_vec();
    let bit_len = (data.len() as u64) * 8;
    msg.push(0x80);
    while msg.len() % 64 != 56 {
        msg.push(0);
    }
    msg.extend_from_slice(&bit_len.to_be_bytes());
    for chunk in msg.chunks_exact(64) {
        let mut w = [0u32; 64];
        for (i, word) in chunk.chunks_exact(4).enumerate() {
            w[i] = u32::from_be_bytes([word[0], word[1], word[2], word[3]]);
        }
        for i in 16..64 {
            let s0 = w[i - 15].rotate_right(7) ^ w[i - 15].rotate_right(18) ^ (w[i - 15] >> 3);
            let s1 = w[i - 2].rotate_right(17) ^ w[i - 2].rotate_right(19) ^ (w[i - 2] >> 10);
            w[i] = w[i - 16]
                .wrapping_add(s0)
                .wrapping_add(w[i - 7])
                .wrapping_add(s1);
        }
        let [mut a, mut b, mut c, mut d, mut e, mut f, mut g, mut hh] = h;
        for i in 0..64 {
            let s1 = e.rotate_right(6) ^ e.rotate_right(11) ^ e.rotate_right(25);
            let ch = (e & f) ^ (!e & g);
            let t1 = hh
                .wrapping_add(s1)
                .wrapping_add(ch)
                .wrapping_add(K[i])
                .wrapping_add(w[i]);
            let s0 = a.rotate_right(2) ^ a.rotate_right(13) ^ a.rotate_right(22);
            let maj = (a & b) ^ (a & c) ^ (b & c);
            let t2 = s0.wrapping_add(maj);
            hh = g;
            g = f;
            f = e;
            e = d.wrapping_add(t1);
            d = c;
            c = b;
            b = a;
            a = t1.wrapping_add(t2);
        }
        for (slot, v) in h.iter_mut().zip([a, b, c, d, e, f, g, hh]) {
            *slot = slot.wrapping_add(v);
        }
    }
    h.iter().map(|w| format!("{w:08x}")).collect()
}

const WRAP_NAME: &str = "__sysmlStructure__";

/// The id-normalized structural digest of exactly one member's text
/// (top-level form, as the canonical formatter emits it). Errors name
/// the first parse diagnostic or the member-count violation.
///
/// The error is a message rather than a type because every caller shows
/// it and none branches on it: a digest either describes the text or the
/// text is not one member.
pub fn member_structure_digest(member_text: &str) -> Result<String, String> {
    let probe = format!("package {WRAP_NAME} {{\n{member_text}\n}}");
    let parse = parse_source(&probe);
    if let Some(d) = parse.diagnostics.first() {
        return Err(d.message.clone());
    }
    let mut unit = parse.unit;
    unit.dialect = Dialect::Sysml;
    let doc = crate::json::to_compact_json(&unit);
    let nodes = doc
        .as_array()
        .ok_or("compact serialization is not an array")?;
    let by_id: std::collections::HashMap<&str, &Value> = nodes
        .iter()
        .filter_map(|n| Some((n.get("@id")?.as_str()?, n)))
        .collect();
    // Wrapper package → its owned memberships → exactly one member root.
    let wrapper = nodes
        .iter()
        .find(|n| n.get("declaredName").and_then(Value::as_str) == Some(WRAP_NAME))
        .ok_or("wrapper package missing from serialization")?;
    let mut member_roots: Vec<&str> = Vec::new();
    for rel in relation_ids(wrapper, "ownedRelationship") {
        let Some(rel_node) = by_id.get(rel).copied() else {
            continue;
        };
        member_roots.extend(relation_ids(rel_node, "ownedRelatedElement"));
    }
    let [root_id] = member_roots[..] else {
        return Err(format!(
            "a member digest covers exactly one top-level member, found {}",
            member_roots.len()
        ));
    };

    // Visit in document order, minting local ordinals.
    let mut local: std::collections::HashMap<String, String> = Default::default();
    let mut ordered: Vec<&Value> = Vec::new();
    let mut stack = vec![root_id.to_string()];
    while let Some(id) = stack.pop() {
        if local.contains_key(&id) {
            continue;
        }
        let Some(node) = by_id.get(id.as_str()).copied() else {
            continue;
        };
        local.insert(id.clone(), format!("${}", local.len()));
        ordered.push(node);
        // Depth-first document order with a stack: push children reversed.
        let mut pending: Vec<String> = Vec::new();
        for rel in relation_ids(node, "ownedRelationship") {
            pending.push(rel.to_string());
            if let Some(rel_node) = by_id.get(rel).copied() {
                for child in relation_ids(rel_node, "ownedRelatedElement") {
                    pending.push(child.to_string());
                }
            }
        }
        for id in pending.into_iter().rev() {
            stack.push(id);
        }
    }

    let normalized: Vec<Value> = ordered
        .iter()
        .map(|node| normalize(node, &local, root_id))
        .collect();
    let bytes = serde_json::to_string(&normalized).map_err(|e| e.to_string())?;
    Ok(format!("sha256:{}", sha256_hex(bytes.as_bytes())))
}

fn relation_ids<'v>(node: &'v Value, key: &str) -> Vec<&'v str> {
    node.get(key)
        .and_then(Value::as_array)
        .map(|items| {
            items
                .iter()
                .filter_map(|r| r.get("@id")?.as_str())
                .collect()
        })
        .unwrap_or_default()
}

fn map_id(id: &str, local: &std::collections::HashMap<String, String>) -> String {
    local
        .get(id)
        .cloned()
        .unwrap_or_else(|| format!("external:{id}"))
}

fn normalize(
    value: &Value,
    local: &std::collections::HashMap<String, String>,
    root_id: &str,
) -> Value {
    match value {
        Value::Array(items) => {
            Value::Array(items.iter().map(|v| normalize(v, local, root_id)).collect())
        }
        Value::Object(object) => {
            if object.len() == 1 {
                if let Some(id) = object.get("@id").and_then(Value::as_str) {
                    let mut one = Map::new();
                    one.insert("@id".into(), Value::String(map_id(id, local)));
                    return Value::Object(one);
                }
            }
            let is_root = object.get("@id").and_then(Value::as_str) == Some(root_id);
            let mut out = Map::new();
            for (key, child) in object {
                if is_root && key == "owningRelationship" {
                    continue;
                }
                if (key == "@id" || key == "elementId") && child.is_string() {
                    out.insert(
                        key.clone(),
                        Value::String(map_id(child.as_str().unwrap(), local)),
                    );
                } else {
                    out.insert(key.clone(), normalize(child, local, root_id));
                }
            }
            Value::Object(out)
        }
        other => other.clone(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn sha256_test_vectors() {
        assert_eq!(
            sha256_hex(b"abc"),
            "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
        );
    }

    #[test]
    fn digest_is_spelling_independent_but_structure_sensitive() {
        let a = member_structure_digest("part def <'R-1'> beam {\n\tdoc /* d */\n}").unwrap();
        let b = member_structure_digest("part def <'R-1'> beam { doc /* d */ }").unwrap();
        assert_eq!(a, b, "whitespace-only respellings agree");
        let c = member_structure_digest("part def <'R-1'> beam {\n\tdoc /* e */\n}").unwrap();
        assert_ne!(a, c, "content changes disagree");
        let d = member_structure_digest("part def <'R-2'> beam {\n\tdoc /* d */\n}").unwrap();
        assert_ne!(a, d, "identity changes disagree");
    }

    #[test]
    fn digest_is_wrapper_and_position_independent() {
        // Unresolved outward references ride @ref spellings; the digest
        // is a function of the member text alone.
        let a = member_structure_digest("part def B { part x : Outside; }").unwrap();
        let b = member_structure_digest("part def B { part x : Outside; }").unwrap();
        assert_eq!(a, b);
    }

    #[test]
    fn refuses_multi_member_and_broken_text() {
        assert!(member_structure_digest("part def A; part def B;").is_err());
        assert!(member_structure_digest("part def {").is_err());
    }
}
