//! Round-trip gate: `from_compact_cbor(to_compact_cbor(v)) == v`
//! (Value-identical) for every golden element array, size sanity, and
//! clean errors on malformed inputs.

use serde_json::{Value, json};
use std::fs;
use std::path::PathBuf;
use sysmlv2_cbor::{FLAG_ELIDE_IDS, from_compact_cbor, to_compact_cbor};
use sysmlv2_parser::json::to_compact_json;
use sysmlv2_parser::parser::parse_source;

fn goldens() -> Vec<(String, Value)> {
    let dir =
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../sysmlv2-parser/tests/goldens/expected");
    let mut out = Vec::new();
    for entry in fs::read_dir(dir).expect("goldens/expected exists") {
        let path = entry.unwrap().path();
        if path.extension().and_then(|e| e.to_str()) != Some("json") {
            continue;
        }
        let v = serde_json::from_str(&fs::read_to_string(&path).unwrap()).unwrap();
        out.push((path.file_name().unwrap().to_string_lossy().into_owned(), v));
    }
    assert!(out.len() >= 150, "corpus present");
    out
}

#[test]
fn goldens_round_trip_value_identical() {
    for (name, v) in goldens() {
        let bytes = to_compact_cbor(&v).unwrap_or_else(|e| panic!("{name}: encode: {e}"));
        let back = from_compact_cbor(&bytes).unwrap_or_else(|e| panic!("{name}: decode: {e}"));
        assert_eq!(back, v, "{name}: round-trip is Value-identical");
    }
}

#[test]
fn triggered_accept_payload_graph_round_trips_value_identical() {
    let parsed = parse_source("package P { action a { accept sig at clock; } }");
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let compact = to_compact_json(&parsed.unit);
    let bytes = to_compact_cbor(&compact).expect("encode corrected accept graph");
    assert_eq!(
        from_compact_cbor(&bytes).expect("decode corrected accept graph"),
        compact
    );
}

#[test]
fn payload_is_smaller_than_minified_json() {
    let mut json_total = 0usize;
    let mut cbor_total = 0usize;
    for (_, v) in goldens() {
        json_total += serde_json::to_string(&v).unwrap().len();
        cbor_total += to_compact_cbor(&v).unwrap().len();
    }
    assert!(
        cbor_total * 4 < json_total,
        "CBOR ({cbor_total} B) at least 4x under minified JSON ({json_total} B)"
    );
}

#[test]
fn encode_rejects_non_compact_shapes() {
    for bad in [
        json!({}),
        json!([{"@type": "NoSuchMetaclass", "@id": "64126415-ee0c-539b-86b6-247ae20f892b"}]),
        json!([{"@type": "Package", "@id": "not-a-uuid"}]),
        json!([{"@type": "Package", "@id": "64126415-ee0c-539b-86b6-247ae20f892b",
                "owner": {"@id": "64126415-ee0c-539b-86b6-247ae20f892b"}}]),
        json!([{"@type": "Package", "@id": "64126415-ee0c-539b-86b6-247ae20f892b",
                "isAbstract": "yes"}]),
    ] {
        assert!(to_compact_cbor(&bad).is_err(), "rejects {bad}");
    }
}

#[test]
fn decode_rejects_malformed_payloads() {
    let good = to_compact_cbor(&json!([
        {"@type": "Package", "@id": "64126415-ee0c-539b-86b6-247ae20f892b",
         "declaredName": "P", "elementId": "64126415-ee0c-539b-86b6-247ae20f892b",
         "isImpliedIncluded": false, "ownedRelationship": [], "owningRelationship": null}
    ]))
    .unwrap();
    assert!(from_compact_cbor(&good).is_ok());

    // Every strict prefix errors cleanly (truncation never panics).
    for cut in 0..good.len() {
        assert!(
            from_compact_cbor(&good[..cut]).is_err(),
            "prefix {cut} errors"
        );
    }
    // Trailing garbage.
    let mut extra = good.clone();
    extra.push(0x00);
    assert!(from_compact_cbor(&extra).is_err());
    // A missing magic prefix is refused by name.
    let err = from_compact_cbor(&good[8..]).unwrap_err().to_string();
    assert!(err.contains("$S2C"), "{err}");
    // The header word sits after 8 magic bytes + `array(5)` (the
    // owner-exception section under FLAG_IMPLIED_OWNERS): uint64 head
    // (0x1B) then 8 BE bytes — zeros, layout at [13], tables at
    // [14..16], scheme at [16], flags at [17].
    assert_eq!(&good[8..10], &[0x85, 0x1B]);
    // Unknown layout version refuses by name.
    let mut wrong_layout = good.clone();
    wrong_layout[13] = 0xFF;
    let err = from_compact_cbor(&wrong_layout).unwrap_err().to_string();
    assert!(err.contains("layout version"), "{err}");
    // Unknown table version refuses by name.
    let mut wrong_tables = good.clone();
    wrong_tables[14] = 0xFF;
    let err = from_compact_cbor(&wrong_tables).unwrap_err().to_string();
    assert!(err.contains("table version"), "{err}");
    // The scheme axis gates only payloads that derive ids: a foreign
    // scheme stamp on an explicit-id payload still decodes…
    let mut odd_scheme = good.clone();
    odd_scheme[16] = 0xFF;
    assert!(from_compact_cbor(&odd_scheme).is_ok());
    // The id-elision flag needs the resolver-aware decoder.
    let mut elided = good;
    elided[17] |= FLAG_ELIDE_IDS;
    let err = from_compact_cbor(&elided).unwrap_err().to_string();
    assert!(
        err.contains("id-elided"),
        "elision flag names itself: {err}"
    );
}

#[test]
fn library_export_round_trips_value_identical() {
    // The resolved standard library as a payload (`--library`): encode
    // → decode must reproduce the exported element array exactly, so
    // the library's state digest is one digest however it travels.
    // Skips when the normative library is not checked out.
    let lib = sysmlv2_testkit::library_dir();
    if !lib.exists() {
        eprintln!("skipping: library not present");
        return;
    }
    let mut model = sysmlv2_parser::model::Model::new();
    model.load_library_dir(&lib).expect("library loads");
    let (json, units) = sysmlv2_parser::json::library_to_compact_json_with_units(&model);
    let bytes = sysmlv2_cbor::to_compact_cbor_with_units(&json, &units).expect("encodes");
    let (decoded, decoded_units) =
        sysmlv2_cbor::from_cbor_with_units(&bytes, &|_| None).expect("decodes");
    let units_u64: Vec<(u64, String)> = units.iter().map(|(i, p)| (*i as u64, p.clone())).collect();
    assert_eq!(decoded_units, units_u64, "unit table survives");
    let (a, b) = (json.as_array().unwrap(), decoded.as_array().unwrap());
    assert_eq!(a.len(), b.len());
    for (i, (x, y)) in a.iter().zip(b).enumerate() {
        if x != y {
            for (k, vx) in x.as_object().unwrap() {
                let vy = &y[k];
                if vx != vy {
                    panic!(
                        "element {i} ({} {}) field {k}: exported {vx} != decoded {vy}",
                        x["@type"], x["@id"]
                    );
                }
            }
            panic!("element {i}: key sets differ:\n{x}\n{y}");
        }
    }
    assert_eq!(
        sysmlv2_cbor::state_digest(&json).unwrap(),
        sysmlv2_cbor::state_digest(&decoded).unwrap()
    );
}

#[test]
fn json_text_round_trip_preserves_the_state_digest() {
    // Exact float parsing (workspace serde_json `float_roundtrip`):
    // the default fast path parses e.g. "1e-28" one ULP off the f64
    // the emitter printed, silently splitting the state digest between
    // a payload that traveled as JSON text and the same payload as
    // binary. The real standard library carries such values
    // (conversion factors 1.0e-28, 1.0e-24).
    let payload = serde_json::json!([
        {
            "@type": "LiteralRational",
            "@id": "00000000-0000-0000-0000-000000000001",
            "value": 1e-28,
        },
        {
            "@type": "LiteralRational",
            "@id": "00000000-0000-0000-0000-000000000002",
            "value": 1e-24,
        },
    ]);
    let text = serde_json::to_string_pretty(&payload).unwrap();
    let reparsed: Value = serde_json::from_str(&text).unwrap();
    assert_eq!(reparsed, payload, "text round trip is exact");
    assert_eq!(
        sysmlv2_cbor::state_digest(&reparsed).unwrap(),
        sysmlv2_cbor::state_digest(&payload).unwrap(),
        "one digest however the payload travels"
    );
}

#[test]
fn implied_owners_round_trip_every_deviation() {
    // Backpointers matching their derivation leave the wire and
    // re-materialize on decode; every deviant state — inconsistent
    // value, explicit null under an owner, absent key, `@ref` spelling,
    // duplicate claimants — still round-trips Value-identical.
    let pkg = |id: &str, owned: &[&str]| -> Value {
        json!({
            "@type": "Package", "@id": id, "elementId": id,
            "declaredName": "P", "isImpliedIncluded": false,
            "ownedRelationship": owned.iter().map(|o| json!({"@id": o})).collect::<Vec<_>>(),
            "owningRelationship": null,
        })
    };
    let mem = |id: &str, owner: Value| -> Value {
        let mut m = json!({
            "@type": "OwningMembership", "@id": id, "elementId": id,
            "isImplied": false, "isImpliedIncluded": false,
            "memberElement": {"@id": "11111111-1111-4111-8111-111111111111"},
            "visibility": "public",
            "ownedRelatedElement": [], "ownedRelationship": [],
        });
        if !owner.is_null() || owner == Value::Null {
            // owner slot spelled exactly as passed; Value::Null means
            // the key is present-as-null. An explicit marker string
            // "ABSENT" drops the key entirely.
        }
        if owner == json!("ABSENT") {
            return m;
        }
        m["owningRelatedElement"] = owner;
        m
    };
    let p1 = "00000000-0000-4000-8000-000000000001";
    let p2 = "00000000-0000-4000-8000-000000000002";
    let m1 = "00000000-0000-4000-8000-00000000000a";
    let consistent = json!({"@id": p1});
    let wrong = json!({"@id": "22222222-2222-4222-8222-222222222222"});
    let by_ref = json!({"@ref": "Some::Path"});
    for (name, owner_state) in [
        ("consistent-derived", consistent),
        ("inconsistent-value", wrong),
        ("explicit-null-under-owner", Value::Null),
        ("ref-spelled", by_ref),
        ("absent-key", json!("ABSENT")),
    ] {
        let payload = Value::Array(vec![pkg(p1, &[m1]), mem(m1, owner_state)]);
        let bytes = to_compact_cbor(&payload).unwrap_or_else(|e| panic!("{name}: encode: {e}"));
        let back = from_compact_cbor(&bytes).unwrap_or_else(|e| panic!("{name}: decode: {e}"));
        assert_eq!(back, payload, "{name}: Value-identical round trip");
    }
    // Duplicate claimants: two packages list the same membership;
    // the first in element order wins the derivation, so a backpointer
    // to the second spells explicitly. Both shapes round-trip.
    for owner_id in [p1, p2] {
        let payload = Value::Array(vec![
            pkg(p1, &[m1]),
            pkg(p2, &[m1]),
            mem(m1, json!({"@id": owner_id})),
        ]);
        let bytes = to_compact_cbor(&payload).unwrap();
        assert_eq!(
            from_compact_cbor(&bytes).unwrap(),
            payload,
            "claimant {owner_id}"
        );
    }
}

#[test]
fn digest_space_is_pinned_across_wire_revisions() {
    // The state digest canonicalizes with owners spelled, independent
    // of what the wire elides — this literal was recorded before
    // FLAG_IMPLIED_OWNERS existed and must never move.
    let payload = json!([{
        "@type": "Package", "@id": "64126415-ee0c-539b-86b6-247ae20f892b",
        "declaredName": "P", "elementId": "64126415-ee0c-539b-86b6-247ae20f892b",
        "isImpliedIncluded": false, "ownedRelationship": [],
        "owningRelationship": null,
    }]);
    assert_eq!(
        sysmlv2_cbor::state_digest(&payload).unwrap().to_string(),
        "4d2d226c-0d83-5bd7-81f9-7b366288ecbe",
    );
    // And the wire round trip of the same payload digests identically.
    let back = from_compact_cbor(&to_compact_cbor(&payload).unwrap()).unwrap();
    assert_eq!(
        sysmlv2_cbor::state_digest(&back).unwrap().to_string(),
        "4d2d226c-0d83-5bd7-81f9-7b366288ecbe",
    );
}

/// Callers act on the error classes differently — refetch a base,
/// fetch a resolver, route to another entry point, give up on the
/// bytes — so each class is reachable and says which it is. The
/// `Display` text stays the explanation.
#[test]
fn errors_classify_what_the_caller_should_do() {
    use sysmlv2_cbor::{
        DeltaOptions, ErrorKind, apply_delta_cbor, delta_compact_cbor, from_full_cbor,
        to_compact_cbor_elided,
    };
    let model = |name: &str| {
        let parsed = parse_source(&format!("package {name} {{ part def V; }}"));
        to_compact_json(&parsed.unit)
    };
    let one = model("P");
    let other = model("Q");
    let payload = to_compact_cbor(&one).unwrap();

    let kind = |e: sysmlv2_cbor::Error| e.kind();
    assert_eq!(
        kind(from_compact_cbor(b"not an s2c payload at all").unwrap_err()),
        ErrorKind::MissingMagic
    );
    // The header word sits right after the magic and the body's array
    // head, spelled as a full-width uint: its fourth byte is the wire
    // layout generation.
    let mut wrong_layout = payload.clone();
    wrong_layout[13] = 9;
    assert_eq!(
        kind(from_compact_cbor(&wrong_layout).unwrap_err()),
        ErrorKind::UnsupportedVersion
    );
    let elided = to_compact_cbor_elided(&one, &|_| None).unwrap();
    assert_eq!(
        kind(from_compact_cbor(&elided).unwrap_err()),
        ErrorKind::NeedsResolver
    );
    assert_eq!(
        kind(from_full_cbor(&payload).unwrap_err()),
        ErrorKind::WrongForm
    );
    let delta = delta_compact_cbor(&one, &other, &DeltaOptions::default()).unwrap();
    assert_eq!(
        kind(from_compact_cbor(&delta).unwrap_err()),
        ErrorKind::WrongForm
    );
    assert_eq!(
        kind(apply_delta_cbor(&delta, &other).unwrap_err()),
        ErrorKind::BaseDigestMismatch
    );
    assert_eq!(
        kind(from_compact_cbor(&payload[..payload.len() - 1]).unwrap_err()),
        ErrorKind::Truncated
    );
    let unknown =
        json!([{ "@type": "NotAMetaclass", "@id": "00000000-0000-4000-8000-000000000001" }]);
    let err = to_compact_cbor(&unknown).unwrap_err();
    assert!(err.to_string().contains("unknown @type"), "{err}");
    assert_eq!(kind(err), ErrorKind::Malformed);
}
