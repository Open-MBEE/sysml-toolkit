//! Canonicalization gate: a wire-elided spelling of a compact document
//! (schema-default fields dropped, as service producers do) and the
//! fully-spelled original canonicalize to the same document; the pass
//! is idempotent, preserves ids/order/non-default values, and rejects
//! non-compact shapes. Contrast gate: the CBOR round-trip stays
//! presence-faithful — canonicalize_compact is the only default
//! rehydrator.

use serde_json::{Map, Value, json};
use std::fs;
use std::path::PathBuf;
use sysmlv2_cbor::{
    canonicalize_compact, from_compact_cbor, graph_normalize, graph_normalize_compact,
    state_digest, to_compact_cbor,
};

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

/// The service-side wire elision: drop every field sitting at its
/// metaclass default — kept iff removing it would NOT canonicalize
/// back to the very same value.
fn elide_defaults(doc: &Value) -> Value {
    let elided: Vec<Value> = doc
        .as_array()
        .unwrap()
        .iter()
        .map(|el| {
            let obj = el.as_object().unwrap();
            let kept: Map<String, Value> = obj
                .iter()
                .filter(|(k, v)| {
                    if k.as_str() == "@id" || k.as_str() == "@type" {
                        return true;
                    }
                    let mut probe = obj.clone();
                    probe.remove(*k);
                    let canon: Value = serde_json::from_str(
                        &canonicalize_compact(
                            &Value::Array(vec![Value::Object(probe)]).to_string(),
                        )
                        .unwrap(),
                    )
                    .unwrap();
                    canon.as_array().unwrap()[0].get(*k) != Some(*v)
                })
                .map(|(k, v)| (k.clone(), v.clone()))
                .collect();
            Value::Object(kept)
        })
        .collect();
    Value::Array(elided)
}

#[test]
fn elided_and_spelled_canonicalize_identically() {
    let mut elided_something = 0usize;
    for (name, v) in goldens() {
        let spelled = canonicalize_compact(&v.to_string())
            .unwrap_or_else(|e| panic!("{name}: canonicalize: {e}"));
        let wire = elide_defaults(&v);
        if wire.to_string().len() < v.to_string().len() {
            elided_something += 1;
        }
        let from_wire = canonicalize_compact(&wire.to_string())
            .unwrap_or_else(|e| panic!("{name}: canonicalize elided: {e}"));
        assert_eq!(spelled, from_wire, "{name}: elision split is bridged");
        let again = canonicalize_compact(&spelled).unwrap();
        assert_eq!(spelled, again, "{name}: idempotent");
    }
    assert!(elided_something >= 100, "the elision simulation bites");
}

#[test]
fn canonical_form_only_adds_defaults() {
    for (name, v) in goldens() {
        let canon: Value =
            serde_json::from_str(&canonicalize_compact(&v.to_string()).unwrap()).unwrap();
        let (input, output) = (v.as_array().unwrap(), canon.as_array().unwrap());
        assert_eq!(input.len(), output.len(), "{name}: element count");
        for (el, canon_el) in input.iter().zip(output) {
            let (el, canon_el) = (el.as_object().unwrap(), canon_el.as_object().unwrap());
            assert_eq!(el["@id"], canon_el["@id"], "{name}: id preserved");
            assert_eq!(el["@type"], canon_el["@type"], "{name}: type preserved");
            for (k, val) in el {
                assert_eq!(
                    Some(val),
                    canon_el.get(k),
                    "{name}: present value {k} preserved verbatim"
                );
            }
        }
    }
}

#[test]
fn defaults_spell_per_metaclass() {
    // isUnique defaults TRUE on features, isAbstract FALSE, an
    // OwningMembership's visibility "public", elementId mirrors @id.
    let doc = json!([
        {"@type": "PartUsage", "@id": "64126415-ee0c-539b-86b6-247ae20f892b"},
        {"@type": "OwningMembership", "@id": "0e3e6d3c-9a9b-5a3e-8f26-1c1a2b3c4d5e"},
    ]);
    let canon: Value =
        serde_json::from_str(&canonicalize_compact(&doc.to_string()).unwrap()).unwrap();
    let part = canon.as_array().unwrap()[0].as_object().unwrap();
    assert_eq!(part["isUnique"], json!(true));
    assert_eq!(part["isAbstract"], json!(false));
    assert_eq!(part["declaredName"], Value::Null);
    assert_eq!(part["ownedRelationship"], json!([]));
    assert_eq!(
        part["elementId"],
        json!("64126415-ee0c-539b-86b6-247ae20f892b")
    );
    let mem = canon.as_array().unwrap()[1].as_object().unwrap();
    assert_eq!(mem["visibility"], json!("public"));
    // A spelled non-default survives; a spelled default is untouched.
    let doc = json!([
        {"@type": "PartUsage", "@id": "64126415-ee0c-539b-86b6-247ae20f892b",
         "isUnique": false, "isAbstract": false},
    ]);
    let canon: Value =
        serde_json::from_str(&canonicalize_compact(&doc.to_string()).unwrap()).unwrap();
    let part = canon.as_array().unwrap()[0].as_object().unwrap();
    assert_eq!(part["isUnique"], json!(false));
    assert_eq!(part["isAbstract"], json!(false));
}

#[test]
fn cbor_round_trip_stays_presence_faithful() {
    // The contrast pinning why this entry point exists: encode/decode
    // preserves the elided-vs-spelled split; canonicalize closes it.
    let elided = json!([
        {"@type": "PartUsage", "@id": "64126415-ee0c-539b-86b6-247ae20f892b"},
    ]);
    let back = from_compact_cbor(&to_compact_cbor(&elided).unwrap()).unwrap();
    assert!(back.as_array().unwrap()[0].get("isUnique").is_none());
    let canon: Value =
        serde_json::from_str(&canonicalize_compact(&back.to_string()).unwrap()).unwrap();
    assert_eq!(canon.as_array().unwrap()[0]["isUnique"], json!(true));
}

#[test]
fn graph_normal_twin_respells_the_stored_form() {
    // A maximally spelled document (defaults explicit, backpointers
    // absent, unsorted): the graph-normal spelling elides the
    // defaults, spells elementId, derives first-claimant ownership
    // backpointers from the forward lists, and sorts by @id.
    let pkg = "00000000-0000-4000-8000-000000000002";
    let mem = "00000000-0000-4000-8000-000000000003";
    let part = "00000000-0000-4000-8000-000000000001";
    let doc = json!([
        {
            "@type": "Package", "@id": pkg,
            "declaredName": "Round", "isImpliedIncluded": false,
            "aliasIds": [], "ownedRelationship": [{"@id": mem}],
            "owningRelationship": null
        },
        {
            "@type": "OwningMembership", "@id": mem,
            "visibility": "public", "isImplied": false,
            "ownedRelatedElement": [{"@id": part}],
            "source": [{"@id": pkg}], "target": [{"@id": part}]
        },
        {
            "@type": "PartUsage", "@id": part,
            "declaredName": "wheel", "isUnique": true, "isAbstract": true
        }
    ]);
    let normal: Value =
        serde_json::from_str(&graph_normalize_compact(&doc.to_string()).unwrap()).unwrap();
    let arr = normal.as_array().unwrap();
    // Sorted by @id: part < pkg < mem.
    assert_eq!(arr[0]["@id"], json!(part));
    assert_eq!(arr[1]["@id"], json!(pkg));
    assert_eq!(arr[2]["@id"], json!(mem));
    let part_el = arr[0].as_object().unwrap();
    // Spelled defaults elided, non-defaults kept, elementId spelled.
    assert!(part_el.get("isUnique").is_none(), "true default elided");
    assert_eq!(part_el["isAbstract"], json!(true), "non-default kept");
    assert_eq!(part_el["elementId"], json!(part), "elementId spelled");
    // Backpointers derived first-claimant from the forward lists.
    assert_eq!(part_el["owningRelationship"]["@id"], json!(mem));
    let mem_el = arr[2].as_object().unwrap();
    assert_eq!(mem_el["owningRelatedElement"]["@id"], json!(pkg));
    assert!(
        mem_el.get("visibility").is_none(),
        "default enum value elided"
    );
    let pkg_el = arr[1].as_object().unwrap();
    assert!(
        pkg_el.get("owningRelationship").is_none(),
        "an unclaimed root derives no backpointer (the spelled null was a default)"
    );
    assert!(pkg_el.get("aliasIds").is_none(), "empty list elided");
    assert!(
        pkg_el.get("isImpliedIncluded").is_none(),
        "false default elided"
    );
    // Idempotent, and the fully spelled twin lands in the same cell.
    let again = graph_normalize(&normal).unwrap();
    assert_eq!(again, normal, "idempotent");
    let spelled: Value =
        serde_json::from_str(&canonicalize_compact(&normal.to_string()).unwrap()).unwrap();
    assert_eq!(
        graph_normalize(&spelled).unwrap(),
        normal,
        "canonicalized spelling graph-normalizes back exactly"
    );
    assert_eq!(
        state_digest(&graph_normalize(&spelled).unwrap()).unwrap(),
        state_digest(&normal).unwrap(),
        "one digest cell for both spellings"
    );
}

#[test]
fn graph_normal_keeps_explicit_backpointers_and_drops_derived_props() {
    let a = "00000000-0000-4000-8000-00000000000a";
    let b = "00000000-0000-4000-8000-00000000000b";
    // An explicitly spelled backpointer stays verbatim even when no
    // forward list claims it; a derived canonical property (`owner`)
    // drops like a store's ingest drops it — where canonicalize
    // rejects it (gated below in rejects_non_compact_shapes).
    let doc = json!([
        {
            "@type": "PartUsage", "@id": a,
            "owningRelationship": {"@id": b},
            "owner": {"@id": b},
            "qualifiedName": "Round::wheel"
        }
    ]);
    let normal = graph_normalize(&doc).unwrap();
    let el = normal.as_array().unwrap()[0].as_object().unwrap();
    assert_eq!(el["owningRelationship"]["@id"], json!(b));
    assert!(el.get("owner").is_none());
    assert!(el.get("qualifiedName").is_none());
    // A key outside even the full schema is still an error.
    let bad = json!([
        {"@type": "PartUsage", "@id": a, "notAProperty": 1}
    ]);
    assert!(graph_normalize(&bad).is_err());
}

#[test]
fn graph_normal_and_canonical_collapse_the_corpus_into_one_cell() {
    // Over the whole golden corpus: the graph-normal twin absorbs the
    // spelling split exactly like canonicalize does, from the other
    // side — graph_normalize(canonicalize(D)) == graph_normalize(D),
    // idempotent, and one state digest per document across spellings.
    for (name, v) in goldens() {
        let normal = graph_normalize(&v).unwrap_or_else(|e| panic!("{name}: graph_normalize: {e}"));
        let again = graph_normalize(&normal).unwrap();
        assert_eq!(again, normal, "{name}: idempotent");
        let spelled: Value =
            serde_json::from_str(&canonicalize_compact(&v.to_string()).unwrap()).unwrap();
        let from_spelled = graph_normalize(&spelled)
            .unwrap_or_else(|e| panic!("{name}: graph_normalize spelled: {e}"));
        assert_eq!(
            from_spelled, normal,
            "{name}: the spelling domains collapse"
        );
        let from_wire = graph_normalize(&elide_defaults(&v))
            .unwrap_or_else(|e| panic!("{name}: graph_normalize elided: {e}"));
        assert_eq!(from_wire, normal, "{name}: wire elision collapses too");
    }
}

#[test]
fn rejects_non_compact_shapes() {
    for (bad, why) in [
        (json!({}), "not an array"),
        (
            json!([{"@id": "64126415-ee0c-539b-86b6-247ae20f892b"}]),
            "missing @type",
        ),
        (
            json!([{"@type": "NoSuchMetaclass", "@id": "64126415-ee0c-539b-86b6-247ae20f892b"}]),
            "unknown metaclass",
        ),
        (json!([{"@type": "Package"}]), "missing @id"),
        (
            json!([{"@type": "Package", "@id": "64126415-ee0c-539b-86b6-247ae20f892b",
                 "owner": {"@id": "64126415-ee0c-539b-86b6-247ae20f892b"}}]),
            "derived property",
        ),
    ] {
        assert!(
            canonicalize_compact(&bad.to_string()).is_err(),
            "rejects {why}: {bad}"
        );
    }
}
