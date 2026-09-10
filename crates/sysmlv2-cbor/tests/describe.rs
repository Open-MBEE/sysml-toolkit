//! Describe gate: `describe` agrees with the encoders across every
//! payload form, and malformed bytes yield clean errors, never a
//! panic.

use serde_json::Value;
use sysmlv2_cbor::{
    DeltaOptions, delta_compact_cbor, describe, state_digest, to_compact_cbor,
    to_compact_cbor_elided, to_full_cbor,
};
use sysmlv2_parser::json::model_to_compact_json;
use sysmlv2_parser::model::Model;

fn compact_of(src: &str) -> Value {
    let mut model = Model::new();
    model.add_source("m.sysml".to_string(), src);
    model_to_compact_json(&model)
}

const BASE: &str = "package P { part def V { attribute total; } part v : V; part def W; }";
const TARGET: &str = "package P { part def V { attribute renamed; } part v : V; part def N; }";

#[test]
fn snapshot_summaries_agree_with_the_encoders() {
    let compact = compact_of(BASE);
    let n = compact.as_array().unwrap().len();

    let plain = to_compact_cbor(&compact).unwrap();
    let d = describe(&plain).unwrap();
    assert_eq!(d["form"], "compact");
    assert_eq!(d["elements"], n);
    assert_eq!(d["idsElided"], false);
    assert_eq!(d["bytes"], plain.len());
    assert_eq!(d["versions"]["supported"], true);
    assert_eq!(d["versions"]["layout"], 1);

    let elided = to_compact_cbor_elided(&compact, &|_| None).unwrap();
    let d = describe(&elided).unwrap();
    assert_eq!(d["form"], "compact");
    assert_eq!(d["idsElided"], true);
    assert_eq!(d["elements"], n);
    assert_eq!(d["exceptions"], 1, "one assigned root per unit");
    assert!(d["idDigest"].is_string());

    let mut model = Model::new();
    model.add_source("m.sysml".to_string(), BASE);
    let full = sysmlv2_parser::full::model_to_full_json_with(&model, false);
    let full_bytes = to_full_cbor(&full).unwrap();
    let d = describe(&full_bytes).unwrap();
    assert_eq!(d["form"], "full");
    assert_eq!(d["elements"], full.as_array().unwrap().len());
}

#[test]
fn delta_summaries_expose_digests_claims_and_changes() {
    let base = compact_of(BASE);
    let target = compact_of(TARGET);
    for portable in [false, true] {
        let opts = DeltaOptions {
            portable,
            claims: vec![(1, sysmlv2_cbor::Claim::Id(uuid::Uuid::nil()))],
            ..Default::default()
        };
        let bytes = delta_compact_cbor(&base, &target, &opts).unwrap();
        let d = describe(&bytes).unwrap();
        assert_eq!(d["form"], "delta");
        assert_eq!(
            d["delta"]["identityMode"],
            if portable { "portable" } else { "strict" }
        );
        assert_eq!(
            d["delta"]["baseDigest"].as_str().unwrap(),
            state_digest(&base).unwrap().to_string()
        );
        assert_eq!(
            d["delta"]["resultDigest"].as_str().unwrap(),
            state_digest(&target).unwrap().to_string()
        );
        assert_eq!(d["delta"]["claims"][0]["key"], 1);
        let ch = &d["delta"]["changes"];
        assert!(ch["creates"].as_u64().unwrap() >= 1, "{ch}");
        assert!(ch["deletes"].as_u64().unwrap() >= 1, "{ch}");
        assert!(ch["updates"].as_u64().unwrap() >= 1, "{ch}");
        assert_eq!(
            d["delta"]["createdIds"].as_array().unwrap().len() as u64,
            d["delta"]["created"].as_u64().unwrap()
        );
        assert_eq!(d["delta"]["targetsTruncated"], false);
    }
}

#[test]
fn mutated_payloads_never_panic_under_describe() {
    let base = compact_of(BASE);
    let target = compact_of(TARGET);
    for bytes in [
        to_compact_cbor(&base).unwrap(),
        to_compact_cbor_elided(&base, &|_| None).unwrap(),
        delta_compact_cbor(&base, &target, &Default::default()).unwrap(),
    ] {
        for i in 0..bytes.len() {
            let mut bad = bytes.clone();
            bad[i] ^= 0x01;
            let _ = describe(&bad);
        }
        for cut in 0..bytes.len() {
            let _ = describe(&bytes[..cut]);
        }
    }
}
