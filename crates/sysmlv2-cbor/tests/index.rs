//! Base-index gates: the compact base index + resolved delta records are a
//! faithful stand-in for a materialized base — resolving + transitioning
//! must agree with `apply_delta_cbor` end to end.

use serde_json::Value;
use sysmlv2_cbor::index::{BaseIndex, RecordPayload, resolve_strict_delta};
use sysmlv2_cbor::{DeltaOptions, apply_delta_cbor, delta_compact_cbor};
use sysmlv2_parser::json::model_to_compact_json;
use sysmlv2_parser::model::Model;

fn compact_of(src: &str) -> Value {
    let mut model = Model::new();
    model.add_source("m.sysml".to_string(), src);
    model_to_compact_json(&model)
}

fn differential(base_src: &str, target_src: &str) -> (BaseIndex, BaseIndex) {
    let base = compact_of(base_src);
    let target = compact_of(target_src);
    let bytes = delta_compact_cbor(&base, &target, &DeltaOptions::default()).unwrap();
    let index = BaseIndex::from_compact(&base).unwrap();
    let resolved = resolve_strict_delta(&bytes, &index).unwrap();
    let transitioned = resolved.transition(&index).unwrap();
    let applied = apply_delta_cbor(&bytes, &base).unwrap();
    (transitioned, BaseIndex::from_compact(&applied).unwrap())
}

const BASE: &str = "package P {
    part def V { attribute total; }
    part v : V;
    part def W;
}";

#[test]
fn transition_matches_apply_for_mixed_changes() {
    // Creates + updates + deletes + (planner's choice of) patches.
    let (got, want) = differential(
        BASE,
        "package P {
            part def V { attribute renamed; }
            part v : V;
            part def N { attribute x; }
        }",
    );
    assert_eq!(got, want);
}

#[test]
fn transition_matches_apply_for_reparent_and_growth() {
    let (got, want) = differential(
        BASE,
        "package P {
            part def V { attribute total; attribute extra; }
            part def Q { part v : V; }
            part def W;
        }",
    );
    assert_eq!(got, want);
}

#[test]
fn transition_matches_apply_from_the_empty_base() {
    let empty = Value::Array(Vec::new());
    let target = compact_of(BASE);
    let bytes = delta_compact_cbor(&empty, &target, &DeltaOptions::default()).unwrap();
    let index = BaseIndex::from_compact(&empty).unwrap();
    let resolved = resolve_strict_delta(&bytes, &index).unwrap();
    let transitioned = resolved.transition(&index).unwrap();
    let applied = apply_delta_cbor(&bytes, &empty).unwrap();
    assert_eq!(transitioned, BaseIndex::from_compact(&applied).unwrap());
    assert!(
        resolved
            .records
            .iter()
            .all(|r| matches!(r.payload, RecordPayload::Element(_)))
    );
}

#[test]
fn record_semantics_match_describe() {
    let base = compact_of(BASE);
    let target = compact_of("package P { part def V { attribute total; } part v : V; }");
    let bytes = delta_compact_cbor(&base, &target, &DeltaOptions::default()).unwrap();
    let index = BaseIndex::from_compact(&base).unwrap();
    let resolved = resolve_strict_delta(&bytes, &index).unwrap();
    let d = sysmlv2_cbor::describe(&bytes).unwrap();
    let count = |p: fn(&RecordPayload) -> bool| -> u64 {
        resolved.records.iter().filter(|r| p(&r.payload)).count() as u64
    };
    assert_eq!(
        d["delta"]["changes"]["deletes"].as_u64().unwrap(),
        count(|p| matches!(p, RecordPayload::Delete)),
    );
    assert_eq!(resolved.base_digest.to_string(), d["delta"]["baseDigest"]);
    assert_eq!(
        resolved.result_digest.to_string(),
        d["delta"]["resultDigest"]
    );
}

#[test]
fn index_bytes_round_trip_and_tamper_detection() {
    let index = BaseIndex::from_compact(&compact_of(BASE)).unwrap();
    let bytes = index.to_bytes();
    assert_eq!(BaseIndex::from_bytes(&bytes).unwrap(), index);
    let mut bad = bytes.clone();
    let mid = bad.len() / 2;
    bad[mid] ^= 0x01;
    assert!(BaseIndex::from_bytes(&bad).is_err(), "checksum trips");
    let err = BaseIndex::from_bytes(&bytes[..bytes.len() - 1])
        .unwrap_err()
        .to_string();
    assert!(
        err.contains("checksum") || err.contains("truncated"),
        "{err}"
    );
}

#[test]
fn elided_created_id_deltas_are_out_of_index_scope() {
    let base = compact_of(BASE);
    let target = compact_of("package P { part def V { attribute total; } part def M; }");
    let bytes =
        sysmlv2_cbor::delta_compact_cbor_elided(&base, &target, &DeltaOptions::default(), &|_| {
            None
        })
        .unwrap();
    let index = BaseIndex::from_compact(&base).unwrap();
    let err = resolve_strict_delta(&bytes, &index)
        .unwrap_err()
        .to_string();
    assert!(err.contains("materialized base"), "{err}");
}
