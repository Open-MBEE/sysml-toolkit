//! Full-form gate: full-form CBOR is an emit view — `to_full_cbor` encodes
//! the materialized element list (derived properties included) in its
//! own ordinal space, and `from_full_cbor` reproduces the exact full
//! JSON `Value`. Compact and full payloads refuse each other's
//! decoders.

use serde_json::Value;
use std::fs;
use std::path::PathBuf;
use sysmlv2_cbor::{from_compact_cbor, from_full_cbor, to_full_cbor};
use sysmlv2_parser::full::model_to_full_json_with;
use sysmlv2_parser::model::Model;

fn golden_model() -> Model {
    let dir = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../sysmlv2-parser/tests/goldens");
    let mut fixtures: Vec<PathBuf> = fs::read_dir(&dir)
        .unwrap()
        .flatten()
        .map(|e| e.path())
        .filter(|p| {
            matches!(
                p.extension().and_then(|e| e.to_str()),
                Some("sysml" | "kerml")
            )
        })
        .collect();
    fixtures.sort();
    assert!(fixtures.len() >= 4);
    let mut model = Model::new();
    for path in &fixtures {
        model.add_source(
            path.file_name().unwrap().to_string_lossy().into_owned(),
            &fs::read_to_string(path).unwrap(),
        );
    }
    model
}

#[test]
fn full_form_round_trips_value_identical() {
    let model = golden_model();
    for recover_refs in [false, true] {
        let full = model_to_full_json_with(&model, recover_refs);
        let n = full.as_array().unwrap().len();
        assert!(n >= 1362, "full corpus present ({n} elements)");
        let bytes = to_full_cbor(&full)
            .unwrap_or_else(|e| panic!("encode (recover_refs={recover_refs}): {e}"));
        let back = from_full_cbor(&bytes)
            .unwrap_or_else(|e| panic!("decode (recover_refs={recover_refs}): {e}"));
        assert_eq!(back, full, "recover_refs={recover_refs}");
    }
}

#[test]
fn full_uses_wide_presence_and_stays_dense() {
    let model = golden_model();
    let full = model_to_full_json_with(&model, false);
    let bytes = to_full_cbor(&full).unwrap();
    let minified = serde_json::to_string(&full).unwrap();
    // Full form materializes ~5x the properties; the presence bitmap
    // keeps the density win in the same league as compact.
    assert!(
        bytes.len() * 6 < minified.len(),
        "full CBOR ({}) at least 6x under minified full JSON ({})",
        bytes.len(),
        minified.len()
    );
}

#[test]
fn forms_refuse_each_others_decoder() {
    let model = golden_model();
    let full = model_to_full_json_with(&model, false);
    let full_bytes = to_full_cbor(&full).unwrap();
    let err = from_compact_cbor(&full_bytes).unwrap_err().to_string();
    assert!(err.contains("full-form"), "{err}");

    let compact: Value = sysmlv2_parser::json::model_to_compact_json(&model);
    let compact_bytes = sysmlv2_cbor::to_compact_cbor(&compact).unwrap();
    let err = from_full_cbor(&compact_bytes).unwrap_err().to_string();
    assert!(err.contains("compact"), "{err}");

    // from_cbor takes either.
    assert_eq!(sysmlv2_cbor::from_cbor(&full_bytes).unwrap(), full);
    assert_eq!(sysmlv2_cbor::from_cbor(&compact_bytes).unwrap(), compact);
}
