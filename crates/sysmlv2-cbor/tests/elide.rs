//! Id-elision gates: id elision round-trips exactly (native, foreign, and
//! library-resolved payloads), the digest catches tampering as a hard
//! error, and non-resolver decoders refuse elided payloads cleanly.

use serde_json::Value;
use std::fs;
use std::path::PathBuf;
use sysmlv2_cbor::{
    from_cbor, from_compact_cbor, from_compact_cbor_elided, to_compact_cbor, to_compact_cbor_elided,
};
use sysmlv2_parser::json::{library_name_map, model_to_compact_json};
use sysmlv2_parser::model::Model;

fn golden_compact() -> (Value, usize) {
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
    let mut model = Model::new();
    for path in &fixtures {
        model.add_source(
            path.file_name().unwrap().to_string_lossy().into_owned(),
            &fs::read_to_string(path).unwrap(),
        );
    }
    (model_to_compact_json(&model), fixtures.len())
}

fn no_external(s: &str) -> Option<String> {
    panic!("unexpected external target {s}")
}

#[test]
fn elided_golden_corpus_round_trips_and_shrinks() {
    let (compact, units) = golden_compact();
    let n = compact.as_array().unwrap().len();
    let plain = to_compact_cbor(&compact).unwrap();
    let elided = to_compact_cbor_elided(&compact, &no_external).unwrap();
    // Only the roots (one per unit) ride in the exception map: the id
    // table's 17 bytes/element collapse to presence in the tree.
    assert!(
        plain.len() - elided.len() >= 15 * (n - units),
        "elided ({}) saves the id table over plain ({}) for {n} elements",
        elided.len(),
        plain.len()
    );
    let back = from_compact_cbor_elided(&elided, &no_external).unwrap();
    assert_eq!(back, compact, "elided round-trip is Value-identical");
}

#[test]
fn library_resolved_model_elides_to_roots_only() {
    let Some(files) = sysmlv2_testkit::apollo_files() else {
        eprintln!("skipping: end-to-end model submodule not initialized");
        return;
    };
    let mut model = Model::new();
    model
        .load_library_dir(&sysmlv2_testkit::library_dir())
        .unwrap();
    for f in &files {
        let src = fs::read_to_string(f).unwrap();
        model.add_source(f.file_name().unwrap().to_string_lossy().into_owned(), &src);
    }
    let compact = model_to_compact_json(&model);
    let names: std::collections::HashMap<String, String> = library_name_map(&model)
        .into_iter()
        .filter_map(|(id, segs)| segs.last().cloned().map(|n| (id.to_string(), n)))
        .collect();
    let resolver = |s: &str| names.get(s).cloned();
    let n = compact.as_array().unwrap().len();
    let plain = to_compact_cbor(&compact).unwrap();
    let elided = to_compact_cbor_elided(&compact, &resolver).unwrap();
    assert!(plain.len() - elided.len() >= 15 * (n - files.len()));
    let back = from_compact_cbor_elided(&elided, &resolver).unwrap();
    assert_eq!(back, compact);
}

#[test]
fn foreign_ids_land_in_exceptions_and_still_round_trip() {
    let (mut compact, _) = golden_compact();
    // Re-badge a handful of elements with foreign ids (references left
    // dangling on purpose — the payload must reproduce exactly anyway).
    for (i, e) in compact
        .as_array_mut()
        .unwrap()
        .iter_mut()
        .enumerate()
        .take(40)
    {
        if i.is_multiple_of(3) {
            let foreign = format!("{:08x}-1234-4abc-8def-{:012x}", i, i * 7 + 1);
            e["@id"] = Value::String(foreign.clone());
            e["elementId"] = Value::String(foreign);
        }
    }
    let elided = to_compact_cbor_elided(&compact, &no_external).unwrap();
    let back = from_compact_cbor_elided(&elided, &no_external).unwrap();
    assert_eq!(back, compact);
}

#[test]
fn tampering_fails_the_digest_hard() {
    let (compact, _) = golden_compact();
    let elided = to_compact_cbor_elided(&compact, &no_external).unwrap();
    let original_ids: Vec<&str> = compact
        .as_array()
        .unwrap()
        .iter()
        .map(|e| e["@id"].as_str().unwrap())
        .collect();
    // Flip one bit at a time across the front of the payload (header,
    // exception map, digest, first elements). The digest's contract is
    // **id recovery**: any accepted mutation must reproduce the exact
    // original id sequence (content integrity is a transport/signing
    // concern — a flipped presence bit that touches no name derives
    // the same ids and legitimately decodes). Mutations that alter
    // names or structure change the derived ids and must die on the
    // digest; mutations inside the digest itself must always die.
    let mut digest_failures = 0usize;
    for i in 4..400.min(elided.len()) {
        let mut bad = elided.clone();
        bad[i] ^= 0x01;
        match from_compact_cbor_elided(&bad, &no_external) {
            Err(e) if e.to_string().contains("digest") => digest_failures += 1,
            Err(_) => {} // structural refusal is fine too
            Ok(v) => {
                let ids: Vec<&str> = v
                    .as_array()
                    .unwrap()
                    .iter()
                    .map(|e| e["@id"].as_str().unwrap())
                    .collect();
                assert_eq!(
                    ids, original_ids,
                    "accepted mutation at byte {i} kept every id"
                );
            }
        }
    }
    assert!(
        digest_failures > 0,
        "some mutation reached the digest check"
    );
}

#[test]
fn plain_decoders_refuse_elided_payloads() {
    let (compact, _) = golden_compact();
    let elided = to_compact_cbor_elided(&compact, &no_external).unwrap();
    let err = from_compact_cbor(&elided).unwrap_err().to_string();
    assert!(err.contains("elided"), "{err}");
    let err = from_cbor(&elided).unwrap_err().to_string();
    assert!(err.contains("elided"), "{err}");
}

#[test]
fn foreign_derivation_scheme_refuses_elided_payloads_only() {
    let (compact, _) = golden_compact();
    let mut elided = to_compact_cbor_elided(&compact, &no_external).unwrap();
    // Header word bytes: 8 magic + array(4) + 0x1B, scheme at [16].
    assert_eq!(elided[9], 0x1B);
    elided[16] = 0xFF;
    let err = from_compact_cbor_elided(&elided, &no_external)
        .unwrap_err()
        .to_string();
    assert!(err.contains("id-derivation scheme"), "{err}");
}
