//! Derivability gate (IDS.md): `ids::derive_ids` — the
//! value-side twin of the builder's id assignment — reproduces every
//! non-root user-element id from the compact element array alone,
//! across every golden fixture and (when the submodule is present) the
//! end-to-end validation model resolved against the standard library.
//! A foreign payload degrades to mismatches, never a panic.

#![cfg(feature = "json")]

use serde_json::Value;
use std::fs;
use std::path::PathBuf;
use sysmlv2_parser::ids::derive_ids;
use sysmlv2_parser::json::{library_name_map, model_to_compact_json};
use sysmlv2_parser::model::Model;
use uuid::Uuid;

fn assert_all_derivable(compact: &Value, external: &dyn Fn(&str) -> Option<String>) -> usize {
    let elems = compact.as_array().unwrap();
    let derived = derive_ids(compact, external).expect("payload well-formed");
    let mut roots = 0usize;
    for (e, d) in elems.iter().zip(&derived) {
        let actual = Uuid::parse_str(e["@id"].as_str().unwrap()).unwrap();
        match d {
            Some(d) => assert_eq!(
                *d,
                actual,
                "{} {} derives",
                e["@type"].as_str().unwrap(),
                actual
            ),
            None => roots += 1,
        }
    }
    roots
}

#[test]
fn golden_fixtures_derive_every_non_root_id() {
    let dir = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/goldens");
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
    let compact = model_to_compact_json(&model);
    let n = compact.as_array().unwrap().len();
    assert!(n >= 1362, "corpus present ({n})");
    // Hermetic fixtures: external targets are @ref names, the resolver
    // closure must never fire.
    let roots = assert_all_derivable(&compact, &|s| panic!("unexpected external {s}"));
    assert_eq!(roots, fixtures.len(), "one assigned root per unit");
}

#[test]
fn library_resolved_model_derives_with_external_names() {
    let Some(files) = sysmlv2_testkit::apollo_files() else {
        eprintln!("skipping: end-to-end model submodule not initialized");
        return;
    };
    let mut model = Model::new();
    model
        .load_library_dir(&sysmlv2_testkit::library_dir())
        .expect("library");
    for f in &files {
        let src = fs::read_to_string(f).unwrap();
        model.add_source(f.file_name().unwrap().to_string_lossy().into_owned(), &src);
    }
    let compact = model_to_compact_json(&model);
    let names = library_name_map(&model);
    let by_id: std::collections::HashMap<String, String> = names
        .into_iter()
        .filter_map(|(id, segs)| segs.last().cloned().map(|n| (id.to_string(), n)))
        .collect();
    let roots = assert_all_derivable(&compact, &|s| by_id.get(s).cloned());
    assert_eq!(roots, files.len(), "one assigned root per unit");
}

#[test]
fn foreign_ids_mismatch_without_panic() {
    let mut model = Model::new();
    model.add_source(
        "t.sysml".to_string(),
        "package P { part def V; part v : V; }",
    );
    let mut compact = model_to_compact_json(&model);
    // Re-badge one element with a foreign id (references untouched).
    compact.as_array_mut().unwrap()[2]["@id"] =
        Value::String("11111111-2222-4333-8444-555555555555".into());
    let derived = derive_ids(&compact, &|_| None).unwrap();
    let mismatches = compact
        .as_array()
        .unwrap()
        .iter()
        .zip(&derived)
        .filter(|(e, d)| {
            d.is_some_and(|d| d != Uuid::parse_str(e["@id"].as_str().unwrap()).unwrap())
        })
        .count();
    assert!(mismatches >= 1, "foreign id surfaces as a mismatch");
}
