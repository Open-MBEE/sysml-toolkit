//! Golden snapshots per metaclass: the curated fixtures under
//! `tests/goldens/` exercise every metaclass the corpus emission
//! produces (and then some — 152 total). Each metaclass's elements,
//! across all fixtures, are committed pretty-printed under
//! `tests/goldens/expected/<Metaclass>.json`; any emitter change to a
//! metaclass's compact shape shows up as a reviewable per-metaclass
//! diff instead of a silent drift.
//!
//! Fixtures emit *without* the standard library, so library references
//! serialize as deterministic `@ref` spellings and the gate stays
//! hermetic. IDs are the deterministic ownership-path UUIDv5s.
//!
//! To regenerate deliberately after a reviewed emitter change:
//!
//! ```console
//! UPDATE_GOLDENS=1 cargo test -p sysmlv2-parser --test goldens
//! ```

#![cfg(feature = "json")]

use serde_json::Value;
use std::collections::BTreeMap;
use std::fmt::Write as _;
use std::fs;
use std::path::PathBuf;
use sysmlv2_parser::json::model_to_compact_json;
use sysmlv2_parser::model::Model;

fn goldens_dir() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/goldens")
}

/// Metaclass → pretty JSON of its elements across all fixtures, in
/// (fixture, emission) order.
fn snapshot() -> BTreeMap<String, String> {
    let dir = goldens_dir();
    let mut fixtures: Vec<PathBuf> = fs::read_dir(&dir)
        .expect("tests/goldens exists")
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
    assert!(fixtures.len() >= 4, "golden fixtures present");

    let mut by_metaclass: BTreeMap<String, Vec<Value>> = BTreeMap::new();
    for path in &fixtures {
        let src = fs::read_to_string(path).unwrap();
        let mut model = Model::new();
        model.add_source(
            path.file_name().unwrap().to_string_lossy().into_owned(),
            &src,
        );
        assert!(
            !model.has_errors(),
            "golden fixture {} parses clean",
            path.display()
        );
        let Value::Array(elements) = model_to_compact_json(&model) else {
            panic!("compact JSON is a flat element array");
        };
        for e in elements {
            let ty = e["@type"].as_str().expect("@type").to_owned();
            by_metaclass.entry(ty).or_default().push(e);
        }
    }
    by_metaclass
        .into_iter()
        .map(|(ty, els)| {
            let mut text = serde_json::to_string_pretty(&Value::Array(els)).unwrap();
            text.push('\n');
            (ty, text)
        })
        .collect()
}

#[test]
fn golden_snapshots_per_metaclass() {
    let expected_dir = goldens_dir().join("expected");
    let snap = snapshot();

    if std::env::var("UPDATE_GOLDENS").is_ok() {
        let _ = fs::remove_dir_all(&expected_dir);
        fs::create_dir_all(&expected_dir).unwrap();
        for (ty, text) in &snap {
            fs::write(expected_dir.join(format!("{ty}.json")), text).unwrap();
        }
        println!("regenerated {} goldens", snap.len());
        return;
    }

    let mut report = String::new();
    let mut on_disk: Vec<String> = fs::read_dir(&expected_dir)
        .map(|rd| {
            rd.flatten()
                .filter_map(|e| {
                    e.path()
                        .file_stem()
                        .map(|s| s.to_string_lossy().into_owned())
                })
                .collect()
        })
        .unwrap_or_default();
    on_disk.sort();

    for (ty, text) in &snap {
        let path = expected_dir.join(format!("{ty}.json"));
        match fs::read_to_string(&path) {
            Err(_) => writeln!(report, "  new metaclass without a golden: {ty}").unwrap(),
            Ok(want) if want != *text => {
                writeln!(report, "  golden differs: {ty}").unwrap();
            }
            Ok(_) => {}
        }
    }
    for ty in &on_disk {
        if !snap.contains_key(ty) {
            writeln!(report, "  golden no longer produced: {ty}").unwrap();
        }
    }
    assert!(
        report.is_empty(),
        "golden snapshots drifted — review the diffs, then regenerate with \
         `UPDATE_GOLDENS=1 cargo test -p sysmlv2-parser --test goldens`:\n{report}"
    );
}

/// The fixtures must keep covering at least the metaclass inventory the
/// corpus emission produces today — extend a fixture when a new
/// metaclass starts appearing, never shrink coverage.
#[test]
fn golden_fixtures_cover_the_corpus_inventory() {
    let covered: Vec<String> = snapshot().into_keys().collect();
    let floor = 152usize;
    assert!(
        covered.len() >= floor,
        "golden metaclass coverage shrank: {} < {floor}",
        covered.len()
    );
}
