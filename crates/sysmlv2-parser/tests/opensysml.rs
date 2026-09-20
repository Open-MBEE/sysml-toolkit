//! Independent negative models, with explicit known gaps rather than a claim
//! that every diagnostic is the intended rejection. Two committed baselines
//! pin every file's stage diagnostics: one without a library (missing
//! dependencies stay unknown) and one against the full standard library
//! (the census the backlog plan quotes). Both run the stages of
//! `support/census.rs`, shared with the `opensysmlcheck` reporting example.

#[path = "support/census.rs"]
mod census;

use serde_json::{Value, json};
use std::{collections::BTreeMap, fs, path::Path, path::PathBuf};
use sysmlv2_parser::model::Model;

fn root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/opensysml")
}

/// The pinned census: every provenance entry exists and nothing else does.
fn provenance_files() -> Vec<String> {
    let provenance: Value =
        serde_json::from_str(&fs::read_to_string(root().join("provenance.json")).unwrap()).unwrap();
    let entries = provenance["files"].as_array().unwrap();
    assert_eq!(
        entries.len(),
        462,
        "fixture census changed; adjudicate the source pin"
    );
    let mut files = Vec::new();
    sysmlv2_testkit::collect_files(&root(), &mut files);
    assert_eq!(
        files.len(),
        entries.len(),
        "fixture removed or added without provenance"
    );
    entries
        .iter()
        .map(|e| e["file"].as_str().unwrap().to_string())
        .collect()
}

fn negative_contracts() -> Value {
    serde_json::from_str(include_str!("fixtures/opensysml/negative-contracts.json")).unwrap()
}

/// Compare (or, under `UPDATE_OPENSYSML_BASELINE`, rewrite) a baseline
/// file. Improvements change the baseline too, so every difference is
/// adjudicated by hand.
fn gate(baseline: &str, actual: &BTreeMap<String, Value>) {
    let path = root().join(baseline);
    if std::env::var_os("UPDATE_OPENSYSML_BASELINE").is_some() {
        fs::write(&path, serde_json::to_string_pretty(actual).unwrap() + "\n").unwrap();
    }
    let expected: BTreeMap<String, Value> =
        serde_json::from_str(&fs::read_to_string(&path).expect("missing adjudicated baseline"))
            .unwrap();
    let changed: Vec<_> = actual
        .iter()
        .filter(|(file, value)| expected.get(*file) != Some(*value))
        .map(|(file, value)| format!("{file}: {value}"))
        .collect();
    assert!(
        changed.is_empty(),
        "{baseline} changed; adjudicate improvements as well as regressions:\n{}",
        changed.join("\n")
    );
    assert_eq!(expected.len(), actual.len());
}

#[test]
fn opensysml_negative_diagnostic_baseline() {
    let accepted = census::accepted_fixtures(&negative_contracts());
    let mut actual = BTreeMap::new();
    let mut unknown = 0;
    for name in provenance_files() {
        let source = fs::read_to_string(root().join(&name)).unwrap();
        let mut model = Model::new();
        model.add_source(&name, &source);
        let rows = census::stage_diagnostics(&model);
        let status = census::status(
            &rows,
            true,
            accepted.contains(&name),
            "unknown without library",
        );
        if status == "unknown without library" {
            unknown += 1;
        }
        actual.insert(name, json!({ "status": status, "diagnostics": rows }));
    }
    eprintln!(
        "negative corpus without library: {} files, {unknown} unknown without library",
        actual.len()
    );
    gate("baseline.json", &actual);
}

/// The full-library census: the same files against the standard library,
/// gated on a second baseline, plus every registered contract.
#[test]
fn opensysml_library_diagnostic_baseline() {
    // One retained library graph installed into every model; parity with
    // per-file resolution replay over these fixtures is gated by
    // `tests/prepared_library.rs`.
    let mut base = Model::new();
    base.load_library_dir(&sysmlv2_testkit::library_dir())
        .unwrap();
    let prepared = base.prepare_library().unwrap();

    let accepted = census::accepted_fixtures(&negative_contracts());
    let mut rows_by_file = BTreeMap::new();
    let mut actual = BTreeMap::new();
    let mut unknown = 0;
    for name in provenance_files() {
        let source = fs::read_to_string(root().join(&name)).unwrap();
        let mut model = Model::new();
        prepared.clone().install(&mut model).unwrap();
        model.add_source(&name, &source);
        let rows = census::stage_diagnostics(&model);
        let status = census::status(&rows, false, accepted.contains(&name), "unknown");
        if status == "unknown" {
            unknown += 1;
        }
        actual.insert(
            name.clone(),
            json!({ "status": status, "diagnostics": rows }),
        );
        rows_by_file.insert(name, rows);
    }
    eprintln!(
        "negative corpus with library: {} files, {unknown} unknown",
        actual.len()
    );
    let static_contracts: Value =
        serde_json::from_str(include_str!("fixtures/opensysml/static-contracts.json")).unwrap();
    let missing =
        census::contract_failures(&rows_by_file, &static_contracts, &negative_contracts());
    assert!(
        missing.is_empty(),
        "intended-rule regressions: {}",
        missing.join(", ")
    );
    gate("baseline-library.json", &actual);
}
