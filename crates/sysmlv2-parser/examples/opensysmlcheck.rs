//! Run the pinned external negative corpus against the full standard library
//! and print the per-file stage diagnostics as JSON:
//! `cargo run --release --example opensysmlcheck > report.json`.
//! The same stages and classification are gated by
//! `tests/opensysml.rs::opensysml_library_diagnostic_baseline`; this is the
//! human-readable report, and it still fails on any registered contract
//! regression.
#[path = "../tests/support/census.rs"]
mod census;

use std::{collections::BTreeMap, fs, path::Path};
use sysmlv2_parser::model::Model;

fn main() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/opensysml");
    let library = sysmlv2_testkit::library_dir();
    assert!(
        library.is_dir(),
        "initialize the standard-library submodule first"
    );
    let mut base = Model::new();
    base.load_library_dir(&library).unwrap();
    let prepared = base.prepare_library().expect("prepared library");
    let mut files = Vec::new();
    sysmlv2_testkit::collect_files(&root, &mut files);
    files.sort();
    let mut rows = BTreeMap::new();
    for path in files {
        let name = path
            .strip_prefix(&root)
            .unwrap()
            .to_string_lossy()
            .into_owned();
        let source = fs::read_to_string(&path).unwrap();
        let mut model = Model::new();
        prepared.clone().install(&mut model).unwrap();
        model.add_source(&name, &source);
        rows.insert(name, census::stage_diagnostics(&model));
    }
    println!("{}", serde_json::to_string_pretty(&rows).unwrap());
    let static_contracts: serde_json::Value = serde_json::from_str(include_str!(
        "../tests/fixtures/opensysml/static-contracts.json"
    ))
    .unwrap();
    let negative_contracts: serde_json::Value = serde_json::from_str(include_str!(
        "../tests/fixtures/opensysml/negative-contracts.json"
    ))
    .unwrap();
    let missing = census::contract_failures(&rows, &static_contracts, &negative_contracts);
    assert!(
        missing.is_empty(),
        "intended-rule regressions: {}",
        missing.join(", ")
    );
}
