//! Corpus source labels must preserve identity even when basenames collide.
#![cfg(feature = "json")]
use std::collections::HashSet;
use std::path::Path;
use sysmlv2_parser::{json::model_to_compact_json, model::Model};

fn compact_at(checkout: &Path) -> serde_json::Value {
    let mut model = Model::new();
    for relative in ["examples/model.sysml", "validation/model.sysml"] {
        let path = checkout.join(relative);
        let name = sysmlv2_testkit::relative_source_name(checkout, &path);
        model.add_source(name, "package P { attribute x = 1; }");
    }
    assert!(!model.has_errors());
    model_to_compact_json(&model)
}

#[test]
fn same_basename_documents_have_distinct_root_and_descendant_ids() {
    let compact = compact_at(Path::new("checkout-a"));
    let rows = compact.as_array().unwrap();
    let ids: HashSet<_> = rows
        .iter()
        .map(|row| row["@id"].as_str().unwrap())
        .collect();
    assert_eq!(
        ids.len(),
        rows.len(),
        "no document or descendant identity is aliased"
    );
    let roots: Vec<_> = rows
        .iter()
        .filter(|row| row["@type"] == "Namespace")
        .collect();
    assert_eq!(roots.len(), 2);
    assert_ne!(roots[0]["@id"], roots[1]["@id"]);
}

#[test]
fn relocating_a_checkout_preserves_relative_source_identity() {
    assert_eq!(
        compact_at(Path::new("checkout-a")),
        compact_at(Path::new("checkout-b"))
    );
}
