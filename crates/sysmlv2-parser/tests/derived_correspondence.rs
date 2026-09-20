//! The committed correspondence table (`spec-refs/derived-correspondence.json`,
//! written by `cargo run --example derived_correspondence`) is fresh: its
//! rows are the property catalog's, and every derived row's fidelities
//! are what `derives`/`derives_under` answer today. A change to the
//! layer's tables that is not followed by a regeneration fails here.

#![cfg(feature = "json")]

use std::collections::BTreeSet;
use sysmlv2_parser::json::{
    ClosurePolicy, Derives, PropertyShape, derives, derives_under, property_catalog,
};

fn fidelity(f: Derives) -> &'static str {
    match f {
        Derives::NotDeclared => "not-declared",
        Derives::NotComputed => "not-computed",
        Derives::Passthrough => "passthrough",
        Derives::Exact => "exact",
    }
}

#[test]
fn committed_correspondence_table_is_fresh() {
    let path = sysmlv2_testkit::workspace_root().join("spec-refs/derived-correspondence.json");
    let table: serde_json::Value =
        serde_json::from_str(&std::fs::read_to_string(&path).expect("the committed table"))
            .unwrap();
    let rows = table["rows"].as_array().unwrap();
    let committed: BTreeSet<(String, String, bool, String)> = rows
        .iter()
        .map(|r| {
            (
                r["metaclass"].as_str().unwrap().to_string(),
                r["property"].as_str().unwrap().to_string(),
                r["owned"].as_bool().unwrap(),
                r["shape"].as_str().unwrap().to_string(),
            )
        })
        .collect();
    let current: BTreeSet<(String, String, bool, String)> = property_catalog()
        .map(|e| {
            let shape = match e.shape {
                PropertyShape::Array => "array",
                PropertyShape::Boolean => "boolean",
                PropertyShape::Nullable => "nullable",
                PropertyShape::Scalar => "scalar",
                PropertyShape::Enumeration => "enumeration",
                PropertyShape::RequiredReference => "required-reference",
                _ => "other",
            };
            (
                e.metaclass.to_string(),
                e.property.to_string(),
                e.owned,
                shape.to_string(),
            )
        })
        .collect();
    assert_eq!(
        committed, current,
        "the catalog rows changed: rerun `cargo run --example derived_correspondence`"
    );
    let closure = ClosurePolicy::Closure {
        include_implied: true,
    };
    for r in rows.iter().filter(|r| r["owned"] == false) {
        let m = r["metaclass"].as_str().unwrap();
        let p = r["property"].as_str().unwrap();
        assert_eq!(
            r["fidelity"].as_str(),
            Some(fidelity(derives(m, p))),
            "{m}.{p}: fidelity changed — rerun `cargo run --example derived_correspondence`"
        );
        assert_eq!(
            r["fidelityUnderClosure"].as_str(),
            Some(fidelity(derives_under(m, p, closure))),
            "{m}.{p}: fidelity under the closure policy changed"
        );
    }
}
