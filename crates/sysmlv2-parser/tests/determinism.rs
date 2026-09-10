//! Emission determinism gate: the same source must produce byte-identical
//! compact JSON on every emission. The Annex A vehicle model is the
//! regression subject — `VehicleAnalysis` recursively imports
//! `VehicleConfiguration_b::**`, which makes three same-named `vehicle_b`
//! parts visible in the `fuelEconomyAnalysis` scope, and resolution among
//! them used to follow `HashMap` iteration order (`lookup_recursive`),
//! flipping the emitted ids between runs. Ambiguous recursive-import hits
//! now remain unresolved and are diagnosed rather than receiving a
//! declaration-order-dependent target.

#![cfg(feature = "json")]

use serde_json::Value;
use std::collections::HashMap;
use std::fs;
use sysmlv2_parser::json::to_compact_json;
use sysmlv2_parser::parser::parse_source;

const ANNEX_A: &str =
    "sysml/src/examples/Vehicle Example/SysML v2 Spec Annex A SimpleVehicleModel.sysml";

fn deref<'a>(index: &HashMap<&str, &'a Value>, r: &Value) -> &'a Value {
    index[r["@id"].as_str().expect("expected an {\"@id\"} reference")]
}

/// The first `FeatureReferenceExpression` in `e`'s ownership subtree.
fn find_reference_expr<'a>(index: &HashMap<&str, &'a Value>, e: &'a Value) -> Option<&'a Value> {
    if e["@type"] == "FeatureReferenceExpression" {
        return Some(e);
    }
    for r in e["ownedRelationship"].as_array()? {
        let rel = deref(index, r);
        for owned in rel.get("ownedRelatedElement").and_then(Value::as_array)? {
            if let Some(hit) = find_reference_expr(index, deref(index, owned)) {
                return Some(hit);
            }
        }
    }
    None
}

#[test]
fn annex_a_compact_json_is_deterministic() {
    let path = sysmlv2_testkit::corpus_root().join(ANNEX_A);
    let src = fs::read_to_string(&path).unwrap();
    let parse = parse_source(&src);

    // Each emission builds its scope tables from scratch with fresh
    // (randomly seeded) hash maps, so repeated in-process emissions catch
    // hash-order-dependent resolution.
    let first = to_compact_json(&parse.unit);
    let first_text = first.to_string();
    for run in 1..8 {
        assert_eq!(
            to_compact_json(&parse.unit).to_string(),
            first_text,
            "emission {run} diverged from the first"
        );
    }

    // Pin ambiguity handling itself: the analysis subject
    // (`subject = vehicle_b;`) must retain its spelling rather than bind to
    // one of the three candidates by declaration order.
    let elements = first.as_array().expect("compact form is a flat array");
    let index: HashMap<&str, &Value> = elements
        .iter()
        .map(|e| (e["@id"].as_str().unwrap(), e))
        .collect();
    let analysis = elements
        .iter()
        .find(|e| e["declaredName"] == "fuelEconomyAnalysis")
        .expect("fuelEconomyAnalysis in output");
    let subject_membership = analysis["ownedRelationship"]
        .as_array()
        .unwrap()
        .iter()
        .map(|r| deref(&index, r))
        .find(|rel| rel["@type"] == "SubjectMembership")
        .expect("fuelEconomyAnalysis has a SubjectMembership");
    let subject = deref(&index, &subject_membership["ownedRelatedElement"][0]);
    let expr = find_reference_expr(&index, subject).expect("subject value is a feature reference");
    let target_membership = expr["ownedRelationship"]
        .as_array()
        .unwrap()
        .iter()
        .map(|r| deref(&index, r))
        .find(|rel| rel["@type"] == "Membership")
        .expect("reference expression has a target Membership");
    assert_eq!(
        target_membership["memberElement"]["@ref"].as_str(),
        Some("vehicle_b"),
        "ambiguous recursive-import hit must remain unresolved"
    );
}
