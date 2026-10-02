//! Structural ownership remains readable when inherited semantics are incomplete.
use serde_json::{Value, json};
use sysmlv2_parser::{
    json::{ClosurePolicy, ElementRef, ResolvedModel},
    model::Model,
};

fn relationships(r: &mut ResolvedModel, owner: ElementRef) -> Vec<Value> {
    let written = r.owned_relationships(owner);
    let implied = r.implied_relationships(owner);
    let mut expected = Vec::new();
    for relationship in written.into_iter().chain(implied) {
        let value = json!({"@id": r.element_id(relationship).to_string()});
        if !expected.contains(&value) {
            expected.push(value);
        }
    }
    expected
}

#[test]
fn checked_owned_relationships_include_materialized_edges_in_order() {
    let mut model = Model::new();
    model
        .load_library_dir(&sysmlv2_testkit::library_dir())
        .unwrap();
    let unit = model.add_source(
        "ownership.sysml",
        "package P { part def A { part child; } part def B :> A; part b : B; }",
    );
    assert!(unit.diagnostics.is_empty());
    let mut r = ResolvedModel::build(&model);
    let mut with_implied = 0;
    for name in ["P::A", "P::B", "P::b"] {
        let owner = r.resolve_qualified(name).unwrap();
        // The first checked call must publish the same edges as a warm call.
        let cold = r.property(owner, "ownedRelationship").unwrap();
        let expected = relationships(&mut r, owner);
        let has_implied = !r.implied_relationships(owner).is_empty();
        with_implied += usize::from(has_implied);
        assert_eq!(cold, json!(expected), "{name}");
        for policy in [
            ClosurePolicy::default(),
            ClosurePolicy::Closure {
                include_implied: true,
            },
        ] {
            r.set_closure_policy(policy);
            assert_eq!(r.property(owner, "ownedRelationship").unwrap(), cold);
        }
        for value in cold.as_array().unwrap() {
            let relationship = r.element_by_id(value["@id"].as_str().unwrap()).unwrap();
            assert_eq!(
                r.property(relationship, "owningRelatedElement").unwrap(),
                json!({"@id":r.element_id(owner).to_string()}),
            );
        }
        // Listing materialized edges does not claim complete implied semantics.
        if has_implied {
            assert!(r.property(owner, "isImpliedIncluded").is_err());
        }
    }
    assert!(with_implied > 0);
}

#[test]
fn structural_reads_do_not_hide_unresolved_owned_relationships() {
    let mut model = Model::new();
    model.add_source("ownership.sysml", "part broken : Missing;");
    let mut r = ResolvedModel::build(&model);
    let owner = r.resolve_qualified("broken").unwrap();
    let expected = relationships(&mut r, owner);
    assert!(!expected.is_empty());
    assert_eq!(
        r.property(owner, "ownedRelationship").unwrap(),
        json!(expected)
    );
    let strict = r.to_full_json_strict().unwrap_err();
    assert!(
        !strict
            .issues
            .iter()
            .any(|issue| issue.property == "ownedRelationship")
    );
    assert!(strict.issues.iter().any(|issue| issue.property == "type"));
}
