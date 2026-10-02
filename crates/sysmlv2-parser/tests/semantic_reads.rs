#![cfg(feature = "json")]

use sysmlv2_parser::json::{
    ClosurePolicy, DerivedValue, Derives, PropertyError, ResolvedModel, TypeInputIssue,
    derives_under,
};
use sysmlv2_parser::model::Model;

#[test]
fn exact_reads_refuse_incomplete_closures_but_preserve_empty_and_null() {
    let mut model = Model::new();
    model.add_source("m.sysml", "package P { part def A; part def B :> A; }");
    let mut r = ResolvedModel::build(&model);
    let b = r.resolve_qualified("P::B").unwrap();
    r.set_closure_policy(ClosurePolicy::Closure {
        include_implied: true,
    });
    assert_eq!(
        derives_under("PartDefinition", "inheritedMembership", r.closure_policy()),
        Derives::Passthrough
    );
    // PartDefinition has a checked membership provider, but this model omits
    // the canonical library ancestors needed to certify its complete closure.
    assert_eq!(
        r.derived_exact(b, "inheritedMembership"),
        Err(PropertyError::IncompleteTypeFeatures(
            TypeInputIssue::IncompleteProvider
        ))
    );
    assert_eq!(
        r.derived_exact(b, "ownedFeature"),
        Ok(DerivedValue::Elements(vec![]))
    );
    assert_eq!(r.derived_exact(b, "shortName"), Ok(DerivedValue::Null));
    assert_eq!(
        r.derived_exact(b, "unknown"),
        Err(PropertyError::NotDeclared)
    );
}

#[test]
fn checked_type_reads_refuse_incomplete_typing_before_compatibility_references() {
    let mut model = Model::new();
    model.add_source("m.sysml", "package P { part a : Missing; }");
    let mut r = ResolvedModel::build(&model);
    let a = r.resolve_qualified("P::a").unwrap();
    assert!(
        matches!(r.derived(a,"type"), sysmlv2_parser::json::Derived::Value(DerivedValue::References(ref values)) if values.iter().any(|v|matches!(v,sysmlv2_parser::json::Reference::Unresolved(_))))
    );
    assert_eq!(r.derived_exact(a, "type"), Err(PropertyError::Approximate));
}

#[test]
fn exact_reads_check_required_values_and_keep_external_identity() {
    use std::collections::HashMap;
    use sysmlv2_parser::json::Reference;
    let mut model = Model::new();
    model.add_source(
        "m.sysml",
        "package P { attribute a = 1 + 2; port def D; port p : ~D; }",
    );
    let mut r = ResolvedModel::build(&model);
    let plus = r
        .elements()
        .find(|&e| r.element_type(e) == "OperatorExpression")
        .unwrap();
    let typing = r
        .elements()
        .find(|&e| r.element_type(e) == "ConjugatedPortTyping")
        .unwrap();
    assert_eq!(
        r.derived_exact(plus, "instantiatedType"),
        Err(PropertyError::MissingRequiredValue)
    );
    let definition = r.resolve_qualified("P::D").unwrap();
    assert_eq!(
        r.derived_exact(typing, "portDefinition"),
        Ok(DerivedValue::Element(definition))
    );
    let id = uuid::Uuid::new_v5(&uuid::Uuid::NAMESPACE_OID, b"test-plus");
    r.set_library_names(&HashMap::from([(
        id.to_string(),
        vec!["BaseFunctions".into(), "+".into()],
    )]));
    assert_eq!(
        r.derived_exact(plus, "instantiatedType"),
        Ok(DerivedValue::Reference(Reference::External(id)))
    );
}

#[test]
fn semantic_reader_follows_redefinitions_and_requested_shape() {
    let mut model = Model::new();
    model.add_source(
        "m.sysml",
        "package P { part def D; part p : D; interface def I; }",
    );
    let mut r = ResolvedModel::build(&model);
    let p = r.resolve_qualified("P::p").unwrap();
    let d = r.resolve_qualified("P::D").unwrap();
    let interface = r.resolve_qualified("P::I").unwrap();
    let typing = r
        .elements()
        .find(|&e| r.element_type(e) == "FeatureTyping")
        .unwrap();
    let dref = serde_json::json!({"@id": r.element_id(d).to_string()});
    let pref = serde_json::json!({"@id": r.element_id(p).to_string()});
    assert_eq!(r.property(typing, "general").unwrap(), dref);
    assert_eq!(r.property(typing, "type").unwrap(), dref);
    assert_eq!(
        r.property(typing, "target").unwrap(),
        serde_json::json!([dref])
    );
    assert_eq!(r.property(typing, "specific").unwrap(), pref);
    assert_eq!(
        r.property(typing, "source").unwrap(),
        serde_json::json!([pref])
    );
    assert_eq!(
        r.property(interface, "isSufficient").unwrap(),
        serde_json::json!(true)
    );
    assert_eq!(r.property(p, "isVariable"), Err(PropertyError::Approximate));
    let owning = r.property(p, "owningRelationship").unwrap();
    let membership = r.element_by_id(owning["@id"].as_str().unwrap()).unwrap();
    assert_eq!(
        r.property(membership, "memberName").unwrap(),
        serde_json::json!("p")
    );
    assert_eq!(
        r.property(membership, "ownedMemberName").unwrap(),
        serde_json::json!("p")
    );
}

#[test]
fn semantic_reader_exposes_nonmembership_ownership_and_defaults() {
    let mut model = Model::new();
    model.add_source(
        "m.sysml",
        "package P { part a { part b; } part c; connection connect a.b to c; }",
    );
    let mut r = ResolvedModel::build(&model);
    let chain = r
        .elements()
        .find(|&e| r.element_type(e) == "Feature")
        .unwrap();
    let relation = r.property(chain, "owningRelationship").unwrap();
    let owner = r.element_by_id(relation["@id"].as_str().unwrap()).unwrap();
    assert_eq!(r.element_type(owner), "ReferenceSubsetting");
    assert_eq!(
        r.property(owner, "ownedRelatedElement").unwrap(),
        serde_json::json!([{"@id": r.element_id(chain).to_string()}])
    );
    assert_eq!(
        r.property(chain, "isImpliedIncluded").unwrap(),
        serde_json::json!(false)
    );
    assert_eq!(
        r.property(chain, "isConstant").unwrap(),
        serde_json::json!(false)
    );
}

#[test]
fn strict_export_refuses_incomplete_semantics_without_recovery() {
    let mut model = Model::new();
    model.add_source(
        "m.sysml",
        "package P { port p : Missing; attribute a = 1; }",
    );
    let mut r = ResolvedModel::build(&model);
    let before = r.closure_policy();
    let err = r.to_full_json_strict().unwrap_err();
    assert!(err.issues.iter().any(|i| i.property == "result"));
    assert!(
        err.issues
            .iter()
            .any(|i| matches!(i.reason, PropertyError::UnresolvedReference(_)))
    );
    assert_eq!(r.closure_policy(), before);
}

#[test]
fn strict_export_of_structural_namespace_has_no_placeholders() {
    let mut model = Model::new();
    model.add_source("m.sysml", "package P;");
    let mut r = ResolvedModel::build(&model);
    let value = r.to_full_json_strict().unwrap();
    assert!(
        value
            .as_array()
            .unwrap()
            .iter()
            .all(|e| e["isImpliedIncluded"] == false)
    );
    assert!(!value.to_string().contains("x-sysmlv2-unresolved-reference"));
}

#[test]
fn checked_namespace_member_includes_alias_targets() {
    let mut model = Model::new();
    model.add_source(
        "m.sysml",
        "package P { package A; alias second for A; package Q { alias other for P::A; } }",
    );
    let mut r = ResolvedModel::build(&model);
    let a = r.resolve_qualified("P::A").unwrap();
    let q = r.resolve_qualified("P::Q").unwrap();
    let p = r.resolve_qualified("P").unwrap();
    assert_eq!(
        r.property(p, "member").unwrap().as_array().unwrap().len(),
        2
    );
    assert_eq!(
        r.property(q, "member").unwrap(),
        serde_json::json!([{"@id": r.element_id(a).to_string()}])
    );
    let export = r.to_full_json_strict().unwrap();
    let qid = r.element_id(q).to_string();
    let row = export
        .as_array()
        .unwrap()
        .iter()
        .find(|e| e["@id"] == qid)
        .unwrap();
    assert_eq!(
        row["member"],
        serde_json::json!([{"@id": r.element_id(a).to_string()}])
    );
}
