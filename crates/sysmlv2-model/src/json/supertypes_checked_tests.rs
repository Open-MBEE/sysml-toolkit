use super::*;
use crate::{json::ResolvedModel, model::Model};
fn fixture(source: &str) -> ResolvedModel {
    let mut model = Model::new();
    assert!(model.add_library_source("bases.kerml", "standard library package Base {classifier Anything; datatype DataValue specializes Anything;} standard library package Occurrences {class Occurrence specializes Base::Anything;} standard library package Objects {struct Object specializes Occurrences::Occurrence;}").diagnostics.is_empty());
    assert!(
        model
            .add_source("supertypes.kerml", source)
            .diagnostics
            .is_empty()
    );
    ResolvedModel::build(&model)
}
#[test]
fn explicit_supertypes_exclude_implied_and_validate_the_complete_owned_projection() {
    let mut r = fixture(
        "class A; class B; class C specializes A, B; class D conjugates C; class T {feature x;} feature p:T; feature q chains p.x;",
    );
    let a = r.resolve_qualified("A").unwrap().0;
    let b = r.resolve_qualified("B").unwrap().0;
    let c = r.resolve_qualified("C").unwrap().0;
    let d = r.resolve_qualified("D").unwrap().0;
    let q = r.resolve_qualified("q").unwrap().0;
    let x = r.resolve_qualified("T::x").unwrap().0;
    assert_eq!(
        TypeRelations::default().explicit_supertypes(&mut r.b, c, &mut 0),
        Some(vec![a, b])
    );
    assert_eq!(
        TypeRelations::default().explicit_supertypes(&mut r.b, d, &mut 0),
        Some(vec![c])
    );
    assert_eq!(
        TypeRelations::default().explicit_supertypes(&mut r.b, q, &mut 0),
        Some(vec![x])
    );
    let relations: Vec<_> = r.b.elements[c]
        .owned_relationships
        .iter()
        .copied()
        .filter(|&e| conforms(r.b.elements[e].ty, "Specialization"))
        .collect();
    r.b.set(relations[1], "isImplied", serde_json::json!(true));
    assert_eq!(
        TypeRelations::default().explicit_supertypes(&mut r.b, c, &mut 0),
        Some(vec![a])
    );
    assert_eq!(
        TypeRelations::default().specializes(&mut r.b, c, b, &mut 0),
        RelationFact::Yes
    );
    r.b.set(
        relations[0],
        "target",
        serde_json::json!([{"@id":r.b.elements[b].id.to_string()}]),
    );
    assert_eq!(
        TypeRelations::default().explicit_supertypes(&mut r.b, c, &mut 0),
        None
    );
}
#[test]
fn exact_supertypes_refuses_duplicate_projection_but_compatibility_keeps_positive_identity() {
    let mut r = fixture("class A; class C specializes A, A;");
    let a = r.resolve_qualified("A").unwrap().0;
    let c = r.resolve_qualified("C").unwrap().0;
    assert_eq!(
        TypeRelations::default().explicit_supertypes(&mut r.b, c, &mut 0),
        None
    );
    assert_eq!(
        TypeRelations::default().specializes(&mut r.b, c, a, &mut 0),
        RelationFact::Yes
    );
    let mut steps = crate::eval::MAX_STEPS;
    assert_eq!(
        TypeRelations::default().explicit_supertypes(&mut r.b, c, &mut steps),
        None
    );
    assert!(steps > crate::eval::MAX_STEPS);
}
#[test]
fn feature_target_is_one_hop_and_self_is_not_appended() {
    let mut r = fixture(
        "feature a; feature b chains a; feature q chains b; feature same chains same; feature repeated subsets a chains a;",
    );
    let b = r.resolve_qualified("b").unwrap().0;
    let q = r.resolve_qualified("q").unwrap().0;
    let same = r.resolve_qualified("same").unwrap().0;
    let repeated = r.resolve_qualified("repeated").unwrap().0;
    assert_eq!(
        TypeRelations::default().explicit_supertypes(&mut r.b, q, &mut 0),
        Some(vec![b])
    );
    assert_eq!(
        TypeRelations::default().explicit_supertypes(&mut r.b, same, &mut 0),
        Some(vec![])
    );
    assert_eq!(
        TypeRelations::default().explicit_supertypes(&mut r.b, repeated, &mut 0),
        None,
        "duplicate append stays outside checked domain"
    );
}
#[test]
fn conjugation_and_feature_target_are_not_filtered_as_implied_specializations() {
    let mut r = fixture(
        "feature original; feature chainEnd; feature c conjugates original chains chainEnd;",
    );
    let c = r.resolve_qualified("c").unwrap().0;
    let original = r.resolve_qualified("original").unwrap().0;
    let chain = r.resolve_qualified("chainEnd").unwrap().0;
    let relations = r.b.elements[c].owned_relationships.to_vec();
    for &rel in &relations {
        if conforms(r.b.elements[rel].ty, "Conjugation")
            || conforms(r.b.elements[rel].ty, "FeatureChaining")
        {
            r.b.elements[rel]
                .props
                .insert("isImplied", serde_json::json!(true));
        }
    }
    assert_eq!(
        TypeRelations::default().explicit_supertypes(&mut r.b, c, &mut 0),
        Some(vec![original, chain])
    );
    let last = *relations
        .iter()
        .find(|&&rel| conforms(r.b.elements[rel].ty, "FeatureChaining"))
        .unwrap();
    let wrong = r.b.elements[original].id;
    r.b.elements[last]
        .props
        .insert("target", serde_json::json!([{"@id":wrong.to_string()}]));
    assert_eq!(
        TypeRelations::default().explicit_supertypes(&mut r.b, c, &mut 0),
        None,
        "last link cannot hide behind conjugation"
    );
}
#[test]
fn explicit_projection_uses_shared_semantic_ownership_after_materialization() {
    use crate::json::{ClosurePolicy, Derived, DerivedValue, ElementRef};
    let mut r = fixture("class A; class C specializes A; feature x; feature v=x;");
    let a = r.resolve_qualified("A").unwrap().0;
    let c = r.resolve_qualified("C").unwrap().0;
    let v = r.resolve_qualified("v").unwrap();
    let expression = r.members_via(v, "FeatureValue")[0];
    assert_eq!(
        TypeRelations::default().explicit_supertypes(&mut r.b, c, &mut 0),
        Some(vec![a])
    );
    r.set_closure_policy(ClosurePolicy::Closure {
        include_implied: true,
    });
    let result = match r.derived(expression, "result") {
        Derived::Value(DerivedValue::Element(result)) => result,
        other => panic!("expected generated result: {other:?}"),
    };
    assert!(result.0 >= r.b.explicit_len());
    assert_eq!(
        TypeRelations::default().explicit_supertypes(&mut r.b, c, &mut 0),
        Some(vec![a])
    );
    assert_eq!(
        TypeRelations::default().explicit_supertypes(&mut r.b, result.0, &mut 0),
        Some(vec![])
    );
    assert!(
        r.implied_relationships(ElementRef(c))
            .iter()
            .all(|rel| r.is_implied(*rel))
    );
    let subsetting = r.b.elements[result.0].owned_relationships[0];
    let wrong = r.b.elements[a].id;
    r.b.elements[subsetting].props.insert(
        "owningRelatedElement",
        serde_json::json!({"@id":wrong.to_string()}),
    );
    assert_eq!(
        TypeRelations::default().explicit_supertypes(&mut r.b, result.0, &mut 0),
        None,
        "excluded implied edge still requires certified ownership"
    );
}

#[test]
fn conjugated_supertypes_ignore_flag_but_preserve_complete_feature_append_and_limits() {
    use crate::json::{DerivedValue, OperationError};
    let mut r = fixture(
        "feature original; feature chainSource {feature chainEnd;} feature c conjugates original chains chainSource.chainEnd; class A; class B conjugates A; class C conjugates B;",
    );
    let original = r.resolve_qualified("original").unwrap();
    let last = r.resolve_qualified("chainSource::chainEnd").unwrap();
    let c = r.resolve_qualified("c").unwrap();
    let b = r.resolve_qualified("B").unwrap();
    let capital_c = r.resolve_qualified("C").unwrap();
    let declaration = "Core-Types-Type-supertypes_Boolean";
    for value in [false, true] {
        let out = r
            .invoke_operation(c, declaration, &[DerivedValue::Bool(value)])
            .unwrap();
        assert_eq!(out.effective, "Core-Features-Feature-supertypes_Boolean");
        assert_eq!(
            out.value,
            DerivedValue::References(vec![
                super::super::Reference::Element(original),
                super::super::Reference::Element(last)
            ])
        );
        assert_eq!(
            TypeRelations::default().checked_supertypes(&mut r.b, capital_c.0, value, &mut 0),
            Ok(vec![b.0])
        );
    }
    let mut steps = crate::eval::MAX_STEPS;
    assert_eq!(
        TypeRelations::default().checked_supertypes(&mut r.b, c.0, false, &mut steps),
        Err(SupertypesFailure::Incomplete)
    );
    assert!(steps > crate::eval::MAX_STEPS);
    let rel = r.b.elements[c.0]
        .owned_relationships
        .iter()
        .copied()
        .find(|&rel| conforms(r.b.elements[rel].ty, "Conjugation"))
        .unwrap();
    r.b.elements[rel].props.insert(
        "originalType",
        serde_json::json!({"@id":uuid::Uuid::new_v4().to_string()}),
    );
    assert!(matches!(
        r.invoke_operation(c, declaration, &[DerivedValue::Bool(false)]),
        Err(OperationError::Incomplete { .. })
    ));
}
