use super::*;
use crate::{
    json::{ClosurePolicy, derives},
    model::Model,
};
fn model(source: &str) -> ResolvedModel {
    let mut m = Model::new();
    assert!(
        m.add_source("typing-dependencies.kerml", source)
            .diagnostics
            .is_empty()
    );
    let mut r = ResolvedModel::build(&m);
    r.set_closure_policy(ClosurePolicy::Closure {
        include_implied: true,
    });
    r
}
#[test]
fn inverse_typing_invalidates_direct_filters_and_generated_compositions() {
    // The first two cases are native source syntax. The remaining cases use
    // the same explicit inverse FeatureTyping topology with exact receiver and
    // target metaclasses to exercise each kind-filtered dependency branch.
    for (receiver, target, property) in [
        ("Feature", "Classifier", "type"),
        ("Step", "Behavior", "behavior"),
        ("Expression", "Function", "function"),
        ("BooleanExpression", "Predicate", "predicate"),
        ("MetadataFeature", "Metaclass", "metaclass"),
        ("Connector", "Association", "association"),
        ("Flow", "Interaction", "interaction"),
        ("Usage", "Classifier", "definition"),
    ] {
        let mut r = model("classifier T; feature x; typing x typed by T;");
        let x = r.resolve_qualified("x").unwrap();
        let t = r.resolve_qualified("T").unwrap();
        r.b.elements[x.0].ty = receiver;
        r.b.elements[t.0].ty = target;
        let compatibility = r.derived(x, property);
        assert!(
            matches!(compatibility,Derived::Value(DerivedValue::References(ref values)) if values.is_empty())
                || matches!(compatibility, Derived::Value(DerivedValue::Null)),
            "{receiver}.{property}: {compatibility:?}"
        );
        assert_eq!(
            derives(receiver, property),
            Derives::Passthrough,
            "{receiver}.{property}"
        );
        assert!(r.property(x, property).is_err(), "{receiver}.{property}");
        assert!(
            r.derived_exact(x, property).is_err(),
            "{receiver}.{property}"
        );
        assert_eq!(r.derived(x, property), compatibility);
        for alias in ["type", "behavior", "function"] {
            if crate::semantic_catalog::property(receiver, alias).is_some() {
                assert!(
                    r.property(x, alias).is_err(),
                    "{receiver}.{alias} must not bypass its effective redefinition"
                );
                assert!(r.derived_exact(x, alias).is_err(), "{receiver}.{alias}");
            }
        }
    }
}
#[test]
fn individual_predicate_does_not_turn_missing_inverse_type_into_exact_null() {
    let mut r = model("classifier T; feature x; typing x typed by T;");
    let x = r.resolve_qualified("x").unwrap();
    let t = r.resolve_qualified("T").unwrap();
    r.b.elements[x.0].ty = "OccurrenceUsage";
    r.b.elements[t.0].ty = "OccurrenceDefinition";
    r.b.elements[t.0]
        .props
        .insert("isIndividual", serde_json::json!(true));
    assert_eq!(
        r.derived(x, "individualDefinition"),
        Derived::Value(DerivedValue::Null)
    );
    assert_eq!(
        derives("OccurrenceUsage", "individualDefinition"),
        Derives::Passthrough
    );
    assert_eq!(
        r.derived_exact(x, "individualDefinition"),
        Err(PropertyError::Approximate)
    );
}
#[test]
fn payload_type_dereference_preserves_dependency_qualification() {
    let mut r =
        model("classifier T; feature holder {feature payload;} typing holder::payload typed by T;");
    let holder = r.resolve_qualified("holder").unwrap();
    let payload = r.resolve_qualified("holder::payload").unwrap();
    r.b.elements[holder.0].ty = "Flow";
    r.b.elements[payload.0].ty = "PayloadFeature";
    assert_eq!(r.d_payload_feature(holder), Some(payload));
    let compatibility = r.derived(holder, "payloadType");
    assert_eq!(
        compatibility,
        Derived::Value(DerivedValue::References(vec![]))
    );
    assert_eq!(derives("Flow", "payloadType"), Derives::Passthrough);
    assert_eq!(
        r.derived_exact(holder, "payloadType"),
        Err(PropertyError::Approximate)
    );
    assert_eq!(r.derived(holder, "payloadType"), compatibility);
}
#[test]
fn owned_relationship_type_and_instantiated_type_keep_distinct_contracts() {
    assert_eq!(derives("FeatureTyping", "type"), Derives::NotDeclared);
    assert_eq!(
        derives("InvocationExpression", "instantiatedType"),
        Derives::Exact
    );
    assert_eq!(derives("Step", "behavior"), Derives::Passthrough);
    assert_eq!(derives("Expression", "behavior"), Derives::Passthrough);
}
