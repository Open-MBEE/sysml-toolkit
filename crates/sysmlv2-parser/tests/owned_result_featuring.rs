#![cfg(feature = "json")]
use sysmlv2_parser::{
    json::{ClosurePolicy, Derived, ElementRef, ResolvedModel, model_to_compact_json},
    model::Model,
};
fn one(r: &mut ResolvedModel, e: ElementRef, name: &str) -> ElementRef {
    match r.derived(e, name) {
        Derived::Value(v) => v.element().unwrap(),
        other => panic!("{other:?}"),
    }
}
fn many(r: &mut ResolvedModel, e: ElementRef, name: &str) -> Vec<ElementRef> {
    match r.derived(e, name) {
        Derived::Value(v) => v.elements(),
        other => panic!("{other:?}"),
    }
}
#[test]
fn result_and_binding_end_featuring_are_real_local_relationships_with_stable_source() {
    let mut m = Model::new();
    assert!(
        m.add_source(
            "owned-featuring.kerml",
            "feature n;feature x=n;function F {return result;}feature call=F();"
        )
        .diagnostics
        .is_empty()
    );
    let compact = model_to_compact_json(&m);
    let mut r = ResolvedModel::build(&m);
    let source: Vec<_> = r.user_elements().map(|e| r.element_id(e)).collect();
    let expr = r
        .user_elements()
        .find(|&e| r.element_type(e) == "FeatureReferenceExpression")
        .unwrap();
    let mut expected = None;
    for policy in [
        ClosurePolicy::Passthrough,
        ClosurePolicy::Closure {
            include_implied: false,
        },
        ClosurePolicy::Closure {
            include_implied: true,
        },
    ] {
        r.set_closure_policy(policy);
        let result = one(&mut r, expr, "result");
        let binding = many(&mut r, expr, "ownedMember")
            .into_iter()
            .find(|&e| r.element_type(e) == "BindingConnector")
            .unwrap();
        let ends = many(&mut r, binding, "connectorEnd");
        assert_eq!(ends.len(), 2);
        let mut owners = vec![(result, expr)];
        owners.extend(ends.into_iter().map(|end| (end, binding)));
        let mut ids = Vec::new();
        for (owner, target) in owners {
            let rows: Vec<_> = r
                .implied_relationships(owner)
                .into_iter()
                .filter(|&e| r.element_type(e) == "TypeFeaturing")
                .collect();
            assert_eq!(rows.len(), 1);
            let properties = r.element_properties(rows[0]);
            assert_eq!(
                properties["featureOfType"]["@id"],
                r.element_id(owner).to_string()
            );
            assert_eq!(
                properties["featuringType"]["@id"],
                r.element_id(target).to_string()
            );
            assert_eq!(
                properties["owningRelatedElement"]["@id"],
                r.element_id(owner).to_string()
            );
            ids.push(r.element_id(rows[0]));
        }
        assert!(
            !r.implied_relationships(binding)
                .into_iter()
                .any(|e| r.element_type(e) == "TypeFeaturing")
        );
        assert!(r.property(expr, "ownedFeature").is_err());
        if let Some(old) = &expected {
            assert_eq!(&ids, old);
        } else {
            expected = Some(ids);
        }
    }
    assert_eq!(
        source,
        r.user_elements()
            .map(|e| r.element_id(e))
            .collect::<Vec<_>>()
    );
    assert_eq!(compact, model_to_compact_json(&m));
}
