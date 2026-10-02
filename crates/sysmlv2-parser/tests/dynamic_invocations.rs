#![cfg(feature = "json")]
use sysmlv2_parser::{
    json::{ClosurePolicy, ModelLevelEvaluability, ResolvedModel, model_to_compact_json},
    model::Model,
};

#[test]
fn public_dynamic_callee_and_argument_edges_preserve_source_and_report_qualification() {
    let mut model = Model::new();
    assert!(model.add_source("dynamic-sdk.kerml", "function F {in p; return result;} feature callee {feature nested;} feature call=F(1); feature other=callee();").diagnostics.is_empty());
    let compact = model_to_compact_json(&model);
    let mut r = ResolvedModel::build(&model);
    let calls: Vec<_> = r
        .user_elements()
        .filter(|&e| r.element_type(e) == "InvocationExpression")
        .collect();
    assert_eq!(calls.len(), 2);
    let f = r.resolve_qualified("F").unwrap();
    let p = r.resolve_qualified("F::p").unwrap();
    let callee = r.resolve_qualified("callee").unwrap();
    let source_ids: Vec<_> = r.user_elements().map(|e| r.element_id(e)).collect();
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
        let mut edges = Vec::new();
        for (&call, (kind, target, key)) in calls.iter().zip([
            ("FeatureTyping", f, "type"),
            ("Subsetting", callee, "subsettedFeature"),
        ]) {
            assert!(r.feature_type_report(call).types.is_err());
            let rows: Vec<_> = r
                .implied_relationships(call)
                .into_iter()
                .filter(|&row| {
                    r.element_type(row) == kind
                        && r.element_properties(row)[key]["@id"] == r.element_id(target).to_string()
                })
                .collect();
            assert_eq!(rows.len(), 1);
            edges.push(r.element_id(rows[0]));
            assert_eq!(
                r.element_properties(rows[0])["owningRelatedElement"]["@id"],
                r.element_id(call).to_string()
            );
            assert!(
                !r.owned_relationships(call)
                    .iter()
                    .any(|&row| r.element_type(row) == "ReturnParameterMembership")
            );
            assert!(r.feature_type_report(call).types.is_err());
            assert!(matches!(
                r.model_level_evaluability(call).classification,
                ModelLevelEvaluability::Unknown(_)
            ));
        }
        let user: Vec<_> = r.user_elements().collect();
        let mut positional = Vec::new();
        for candidate in user {
            for row in r.implied_relationships(candidate) {
                if r.element_type(row) == "Redefinition"
                    && r.element_properties(row)["redefinedFeature"]["@id"]
                        == r.element_id(p).to_string()
                {
                    positional.push(r.element_id(row));
                }
            }
        }
        assert_eq!(positional.len(), 1);
        edges.extend(positional);
        if let Some(old) = &expected {
            assert_eq!(old, &edges);
        } else {
            expected = Some(edges);
        }
    }
    assert_eq!(
        source_ids,
        r.user_elements()
            .map(|e| r.element_id(e))
            .collect::<Vec<_>>()
    );
    assert_eq!(compact, model_to_compact_json(&model));
}
