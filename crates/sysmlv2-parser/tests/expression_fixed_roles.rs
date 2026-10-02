#![cfg(feature = "json")]
use sysmlv2_parser::{
    json::{ClosurePolicy, ResolvedModel, model_to_compact_json},
    model::Model,
};

#[test]
fn actual_library_boolean_and_invariant_roles_preserve_sysml_bases_and_source_graph() {
    let library = sysmlv2_testkit::library_dir();
    if !library.is_dir() {
        eprintln!("skipping: standard library unavailable");
        return;
    }
    let mut model = Model::new();
    model.load_library_dir(&library).unwrap();
    for (path, source) in [
        (
            "fixed-roles.kerml",
            "package K { bool plain; inv true positive; inv false negative; }",
        ),
        (
            "fixed-roles.sysml",
            "package S { constraint plain {true} assert constraint positive {true} assert not constraint negative {false} }",
        ),
    ] {
        let parsed = model.add_source(path, source);
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    }
    let compact = model_to_compact_json(&model);
    let mut r = ResolvedModel::build(&model);
    let before: Vec<_> = r.user_elements().map(|e| r.element_id(e)).collect();
    let evaluations = r.resolve_qualified("Performances::evaluations").unwrap();
    let boolean = r
        .resolve_qualified("Performances::booleanEvaluations")
        .unwrap();
    let system_base = r
        .resolve_qualified("Constraints::constraintChecks")
        .unwrap();
    let cases: Vec<_> = [
        (
            "K::plain",
            "BooleanExpression",
            "Performances::booleanEvaluations",
            None,
            false,
        ),
        (
            "K::positive",
            "Invariant",
            "Performances::trueEvaluations",
            Some(false),
            false,
        ),
        (
            "K::negative",
            "Invariant",
            "Performances::falseEvaluations",
            Some(true),
            false,
        ),
        (
            "S::plain",
            "ConstraintUsage",
            "Performances::booleanEvaluations",
            None,
            true,
        ),
        (
            "S::positive",
            "AssertConstraintUsage",
            "Performances::trueEvaluations",
            Some(false),
            true,
        ),
        (
            "S::negative",
            "AssertConstraintUsage",
            "Performances::falseEvaluations",
            Some(true),
            true,
        ),
    ]
    .into_iter()
    .map(|(name, ty, role, negated, sysml)| {
        let owner = r.resolve_qualified(name).unwrap();
        assert_eq!(r.element_type(owner), ty);
        (owner, r.resolve_qualified(role).unwrap(), negated, sysml)
    })
    .collect();
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
        let mut ids = Vec::new();
        for &(owner, role, negated, sysml) in &cases {
            assert!(r.conforms_with_implied(owner, role));
            assert!(r.conforms_with_implied(owner, boolean));
            assert!(r.conforms_with_implied(owner, evaluations));
            if let Some(negated) = negated {
                assert_eq!(
                    r.property(owner, "isNegated").unwrap(),
                    serde_json::json!(negated)
                );
            }
            let edges = r.implied_relationships(owner);
            if sysml {
                assert!(r.conforms_with_implied(owner, system_base));
                // The new assert-specific role reaches constraintChecks;
                // only plain ConstraintUsage keeps that direct requirement.
                let direct = edges
                    .iter()
                    .filter(|&&edge| {
                        r.element_properties(edge)["subsettedFeature"]["@id"]
                            == r.element_id(system_base).to_string()
                    })
                    .count();
                assert_eq!(direct, usize::from(negated.is_none()));
            }
            assert!(
                !edges.iter().any(
                    |&edge| r.element_properties(edge)["subsettedFeature"]["@id"]
                        == r.element_id(evaluations).to_string()
                ),
                "redundant generic edge"
            );
            if role != boolean {
                assert!(
                    !edges.iter().any(
                        |&edge| r.element_properties(edge)["subsettedFeature"]["@id"]
                            == r.element_id(boolean).to_string()
                    ),
                    "redundant Boolean edge"
                );
            }
            ids.extend(edges.into_iter().map(|edge| r.element_id(edge)));
        }
        if let Some(expected) = &expected {
            assert_eq!(&ids, expected);
        } else {
            expected = Some(ids);
        }
    }
    assert_eq!(
        before,
        r.user_elements()
            .map(|e| r.element_id(e))
            .collect::<Vec<_>>()
    );
    assert_eq!(model_to_compact_json(&model), compact);
}
