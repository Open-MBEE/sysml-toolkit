#![cfg(feature = "json")]
use sysmlv2_parser::{
    json::{ClosurePolicy, ResolvedModel, model_to_compact_json},
    model::Model,
};

#[test]
fn actual_library_expression_ancestry_preserves_compact_graph_and_specific_bases() {
    let library = sysmlv2_testkit::library_dir();
    if !library.is_dir() {
        eprintln!("skipping: standard library unavailable");
        return;
    }
    let mut model = Model::new();
    model.load_library_dir(&library).unwrap();
    assert!(model.add_source("expression-static.kerml", "class C {feature slot;} feature receiver:C; feature referenced=receiver; feature chained=receiver.slot; feature body={1}; feature plus=1+2; feature indexed=receiver#(1); feature selected=receiver.?{in p; true}; feature collected=receiver.{in p; p}; expr declared; expr already subsets Performances::evaluations; bool boolean; inv true invariant {true} function F {return result;} feature invoked=F(); feature constructed=new C();").diagnostics.is_empty());
    let compact = model_to_compact_json(&model);
    let mut r = ResolvedModel::build(&model);
    let target = r.resolve_qualified("Performances::evaluations").unwrap();
    let target_id = r.element_id(target).to_string();
    let kinds = [
        "Expression",
        "FeatureReferenceExpression",
        "FeatureChainExpression",
        "OperatorExpression",
        "IndexExpression",
        "SelectExpression",
        "CollectExpression",
        "BooleanExpression",
        "Invariant",
        "InvocationExpression",
        "ConstructorExpression",
        "LiteralInteger",
        "LiteralBoolean",
    ];
    let expressions: Vec<_> = r
        .user_elements()
        .filter(|&e| kinds.contains(&r.element_type(e)))
        .collect();
    for kind in kinds {
        assert!(
            expressions.iter().any(|&e| r.element_type(e) == kind),
            "missing fixture {kind}"
        );
    }
    let before: Vec<_> = r.user_elements().map(|e| r.element_id(e)).collect();
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
        for &expression in &expressions {
            assert!(
                r.conforms_with_implied(expression, target),
                "{}",
                r.element_type(expression)
            );
            let specific = match r.element_type(expression) {
                "ConstructorExpression" => Some("Performances::constructorEvaluations"),
                "LiteralInteger" => Some("Performances::literalIntegerEvaluations"),
                "LiteralBoolean" => Some("Performances::literalBooleanEvaluations"),
                _ => None,
            };
            let relationships = r.implied_relationships(expression);
            if let Some(specific) = specific {
                let base = r.resolve_qualified(specific).unwrap();
                assert!(r.conforms_with_implied(expression, base));
                assert!(
                    !relationships
                        .iter()
                        .any(|&rel| r.element_properties(rel)["subsettedFeature"]["@id"]
                            == target_id),
                    "redundant generic base on {}",
                    r.element_type(expression)
                );
            }
            edges.extend(relationships.into_iter().map(|rel| r.element_id(rel)));
        }
        if let Some(expected) = &expected {
            assert_eq!(&edges, expected);
        } else {
            expected = Some(edges);
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

#[test]
fn parsed_sysml_expression_usages_keep_specific_roles_without_redundant_evaluations() {
    let library = sysmlv2_testkit::library_dir();
    if !library.is_dir() {
        eprintln!("skipping: standard library unavailable");
        return;
    }
    let mut model = Model::new();
    model.load_library_dir(&library).unwrap();
    assert!(model.add_source("expression-usages.sysml", "package P { calc calculated {1} constraint constrained {true} assert constraint asserted {true} }").diagnostics.is_empty());
    let compact = model_to_compact_json(&model);
    let mut r = ResolvedModel::build(&model);
    let source_ids: Vec<_> = r.user_elements().map(|e| r.element_id(e)).collect();
    let evaluations = r.resolve_qualified("Performances::evaluations").unwrap();
    let evaluations_id = r.element_id(evaluations).to_string();
    let usages: Vec<_> = [
        (
            "P::calculated",
            "CalculationUsage",
            "Calculations::calculations",
        ),
        (
            "P::constrained",
            "ConstraintUsage",
            "Constraints::constraintChecks",
        ),
        (
            "P::asserted",
            "AssertConstraintUsage",
            "Constraints::assertedConstraintChecks",
        ),
    ]
    .into_iter()
    .map(|(name, metaclass, role)| {
        let element = r.resolve_qualified(name).unwrap();
        assert_eq!(r.element_type(element), metaclass);
        let role = r.resolve_qualified(role).unwrap();
        (element, role)
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
        let mut relationship_ids = Vec::new();
        for &(usage, role) in &usages {
            assert!(r.conforms_with_implied(usage, role));
            assert!(r.conforms_with_implied(usage, evaluations));
            let role_id = r.element_id(role).to_string();
            let relationships = r.implied_relationships(usage);
            assert_eq!(
                relationships
                    .iter()
                    .filter(|&&rel| {
                        r.element_type(rel) == "Subsetting"
                            && r.element_properties(rel)["subsettedFeature"]["@id"] == role_id
                    })
                    .count(),
                1,
                "specific role on {}",
                r.element_type(usage)
            );
            assert!(
                !relationships.iter().any(|&rel| {
                    r.element_type(rel) == "Subsetting"
                        && r.element_properties(rel)["subsettedFeature"]["@id"] == evaluations_id
                }),
                "redundant generic role on {}",
                r.element_type(usage)
            );
            relationship_ids.extend(relationships.into_iter().map(|rel| r.element_id(rel)));
        }
        if let Some(expected) = &expected {
            assert_eq!(&relationship_ids, expected);
        } else {
            expected = Some(relationship_ids);
        }
    }
    assert_eq!(
        source_ids,
        r.user_elements()
            .map(|e| r.element_id(e))
            .collect::<Vec<_>>()
    );
    assert_eq!(model_to_compact_json(&model), compact);
}
