#![cfg(feature = "json")]
use sysmlv2_parser::{
    json::{ClosurePolicy, ResolvedModel, model_to_compact_json},
    model::Model,
};

#[test]
fn actual_library_constructor_ancestry_preserves_source_graph_and_no_owned_result_claim() {
    let library = sysmlv2_testkit::library_dir();
    if !library.is_dir() {
        eprintln!("skipping: standard library unavailable");
        return;
    }
    let mut model = Model::new();
    model.load_library_dir(&library).unwrap();
    assert!(model
        .add_source(
            "constructor-static.kerml",
            "class Box { feature item; } feature empty=new Box(); feature filled=new Box(item=1);"
        )
        .diagnostics
        .is_empty());
    let compact = model_to_compact_json(&model);
    let mut r = ResolvedModel::build(&model);
    let expressions: Vec<_> = r
        .user_elements()
        .filter(|&e| r.element_type(e) == "ConstructorExpression")
        .collect();
    assert_eq!(expressions.len(), 2);
    let target = r
        .resolve_qualified("Performances::constructorEvaluations")
        .unwrap();
    let target_id = r.element_id(target).to_string();
    let original_ids: Vec<_> = r.user_elements().map(|e| r.element_id(e)).collect();
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
            let required: Vec<_> = r
                .implied_relationships(expression)
                .into_iter()
                .filter(|&rel| {
                    r.element_type(rel) == "Subsetting"
                        && r.element_properties(rel)["subsettedFeature"]["@id"] == target_id
                })
                .collect();
            assert_eq!(required.len(), 1);
            assert!(matches!(
                r.model_level_evaluability(expression).classification,
                sysmlv2_parser::json::ModelLevelEvaluability::Unknown(_)
            ));
            edges.push(r.element_id(required[0]));
            assert_eq!(
                r.element_properties(required[0])["subsettingFeature"]["@id"],
                r.element_id(expression).to_string()
            );
            assert!(
                !r.owned_relationships(expression)
                    .into_iter()
                    .any(|rel| r.element_type(rel) == "ReturnParameterMembership")
            );
        }
        if let Some(ref expected) = expected {
            assert_eq!(&edges, expected);
        } else {
            expected = Some(edges);
        }
    }
    assert_eq!(
        original_ids,
        r.user_elements()
            .map(|e| r.element_id(e))
            .collect::<Vec<_>>()
    );
    assert_eq!(model_to_compact_json(&model), compact);
}
