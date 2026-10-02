#![cfg(feature = "json")]
use sysmlv2_parser::{
    json::{ClosurePolicy, Derived, ResolvedModel, model_to_compact_json},
    model::Model,
};
#[test]
fn generated_result_redefines_the_actual_canonical_return_without_promoting_the_family() {
    let mut m = Model::new();
    m.add_library_source("result-library.kerml","standard library package Base {classifier Anything;feature things:Anything;} standard library package Occurrences {class Occurrence specializes Base::Anything;feature occurrences:Occurrence subsets Base::things;} standard library package Performances {behavior Performance specializes Occurrences::Occurrence;function Evaluation specializes Performance {return result;} step performances:Performance subsets Occurrences::occurrences;expr evaluations:Evaluation subsets performances;}");
    m.add_source("result-user.kerml", "feature n;feature x=n;");
    assert!(!m.has_errors());
    let compact = model_to_compact_json(&m);
    let mut r = ResolvedModel::build(&m);
    let source: Vec<_> = r.user_elements().map(|e| r.element_id(e)).collect();
    let expression = r
        .user_elements()
        .find(|&e| r.element_type(e) == "FeatureReferenceExpression")
        .unwrap();
    let target = r
        .resolve_qualified("Performances::Evaluation::result")
        .unwrap();
    let mut previous = None;
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
        let result = match r.derived(expression, "result") {
            Derived::Value(v) => v.element().unwrap(),
            other => panic!("{other:?}"),
        };
        let edges: Vec<_> = r
            .implied_relationships(result)
            .into_iter()
            .filter(|&e| r.element_type(e) == "Redefinition")
            .collect();
        assert_eq!(edges.len(), 1);
        let edge = edges[0];
        let properties = r.element_properties(edge);
        assert_eq!(
            properties["redefiningFeature"]["@id"],
            r.element_id(result).to_string()
        );
        assert_eq!(
            properties["redefinedFeature"]["@id"],
            r.element_id(target).to_string()
        );
        assert_eq!(
            properties["owningRelatedElement"]["@id"],
            r.element_id(result).to_string()
        );
        assert!(r.property(expression, "ownedFeature").is_err());
        let identity = (result, edge, r.element_id(result), r.element_id(edge));
        if let Some(previous) = previous {
            assert_eq!(identity, previous);
        }
        previous = Some(identity);
    }
    assert_eq!(
        source,
        r.user_elements()
            .map(|e| r.element_id(e))
            .collect::<Vec<_>>()
    );
    assert_eq!(compact, model_to_compact_json(&m));
}
