#![cfg(feature = "json")]

use sysmlv2_parser::{
    json::{FeatureTypeIssue, ResolvedModel},
    model::Model,
};
const LIBRARY: &str = "standard library package Base {classifier Anything; feature things:Anything;} standard library package Occurrences {class Occurrence specializes Base::Anything; feature occurrences:Occurrence subsets Base::things;} standard library package Performances {behavior Performance specializes Occurrences::Occurrence; function Evaluation specializes Performance; step performances:Performance subsets Occurrences::occurrences; expr evaluations:Evaluation subsets performances;}";
fn fixture(source: &str) -> ResolvedModel {
    fixture_with_library(source, LIBRARY)
}
fn fixture_with_library(source: &str, library: &str) -> ResolvedModel {
    let mut m = Model::new();
    assert!(
        m.add_library_source("type-library.kerml", library)
            .diagnostics
            .is_empty()
    );
    assert!(
        m.add_source("type-user.kerml", source)
            .diagnostics
            .is_empty()
    );
    ResolvedModel::build(&m)
}
#[test]
fn complete_properties_share_one_projection_and_preserve_identity() {
    let mut r = fixture(
        "function F specializes Performances::Evaluation; expr e:F subsets Performances::evaluations;",
    );
    let e = r.resolve_qualified("e").unwrap();
    let f = r.resolve_qualified("F").unwrap();
    let before = r.elements().map(|e| r.element_id(e)).collect::<Vec<_>>();
    let first = r.feature_type_report(e);
    assert_eq!(first.types, Ok(vec![f]));
    assert_eq!(first.behavior, Ok(vec![f]));
    assert_eq!(first.function, Ok(Some(f)));
    assert!(first.steps > 0);
    for _ in 0..3 {
        let again = r.feature_type_report(e);
        assert_eq!(again.types, first.types);
        assert_eq!(again.function, first.function);
    }
    assert_eq!(
        r.elements().map(|e| r.element_id(e)).collect::<Vec<_>>(),
        before
    );
}
#[test]
fn incomplete_function_and_types_are_errors_never_empty_success() {
    let library = LIBRARY.replace(
        "expr evaluations:Evaluation subsets performances;",
        "expr evaluations:Evaluation;",
    );
    assert_ne!(library, LIBRARY);
    // Expression's Step ancestry supplies this omitted authored edge.
    let mut complete = fixture_with_library(
        "function F specializes Performances::Evaluation; expr e:F;",
        &library,
    );
    let e = complete.resolve_qualified("e").unwrap();
    let f = complete.resolve_qualified("F").unwrap();
    let report = complete.feature_type_report(e);
    assert_eq!(report.types, Ok(vec![f]));
    assert_eq!(report.function, Ok(Some(f)));

    // Remove the required canonical Feature, not merely its authored edge.
    // No authored endpoint is unresolved: the missing implied family itself
    // must remain an error, rather than becoming an empty successful result.
    let library = library.replace(
        "step performances:Performance subsets Occurrences::occurrences;",
        "",
    );
    let mut r = fixture_with_library(
        "function F specializes Performances::Evaluation; expr e:F; feature call=F();",
        &library,
    );
    assert!(r.resolve_qualified("Performances::evaluations").is_some());
    assert!(r.resolve_qualified("Performances::performances").is_none());
    assert!(r.resolve_qualified("Performances::Performance").is_some());
    let e = r.resolve_qualified("e").unwrap();
    let report = r.feature_type_report(e);
    assert_eq!(report.types, Err(FeatureTypeIssue::MissingRequiredFamilies));
    assert_eq!(
        report.function,
        Err(FeatureTypeIssue::MissingRequiredFamilies)
    );
    let call = r.resolve_qualified("call").unwrap();
    let invocation = r.members_via(call, "FeatureValue")[0];
    let report = r.feature_type_report(invocation);
    assert!(report.types.is_err());
    assert!(report.function.is_err());
    let f = r.resolve_qualified("F").unwrap();
    assert_eq!(
        r.feature_type_report(f).types,
        Err(FeatureTypeIssue::InvalidElement)
    );
}
#[test]
fn property_applicability_is_distinct_from_missing_evidence() {
    let mut r = fixture("feature x:Base::Anything subsets Base::things;");
    let x = r.resolve_qualified("x").unwrap();
    let anything = r.resolve_qualified("Base::Anything").unwrap();
    let report = r.feature_type_report(x);
    assert_eq!(report.types, Ok(vec![anything]));
    assert_eq!(report.behavior, Err(FeatureTypeIssue::NotApplicable));
    assert_eq!(report.function, Err(FeatureTypeIssue::NotApplicable));
    let mut m = Model::new();
    assert!(
        m.add_source("no-library.kerml", "feature x;")
            .diagnostics
            .is_empty()
    );
    let mut r = ResolvedModel::build(&m);
    let x = r.resolve_qualified("x").unwrap();
    assert_eq!(
        r.feature_type_report(x).types,
        Err(FeatureTypeIssue::MissingRequiredFamilies)
    );
}
