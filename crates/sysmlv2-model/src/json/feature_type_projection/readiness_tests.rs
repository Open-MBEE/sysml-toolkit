//! Repository tests for the bounded namespace-owned kernel typing certificate.
use super::{adapter::RepositoryTyping, *};
use crate::{json::ResolvedModel, model::Model};
const LIBRARY: &str = "standard library package Base {classifier Anything; feature things:Anything;} standard library package Occurrences {class Occurrence specializes Base::Anything; feature occurrences:Occurrence subsets Base::things;} standard library package Performances {behavior Performance specializes Occurrences::Occurrence; function Evaluation specializes Performance; step performances:Performance subsets Occurrences::occurrences; expr evaluations:Evaluation subsets performances;}";
fn fixture(user: &str) -> ResolvedModel {
    let mut m = Model::new();
    assert!(
        m.add_library_source("typing-bases.kerml", LIBRARY)
            .diagnostics
            .is_empty()
    );
    assert!(
        m.add_source("typing-ready.kerml", user)
            .diagnostics
            .is_empty()
    );
    ResolvedModel::build(&m)
}
fn replay_fixtures(user: &str) -> Vec<ResolvedModel> {
    use crate::{libcache::LibraryCache, prepared::PreparedLibrary};
    use std::sync::Arc;
    let mut base = Model::new();
    assert!(
        base.add_library_source("typing-bases.kerml", LIBRARY)
            .diagnostics
            .is_empty()
    );
    base.record_library_cache();
    ResolvedModel::build(&base);
    let cache =
        LibraryCache::from_bytes(&base.take_recorded_library_cache().unwrap().to_bytes()).unwrap();
    let prepared = base.prepare_library().unwrap();
    let decoded =
        Arc::new(PreparedLibrary::from_bytes(&prepared.to_bytes(79).unwrap(), 79).unwrap());
    (0..4)
        .map(|mode| {
            let mut model = Model::new();
            match mode {
                2 => Arc::clone(&prepared).install(&mut model).unwrap(),
                3 => Arc::clone(&decoded).install(&mut model).unwrap(),
                _ => {
                    model.add_library_source("typing-bases.kerml", LIBRARY);
                    if mode == 1 {
                        model.set_library_cache(cache.clone());
                    }
                }
            }
            assert!(
                model
                    .add_source("typing-ready.kerml", user)
                    .diagnostics
                    .is_empty()
            );
            ResolvedModel::build(&model)
        })
        .collect()
}
#[test]
fn exact_expression_function_is_reduced_from_complete_shared_closure() {
    let mut expected = None;
    for mut r in replay_fixtures(
        "function F specializes Performances::Evaluation; expr e:F subsets Performances::evaluations;",
    ) {
        let expression = r.resolve_qualified("e").unwrap().0;
        let function = r.resolve_qualified("F").unwrap().0;
        let id = r.b.elements[function].id;
        if let Some(expected) = expected {
            assert_eq!(id, expected);
        } else {
            expected = Some(id);
        }
        let before: Vec<_> = r.user_elements().map(|e| r.element_id(e)).collect();
        let mut proof = RepositoryTyping::new(&mut r.b, &mut 0).unwrap();
        let result = proof.project(expression, &mut 0);
        assert!(result.complete(), "{result:?}");
        assert_eq!(result.candidates, [function]);
        assert_eq!(result.function(&proof), Ok(Some(function)));
        assert_eq!(
            proof.project(expression, &mut 0).function(&proof),
            Ok(Some(function))
        );
        drop(proof);
        assert_eq!(
            before,
            r.user_elements()
                .map(|e| r.element_id(e))
                .collect::<Vec<_>>()
        );
    }
}
#[test]
fn feature_subsetting_closure_and_step_behavior_use_the_same_complete_inputs() {
    let mut r = fixture(
        "function F specializes Performances::Evaluation; feature base:F subsets Performances::evaluations; step s subsets base;",
    );
    let step = r.resolve_qualified("s").unwrap().0;
    let function = r.resolve_qualified("F").unwrap().0;
    let mut proof = RepositoryTyping::new(&mut r.b, &mut 0).unwrap();
    let result = proof.project(step, &mut 0);
    assert_eq!(result.behaviors(&proof), Ok(vec![function]));
}
#[test]
fn generic_expression_base_establishes_the_required_source_path() {
    let mut r = fixture("function F specializes Performances::Evaluation; expr e:F;");
    let expression = r.resolve_qualified("e").unwrap().0;
    let function = r.resolve_qualified("F").unwrap().0;
    let mut proof = RepositoryTyping::new(&mut r.b, &mut 0).unwrap();
    let result = proof.project(expression, &mut 0);
    assert_eq!(result.function(&proof), Ok(Some(function)));
}
#[test]
fn existing_required_name_without_a_source_path_is_not_completeness() {
    // The source now receives its required evaluations base automatically.
    // Keep the negative control by breaking an actual canonical ancestor edge:
    // Evaluation still exists, but no longer specializes Performance.
    let library = LIBRARY.replace(
        "function Evaluation specializes Performance;",
        "function Evaluation;",
    );
    let mut model = Model::new();
    assert!(
        model
            .add_library_source("typing-broken-base.kerml", &library)
            .diagnostics
            .is_empty()
    );
    assert!(
        model
            .add_source(
                "typing-ready.kerml",
                "function F specializes Performances::Evaluation; expr e:F;"
            )
            .diagnostics
            .is_empty()
    );
    let mut r = ResolvedModel::build(&model);
    let evaluation = r.resolve_qualified("Performances::Evaluation").unwrap().0;
    let performance = r.resolve_qualified("Performances::Performance").unwrap().0;
    assert_eq!(
        crate::json::type_relations::TypeRelations::default().specializes(
            &mut r.b,
            evaluation,
            performance,
            &mut 0
        ),
        crate::json::type_relations::RelationFact::Unknown
    );
    let expression = r.resolve_qualified("e").unwrap().0;
    let mut proof = RepositoryTyping::new(&mut r.b, &mut 0).unwrap();
    let result = proof.project(expression, &mut 0);
    assert_eq!(
        result.function(&proof),
        Err(Incomplete::AmbiguousSpecialization)
    );
}

#[test]
fn metadata_valuation_owned_context_and_invocation_remain_outside_bounded_domain() {
    for user in [
        "function F specializes Performances::Evaluation; metaclass Mark; expr e:F subsets Performances::evaluations; @Mark about e;",
        "function F specializes Performances::Evaluation; feature e:F subsets Performances::evaluations=1;",
        "function F specializes Performances::Evaluation; class C {expr e:F subsets Performances::evaluations;}",
    ] {
        let mut r = fixture(user);
        let feature = r
            .resolve_qualified("e")
            .or_else(|| r.resolve_qualified("C::e"))
            .unwrap()
            .0;
        let mut proof = RepositoryTyping::new(&mut r.b, &mut 0).unwrap();
        assert!(proof.project(feature, &mut 0).function(&proof).is_err());
    }
}
#[test]
fn invocation_waits_for_accepted_dynamic_typing_lifecycle() {
    let mut r = fixture("function F specializes Performances::Evaluation; feature call=F();");
    let invocation =
        r.b.elements
            .iter()
            .position(|e| e.ty == "InvocationExpression")
            .unwrap();
    let mut proof = RepositoryTyping::new(&mut r.b, &mut 0).unwrap();
    assert_eq!(
        proof.project(invocation, &mut 0).function(&proof),
        Err(Incomplete::MissingRequiredFamilies)
    );
}
#[test]
fn actual_standard_library_supports_explicit_function_identity() {
    let library = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../spec-refs/SysML-v2-Release/sysml.library");
    if !library.exists() {
        eprintln!("skipping: standard library not present");
        return;
    }
    let mut model = Model::new();
    model.load_library_dir(&library).unwrap();
    assert!(model.add_source("typing-actual.kerml","function F specializes Performances::Evaluation; expr e:F subsets Performances::evaluations;").diagnostics.is_empty());
    let mut r = ResolvedModel::build(&model);
    let feature = r.resolve_qualified("e").unwrap().0;
    let function = r.resolve_qualified("F").unwrap().0;
    // Exercise actual library identities without legacy resolver/positional warming.
    r.b.positional_redefinitions = None;
    r.b.base_cache.fill(None);
    let mut proof = RepositoryTyping::new(&mut r.b, &mut 0).unwrap();
    let projection = proof.project(feature, &mut 0);
    assert_eq!(
        projection.function(&proof),
        Ok(Some(function)),
        "{projection:?}"
    );
}

#[test]
fn exhausted_valid_report_always_reports_work_limit_with_warm_indexes() {
    use crate::json::{ElementRef, FeatureTypeIssue};
    let mut r = fixture(
        "function F specializes Performances::Evaluation; expr e:F subsets Performances::evaluations;",
    );
    let e = r.resolve_qualified("e").unwrap();
    assert!(r.feature_type_report(e).types.is_ok());
    // Exercise cutoffs inside carrier, conjugation, owner and provider proofs,
    // after index startup is already paid. Every exhaustion has one public cause.
    for remaining in 0..180 {
        let report =
            r.feature_type_report_with_budget(ElementRef(e.0), crate::eval::MAX_STEPS - remaining);
        if report.steps > crate::eval::MAX_STEPS {
            assert_eq!(
                report.types,
                Err(FeatureTypeIssue::WorkLimit),
                "remaining={remaining}"
            );
            assert_eq!(
                report.function,
                Err(FeatureTypeIssue::WorkLimit),
                "remaining={remaining}"
            );
        }
    }
}

#[test]
fn cold_report_budget_never_publishes_partial_positional_evidence() {
    use crate::json::FeatureTypeIssue;
    let mut r = fixture(
        "function F specializes Performances::Evaluation; expr e:F subsets Performances::evaluations;",
    );
    let e = r.resolve_qualified("e").unwrap();
    // Warm only the immutable row and typing indexes, not positional planning.
    drop(RepositoryTyping::new(&mut r.b, &mut 0).unwrap());
    r.b.positional_redefinitions = None;
    let report = r.feature_type_report_with_budget(e, crate::eval::MAX_STEPS - 100);
    assert_eq!(report.types, Err(FeatureTypeIssue::WorkLimit));
    assert!(r.b.positional_redefinitions.is_none());
    assert!(!r.b.positional_planning);
    let report = r.feature_type_report(e);
    assert!(report.types.is_ok(), "{report:?}");
    assert!(r.b.positional_redefinitions.is_some());
}

#[test]
fn external_name_configuration_keeps_one_retained_authority_during_cold_report() {
    let mut r = fixture(
        "function F specializes Performances::Evaluation; expr e:F subsets Performances::evaluations;",
    );
    let e = r.resolve_qualified("e").unwrap();
    let function = r.resolve_qualified("F").unwrap();
    r.set_library_names(&std::collections::HashMap::from([(
        uuid::Uuid::new_v4().to_string(),
        vec!["Unrelated".into(), "external".into()],
    )]));
    let mut proof = RepositoryTyping::new(&mut r.b, &mut 0).unwrap();
    assert_eq!(
        proof.project(e.0, &mut 0).function(&proof),
        Ok(Some(function.0))
    );
    assert_eq!(
        proof.project(e.0, &mut 0).function(&proof),
        Ok(Some(function.0))
    );
}

#[test]
fn accepted_dynamic_reports_reuse_one_authority_without_cold_static_preparation() {
    let mut r = fixture(
        "function F specializes Performances::Evaluation {return result;} expr e:F; feature call=F();",
    );
    let expression = r.resolve_qualified("e").unwrap().0;
    let function = r.resolve_qualified("F").unwrap().0;
    let invocation = r
        .user_elements()
        .find(|&e| r.element_type(e) == "InvocationExpression")
        .unwrap();
    r.implied_relationships(invocation);
    assert!(r.b.effective_dynamic_plan().is_some());
    r.b.supported_implied = None;
    r.b.positional_redefinitions = None;
    r.b.base_cache.fill(None);
    let accepted = r.b.dynamic_graph.clone().unwrap();
    let count = r.b.elements.len();
    for _ in 0..2 {
        let mut proof = RepositoryTyping::new(&mut r.b, &mut 0).unwrap();
        let report = proof.project(expression, &mut 0);
        assert!(report.complete(), "{report:?}");
        assert_eq!(report.function(&proof), Ok(Some(function)));
        assert_eq!(
            proof.project(expression, &mut 0).function(&proof),
            Ok(Some(function))
        );
        drop(proof);
        assert!(r.b.supported_implied.is_none());
        assert!(r.b.positional_redefinitions.is_none());
        assert!(std::sync::Arc::ptr_eq(
            &accepted,
            r.b.dynamic_graph.as_ref().unwrap()
        ));
        assert_eq!(r.b.elements.len(), count);
    }
}
