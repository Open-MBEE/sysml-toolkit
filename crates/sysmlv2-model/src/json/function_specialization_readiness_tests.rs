//! Private TypeRelations tests; include under type_relations module.
use super::*;
use crate::{json::ResolvedModel, model::Model};
fn fixture(evaluation_base: &str) -> ResolvedModel {
    let mut model = Model::new();
    let library = format!(
        "standard library package Base {{classifier Anything;}} standard library package Occurrences {{class Occurrence specializes Base::Anything;}} standard library package Performances {{behavior Performance specializes Occurrences::Occurrence; function Evaluation {evaluation_base};}}"
    );
    let parsed = model.add_library_source("function-bases.kerml", &library);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let parsed=model.add_source("functions.kerml","function F specializes Performances::Evaluation; function G specializes Performances::Evaluation;");
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    ResolvedModel::build(&model)
}
#[test]
fn exact_functions_have_negative_evidence_only_with_required_ancestor_paths() {
    let mut r = fixture("specializes Performance");
    let f = r.resolve_qualified("F").unwrap().0;
    let g = r.resolve_qualified("G").unwrap().0;
    let mut proof = TypeRelations::default();
    assert_eq!(proof.specializes(&mut r.b, f, g, &mut 0), RelationFact::No);
    let evaluation = r.resolve_qualified("Performances::Evaluation").unwrap().0;
    assert_eq!(
        proof.specializes(&mut r.b, f, evaluation, &mut 0),
        RelationFact::Yes
    );
    let mut r = fixture("");
    let f = r.resolve_qualified("F").unwrap().0;
    let g = r.resolve_qualified("G").unwrap().0;
    let mut proof = TypeRelations::default();
    assert!(
        proof.required_bases(&mut r.b, f, &mut 0).is_some(),
        "canonical names are present"
    );
    assert_eq!(
        proof.specializes(&mut r.b, f, g, &mut 0),
        RelationFact::Unknown,
        "name availability cannot manufacture a missing Evaluation→Performance path"
    );
}
