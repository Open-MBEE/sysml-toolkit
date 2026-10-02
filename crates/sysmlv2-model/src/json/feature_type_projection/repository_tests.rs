//! Wire below feature_type_projection; adapter imports the pending shared seams.
use super::adapter::RepositoryTyping;
use super::{Evidence, Incomplete};
use crate::{json::ResolvedModel, model::Model};
fn model(source: &str) -> ResolvedModel {
    let mut model = Model::new();
    let parsed = model.add_source("typing.kerml", source);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    ResolvedModel::build(&model)
}
#[test]
fn standalone_typing_and_subsetting_use_source_identity_not_relationship_carrier() {
    let mut r = model("function F; feature x; typing x typed by F; feature y; subset y subsets x;");
    let y = r.resolve_qualified("y").unwrap().0;
    let f = r.resolve_qualified("F").unwrap().0;
    let mut steps = 0;
    let mut evidence = RepositoryTyping::new(&mut r.b, &mut steps).unwrap();
    let projection = evidence.project(y, &mut steps);
    assert_eq!(projection.candidates, vec![f]);
    assert_eq!(projection.graph_issue, None);
    assert_eq!(
        projection.function(&evidence),
        Err(Incomplete::MissingRequiredFamilies)
    );
}
#[test]
fn callee_membership_alone_never_becomes_an_expression_function() {
    let mut r = model("function F; feature call=F();");
    let call = r.resolve_qualified("call").unwrap();
    let expression = r.members_via(call, "FeatureValue")[0];
    let mut steps = 0;
    let mut evidence = RepositoryTyping::new(&mut r.b, &mut steps).unwrap();
    let projection = evidence.project(expression.0, &mut steps);
    assert!(projection.candidates.is_empty());
    assert_eq!(
        projection.function(&evidence),
        Err(Incomplete::MissingRequiredFamilies)
    );
}
#[test]
fn conjugation_preserves_own_typing_while_replacing_dependency_rules() {
    let mut r = model("function F; function G; feature x:F; feature y:G conjugates x;");
    let y = r.resolve_qualified("y").unwrap().0;
    let x = r.resolve_qualified("x").unwrap().0;
    let g = r.resolve_qualified("G").unwrap().0;
    let mut steps = 0;
    let mut evidence = RepositoryTyping::new(&mut r.b, &mut steps).unwrap();
    let input = evidence.inputs(y, &mut steps).unwrap();
    assert_eq!(input.typings, vec![g]);
    assert_eq!(input.features, vec![x]);
}
#[test]
fn cross_subsetting_does_not_contribute_typing_dependencies() {
    let mut r = model("function F; feature x:F; feature y subsets x;");
    let y = r.resolve_qualified("y").unwrap().0;
    let relation = r.b.elements[y]
        .owned_relationships
        .iter()
        .copied()
        .find(|&edge| r.b.elements[edge].ty == "Subsetting")
        .unwrap();
    r.b.elements[relation].ty = "CrossSubsetting";
    let mut steps = 0;
    let mut evidence = RepositoryTyping::new(&mut r.b, &mut steps).unwrap();
    let input = evidence.inputs(y, &mut steps).unwrap();
    assert!(input.features.is_empty());
}
#[test]
fn redundant_generic_endpoint_conflict_cannot_become_a_typing_witness() {
    let mut r = model("function F; function G; feature x:F;");
    let x = r.resolve_qualified("x").unwrap().0;
    let g = r.resolve_qualified("G").unwrap();
    let relation = r.b.elements[x]
        .owned_relationships
        .iter()
        .copied()
        .find(|&edge| r.b.elements[edge].ty == "FeatureTyping")
        .unwrap();
    let wrong_id = r.element_id(g).to_string();
    r.b.elements[relation]
        .props
        .insert("target", serde_json::json!([{"@id":wrong_id}]));
    let mut steps = 0;
    let mut evidence = RepositoryTyping::new(&mut r.b, &mut steps).unwrap();
    let projection = evidence.project(x, &mut steps);
    assert_eq!(
        projection.graph_issue,
        Some(Incomplete::InvalidRelationship)
    );
    assert!(projection.function(&evidence).is_err());
}

#[test]
fn conflicting_source_arrays_cannot_certify_the_other_feature_has_no_typing() {
    for key in ["source", "relatedElement"] {
        let mut r = model("function F; feature x:F; feature y;");
        let x = r.resolve_qualified("x").unwrap().0;
        let y = r.resolve_qualified("y").unwrap().0;
        let f = r.resolve_qualified("F").unwrap().0;
        let relationship = r.b.elements[x]
            .owned_relationships
            .iter()
            .copied()
            .find(|&edge| r.b.elements[edge].ty == "FeatureTyping")
            .unwrap();
        let target = crate::json::id_ref(r.b.elements[f].id);
        let source = crate::json::id_ref(r.b.elements[y].id);
        let values = if key == "source" {
            vec![source]
        } else {
            vec![source, target]
        };
        r.b.elements[relationship]
            .props
            .insert(key, crate::properties::Atom::Array(values));
        let mut steps = 0;
        let mut evidence = RepositoryTyping::new(&mut r.b, &mut steps).unwrap();
        let projection = evidence.project(y, &mut steps);
        assert_eq!(
            projection.graph_issue,
            Some(Incomplete::InvalidRelationship)
        );
    }
}

#[test]
fn redundant_composite_intersections_require_current_reciprocal_witnesses() {
    use crate::json::{ElementRef, FeatureTypeIssue};
    use serde_json::json;
    let mut m = Model::new();
    let unit = m.add_library_source("composition.kerml", "standard library package Base {classifier Anything; feature things : Anything;} standard library package Occurrences {class Occurrence specializes Base::Anything { composite feature suboccurrences : Occurrence subsets occurrences; } feature occurrences : Occurrence subsets Base::things;} standard library package Objects {struct Object specializes Occurrences::Occurrence { composite feature subobjects : Object subsets objects, Occurrences::Occurrence::suboccurrences intersects objects, Occurrences::Occurrence::suboccurrences;} feature objects : Object subsets Occurrences::occurrences;}");
    assert!(unit.diagnostics.is_empty());
    assert!(m.add_source("inherited.kerml", "feature external : Occurrences::Occurrence; class Container { composite feature nested subsets external; }").diagnostics.is_empty());
    let mut r = ResolvedModel::build(&m);
    let inherited_only = r.resolve_qualified("Container::nested").unwrap();
    assert!(r.feature_type_report(inherited_only).types.is_err());
    let unrelated = r.resolve_qualified("Objects::Object").unwrap();
    assert_eq!(
        crate::json::type_relations::TypeRelations::default().specializes(
            &mut r.b,
            inherited_only.0,
            unrelated.0,
            &mut 0
        ),
        crate::json::type_relations::RelationFact::Unknown
    );
    let feature = r.resolve_qualified("Objects::Object::subobjects").unwrap();
    let object = r.resolve_qualified("Objects::Object").unwrap();
    let occurrence = r.resolve_qualified("Occurrences::Occurrence").unwrap();
    let intersection = r.b.elements[feature.0]
        .owned_relationships
        .iter()
        .copied()
        .find(|&e| r.b.elements[e].ty == "Intersecting")
        .unwrap();
    assert_eq!(r.feature_type_report(feature).types, Ok(vec![object]));
    let properties = r.b.elements[intersection].props.clone();
    r.b.set(
        intersection,
        "intersectingType",
        json!({"@id": r.element_id(occurrence).to_string()}),
    );
    assert!(r.feature_type_report(feature).types.is_err());
    r.b.elements[intersection].props = properties.clone();
    assert_eq!(r.feature_type_report(feature).types, Ok(vec![object]));
    r.b.set(
        intersection,
        "owningRelatedElement",
        json!({"@id": r.element_id(occurrence).to_string()}),
    );
    assert!(r.feature_type_report(feature).types.is_err());
    r.b.elements[intersection].props = properties;
    assert_eq!(r.feature_type_report(feature).types, Ok(vec![object]));
    assert_eq!(
        r.feature_type_report_with_budget(feature, crate::eval::MAX_STEPS)
            .types,
        Err(FeatureTypeIssue::WorkLimit)
    );
    assert_eq!(
        r.feature_type_report(ElementRef(feature.0)).types,
        Ok(vec![object])
    );
}

#[test]
fn nested_composite_owner_proof_refuses_mutations_cycles_and_budget_then_retries() {
    use crate::{
        json::{FeatureTypeIssue, id_ref},
        model::GraphFormat,
    };
    use serde_json::json;
    for format in [GraphFormat::LegacyV2, GraphFormat::CanonicalV3] {
        let mut m = Model::with_graph_format(format);
        let library = "standard library package Base {classifier Anything; feature things : Anything;} standard library package Occurrences {class Occurrence specializes Base::Anything { composite feature suboccurrences : Occurrence subsets occurrences; } feature occurrences : Occurrence subsets Base::things;}";
        assert!(
            m.add_library_source("composition.kerml", library)
                .diagnostics
                .is_empty()
        );
        assert!(m.add_source("nested.sysml", "occurrence def Event; occurrence outer : Event :> Occurrences::occurrences { occurrence inner : Event; } occurrence cyclic : Event :> cyclic::inner { occurrence inner : Event; }").diagnostics.is_empty());
        let mut r = ResolvedModel::build(&m);
        let owner = r.resolve_qualified("outer").unwrap();
        let child = r.resolve_qualified("outer::inner").unwrap();
        let ty = r.resolve_qualified("Event").unwrap();
        let cycle = r.resolve_qualified("cyclic::inner").unwrap();
        assert!(r.feature_type_report(cycle).types.is_err());
        assert_eq!(r.feature_type_report(child).types, Ok(vec![ty]));
        assert_eq!(
            r.feature_type_report_with_budget(child, crate::eval::MAX_STEPS)
                .types,
            Err(FeatureTypeIssue::WorkLimit)
        );
        assert_eq!(r.feature_type_report(child).types, Ok(vec![ty]));

        // Ordinary typed Kernel Feature owners use the same complete owner
        // projection; the child remains a SysML OccurrenceUsage.
        let original_properties = r.b.elements[owner.0].props.clone();
        r.b.elements[owner.0].ty = "Feature";
        r.b.elements[owner.0]
            .props
            .insert("isVariable", json!(false));
        r.b.elements[owner.0]
            .props
            .insert("isComposite", json!(false));
        assert_eq!(r.feature_type_report(child).types, Ok(vec![ty]));
        r.b.elements[owner.0].ty = "OccurrenceUsage";
        r.b.elements[owner.0].props = original_properties;
        let properties = r.b.elements[owner.0].props.clone();
        for (name, value) in [
            ("isComposite", json!("invalid")),
            ("isVariation", json!(true)),
            ("isPortion", json!(true)),
            ("portionKind", json!("timeslice")),
        ] {
            r.b.elements[owner.0].props.insert(name, value);
            assert!(
                r.feature_type_report(child).types.is_err(),
                "{format:?} {name}"
            );
            r.b.elements[owner.0].props = properties.clone();
            assert_eq!(r.feature_type_report(child).types, Ok(vec![ty]));
        }
        r.b.metadata_of.insert(owner.0, vec![owner.0]);
        assert!(r.feature_type_report(child).types.is_err());
        r.b.metadata_of.insert(owner.0, Vec::new());
        assert_eq!(r.feature_type_report(child).types, Ok(vec![ty]));
        let membership = r.b.elements[child.0].owning_relationship.unwrap();
        let properties = r.b.elements[membership].props.clone();
        let wrong_owner = id_ref(r.b.elements[ty.0].id);
        r.b.elements[membership]
            .props
            .insert("owningRelatedElement", wrong_owner);
        assert!(r.feature_type_report(child).types.is_err());
        r.b.elements[membership].props = properties;
        assert_eq!(r.feature_type_report(child).types, Ok(vec![ty]));
        let typing = r.b.elements[owner.0]
            .owned_relationships
            .iter()
            .copied()
            .find(|&e| r.b.elements[e].ty == "FeatureTyping")
            .unwrap();
        let properties = r.b.elements[typing].props.clone();
        r.b.elements[typing]
            .props
            .insert("type", json!({"@ref": "Missing"}));
        assert!(r.feature_type_report(child).types.is_err());
        r.b.elements[typing].props = properties;
        assert_eq!(r.feature_type_report(child).types, Ok(vec![ty]));
        let mut evidence = RepositoryTyping::new(&mut r.b, &mut 0).unwrap();
        assert!(evidence.project(child.0, &mut 0).complete());
    }
}
