use super::{CheckedRow, PropertyError};
use crate::{
    json::{ClosurePolicy, ResolvedModel, TypeInputIssue},
    model::{GraphFormat, Model},
};
use serde_json::json;
use std::sync::Arc;

fn library(format: GraphFormat) -> Model {
    let mut model = Model::with_graph_format(format);
    for (name, text) in [
        (
            "kernel.kerml",
            "standard library package Base { classifier Anything { feature raw; } feature things : Anything; } standard library package Occurrences { class Occurrence specializes Base::Anything; feature occurrences : Occurrence subsets Base::things; } standard library package Objects { struct Object specializes Occurrences::Occurrence; feature objects : Object subsets Occurrences::occurrences; }",
        ),
        (
            "items.sysml",
            "standard library package Items { item def Item :> Objects::Object; ref item items : Item :> Objects::objects; }",
        ),
        (
            "parts.sysml",
            "standard library package Parts { part def Part :> Items::Item; ref part parts : Part :> Items::items; }",
        ),
    ] {
        let parsed = model.add_library_source(name, text);
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    }
    model
}
fn source(model: &mut Model) -> ResolvedModel {
    let parsed = model.add_source("user.sysml", "part def A { ref a; in ref input; out ref output; } part def B :> A { ref b; ref a2 :>> a; } part def Broken :> Missing { ref x; } port def Unsupported; part outer { ref child; }");
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let mut r = ResolvedModel::build(model);
    r.set_closure_policy(ClosurePolicy::Closure {
        include_implied: true,
    });
    r
}
#[test]
fn definition_usage_filters_complete_sequences_in_order_across_replay() {
    for format in [GraphFormat::LegacyV2, GraphFormat::CanonicalV3] {
        let mut lib = library(format);
        let prepared = lib.prepare_library().unwrap();
        let decoded = Arc::new(
            crate::prepared::PreparedLibrary::from_bytes(&prepared.to_bytes(147).unwrap(), 147)
                .unwrap(),
        );
        let mut expected = None;
        for mode in 0..3 {
            let mut model = if mode == 0 {
                library(format)
            } else {
                let mut model = Model::with_graph_format(format);
                Arc::clone(if mode == 1 { &prepared } else { &decoded })
                    .install(&mut model)
                    .unwrap();
                model
            };
            let mut r = source(&mut model);
            let b = r.resolve_qualified("B").unwrap();
            let mut names = Vec::new();
            for name in ["A::input", "A::output", "B::b", "B::a2"] {
                let e = r.resolve_qualified(name).unwrap();
                names.push(json!({"@id": r.element_id(e).to_string()}));
            }
            let usages = r.property(b, "usage").unwrap();
            assert_eq!(usages.as_array().unwrap().len(), names.len());
            for name in &names {
                assert!(usages.as_array().unwrap().contains(name));
            }
            let directed = r.property(b, "directedUsage").unwrap();
            assert_eq!(directed, json!([names[0], names[1]]));
            // The inherited Kernel Feature is not a Usage; the overwritten a is absent.
            let raw = r.resolve_qualified("Base::Anything::raw").unwrap();
            let features = r.property(b, "feature").unwrap();
            assert!(
                features
                    .as_array()
                    .unwrap()
                    .contains(&json!({"@id":r.element_id(raw).to_string()}))
            );
            let filtered: Vec<_> = features
                .as_array()
                .unwrap()
                .iter()
                .filter(|v| usages.as_array().unwrap().contains(v))
                .cloned()
                .collect();
            assert_eq!(usages, json!(filtered));
            let result = (usages, directed);
            assert_eq!(&result, expected.get_or_insert(result.clone()));
            let mut row = CheckedRow::default();
            assert!(row.read(&mut r, b, "usage").unwrap().is_ok());
            assert!(row.read(&mut r, b, "directedUsage").unwrap().is_ok());
            row.steps = crate::eval::MAX_STEPS;
            assert_eq!(
                row.read(&mut r, b, "usage"),
                Some(Err(PropertyError::IncompleteTypeFeatures(
                    TypeInputIssue::WorkLimit
                )))
            );
            assert!(r.property(b, "usage").is_ok());
            for path in ["Broken", "Unsupported", "outer"] {
                let e = r.resolve_qualified(path).unwrap();
                assert!(r.property(e, "usage").is_err(), "{path}");
                assert!(r.property(e, "directedUsage").is_err(), "{path}");
            }
            for policy in [
                ClosurePolicy::Passthrough,
                ClosurePolicy::Closure {
                    include_implied: false,
                },
            ] {
                r.set_closure_policy(policy);
                for property in ["usage", "directedUsage"] {
                    assert_eq!(r.property(b, property), Err(PropertyError::Approximate));
                }
            }
        }
    }
}

#[test]
fn definition_usage_projections_revalidate_cached_rows_and_leave_fidelity_qualified() {
    use crate::json::{Derives, conditional_property_capability, derives};
    let mut r = source(&mut library(GraphFormat::CanonicalV3));
    let b = r.resolve_qualified("B").unwrap();
    let member = r.resolve_qualified("B::b").unwrap();
    for (name, declaration) in [
        ("usage", "Systems-DefinitionAndUsage-Definition-usage"),
        (
            "directedUsage",
            "Systems-DefinitionAndUsage-Definition-directedUsage",
        ),
    ] {
        assert_eq!(derives("PartDefinition", name), Derives::Passthrough);
        assert!(
            conditional_property_capability(declaration)
                .unwrap()
                .requires_full_closure
        );
    }
    let mut row = CheckedRow::default();
    let before = row.read(&mut r, b, "directedUsage").unwrap().unwrap();
    r.b.elements[member.0]
        .props
        .insert("direction", json!("in"));
    let after = row.read(&mut r, b, "directedUsage").unwrap().unwrap();
    assert_ne!(before, after);
    assert_eq!(after, r.derived_exact(b, "directedUsage").unwrap());
    // The ownership inverse must still hold after warming the certificate.
    r.b.elements[member.0].owning_relationship = None;
    assert!(row.read(&mut r, b, "usage").unwrap().is_err());
    assert!(r.property(b, "usage").is_err());
    let mut empty = Model::new();
    empty.add_source("missing.sysml", "part def P { ref child; }");
    let mut r = ResolvedModel::build(&empty);
    r.set_closure_policy(ClosurePolicy::Closure {
        include_implied: true,
    });
    let p = r.resolve_qualified("P").unwrap();
    assert!(r.property(p, "usage").is_err());
}
