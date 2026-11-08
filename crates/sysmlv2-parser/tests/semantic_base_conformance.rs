//! A definition tagged with semantic metadata specializes the metadata's
//! `baseType` (KerML 9.2); when the base is a feature the definition
//! specializes the feature's declared types, and the redefinition
//! conformance check follows that base like a written one (public mirror
//! issue #16).

#![cfg(feature = "json")]

use sysmlv2_parser::{
    check::validate_model,
    json::{ClosurePolicy, ResolvedModel},
    model::Model,
};

const SOURCE: &str = "package SemanticBases {
    part def SystemContext;
    part systemContexts : SystemContext;
    metadata def <systemContext> SystemContextMetadata :> Metaobjects::SemanticMetadata {
        :>> baseType = systemContexts meta SysML::Type;
    }
    #systemContext part def ComponentContext;
    occurrence def ProjectTemplate {
        part context : SystemContext;
    }
    occurrence def MyProject :> ProjectTemplate {
        part myContext : ComponentContext :>> context;
    }
}";

fn model() -> Model {
    let mut model = Model::new();
    model
        .load_library_dir(&sysmlv2_testkit::library_dir())
        .unwrap();
    let unit = model.add_source("bases.sysml", SOURCE);
    assert!(unit.diagnostics.is_empty(), "{:?}", unit.diagnostics);
    model
}

#[test]
fn a_redefinition_conforms_through_the_semantic_base() {
    let messages: Vec<String> = validate_model(&model())
        .into_iter()
        .map(|(_, d)| d.message)
        .collect();
    assert!(
        !messages
            .iter()
            .any(|m| m.contains("none of its declared types conform")),
        "{messages:?}"
    );
}

#[test]
fn a_feature_valued_base_plans_the_features_types_as_superclassifiers() {
    let model = model();
    let mut r = ResolvedModel::build(&model);
    r.set_closure_policy(ClosurePolicy::Closure {
        include_implied: true,
    });
    let component = r
        .resolve_qualified("SemanticBases::ComponentContext")
        .unwrap();
    let system = r.resolve_qualified("SemanticBases::SystemContext").unwrap();
    let supers: Vec<String> = r
        .implied_relationships(component)
        .into_iter()
        .filter(|&row| r.element_type(row) == "Subclassification")
        .map(|row| {
            r.element_properties(row)["superclassifier"]["@id"]
                .as_str()
                .unwrap()
                .to_string()
        })
        .collect();
    assert!(
        supers.contains(&r.element_id(system).to_string()),
        "{supers:?}"
    );
    // The checked audit agrees with the planner: the tagged definition's
    // member lists certify, and its supertypes carry the base's type.
    let feature = r.property(component, "feature");
    assert!(feature.is_ok(), "{feature:?}");
}
