#![cfg(feature = "json")]
use sysmlv2_parser::{json::ResolvedModel, model::Model};
#[test]
fn alias_identity_remains_fixed_when_its_target_is_excluded() {
    let mut m = Model::new();
    m.add_source(
        "alias.kerml",
        "class Base { feature x; alias ax for Child::x; }
        class Child specializes Base { feature x subsets ax; }",
    );
    assert!(!m.has_errors());
    let mut r = ResolvedModel::build(&m);
    let x = r.resolve_qualified("Child::x").unwrap();
    let base = r.resolve_qualified("Base").unwrap();
    let alias = r
        .owned_relationships(base)
        .into_iter()
        .find(|&e| {
            r.element_properties(e)
                .get("memberName")
                .and_then(|v| v.as_str())
                == Some("ax")
        })
        .unwrap();
    assert_eq!(
        r.element_properties(alias)["memberElement"]["@id"],
        r.element_id(x).to_string()
    );
    let relation = r
        .owned_relationships(x)
        .into_iter()
        .find(|&e| r.element_type(e) == "Subsetting")
        .unwrap();
    assert_eq!(
        r.element_properties(relation)["subsettedFeature"]["@ref"],
        "ax"
    );
    let unresolved = r.unresolved_references();
    assert_eq!(unresolved.len(), 1);
    assert_eq!(unresolved[0].owner, relation);
    assert_eq!(unresolved[0].spelling, "ax");
    assert_eq!(unresolved[0].unit, 0);
    assert!(r.blocked_references().is_empty());
}

#[test]
fn iterative_selection_preserves_deep_inheritance_after_preparation() {
    let mut source = String::from("class T0 { feature x; } alias enable for T0;");
    for i in 1..80 {
        source += &format!(" class T{i} specializes T{};", i - 1);
    }
    let mut library = Model::new();
    library.add_library_source("deep.kerml", &source);
    let prepared = library.prepare_library().unwrap();
    let decoded = std::sync::Arc::new(
        sysmlv2_parser::prepared::PreparedLibrary::from_bytes(&prepared.to_bytes(7).unwrap(), 7)
            .unwrap(),
    );
    for mode in 0..3 {
        let mut m = Model::new();
        match mode {
            0 => {
                m.add_library_source("deep.kerml", &source);
            }
            1 => {
                prepared.clone().install(&mut m).unwrap();
            }
            _ => {
                decoded.clone().install(&mut m).unwrap();
            }
        }
        m.add_source("use.kerml", "feature selected references T79::x;");
        let mut r = ResolvedModel::build(&m);
        let x = r.resolve_qualified("T0::x").unwrap();
        assert_eq!(r.resolve_qualified("T79::x"), Some(x));
        let selected = r.resolve_qualified("selected").unwrap();
        let edge = r
            .owned_relationships(selected)
            .into_iter()
            .find(|&e| r.element_type(e) == "ReferenceSubsetting")
            .unwrap();
        assert_eq!(
            r.element_properties(edge)["referencedFeature"]["@id"],
            r.element_id(x).to_string()
        );
    }
}

#[test]
fn a_new_implicit_root_invalidates_prepared_absence_proofs() {
    let source = "class Receiver; class Source { feature x; alias ax for x; }
        class Child specializes Source;";
    let mut library = Model::new();
    library.add_library_source("library.kerml", source);
    let prepared = library.prepare_library().unwrap();
    let decoded = std::sync::Arc::new(
        sysmlv2_parser::prepared::PreparedLibrary::from_bytes(&prepared.to_bytes(7).unwrap(), 7)
            .unwrap(),
    );
    for mode in 0..3 {
        let mut m = Model::new();
        match mode {
            0 => {
                m.add_library_source("library.kerml", source);
            }
            1 => {
                prepared.clone().install(&mut m).unwrap();
            }
            _ => {
                decoded.clone().install(&mut m).unwrap();
            }
        }
        m.add_source(
            "root.kerml",
            "package Occurrences { class Occurrence { feature token; } }
            feature chosen references Receiver::token;",
        );
        let mut r = ResolvedModel::build(&m);
        let token = r
            .resolve_qualified("Occurrences::Occurrence::token")
            .unwrap();
        assert_eq!(r.resolve_qualified("Receiver::token"), Some(token));
        let chosen = r.resolve_qualified("chosen").unwrap();
        let edge = r
            .owned_relationships(chosen)
            .into_iter()
            .find(|&e| r.element_type(e) == "ReferenceSubsetting")
            .unwrap();
        assert_eq!(
            r.element_properties(edge)["referencedFeature"]["@id"],
            r.element_id(token).to_string()
        );
    }
}

#[test]
fn external_names_invalidate_prepared_recorded_projections() {
    let mut library = Model::new();
    library.add_library_source(
        "external.kerml",
        "class Source { feature x; alias ax for x; } class Child specializes Source;",
    );
    let prepared = library.prepare_library().unwrap();
    let names = std::collections::HashMap::from([(
        uuid::Uuid::new_v5(&uuid::Uuid::NAMESPACE_OID, b"external occurrence").to_string(),
        vec!["Occurrences".to_owned(), "Occurrence".to_owned()],
    )]);
    let build = || {
        let mut m = Model::new();
        prepared.clone().install(&mut m).unwrap();
        m.add_source("user.kerml", "feature user;");
        ResolvedModel::build(&m)
    };
    let mut warm = build();
    assert_eq!(warm.resolve_qualified("Child::x"), None);
    warm.set_library_names(&names);
    let mut cold = build();
    cold.set_library_names(&names);
    for name in ["Child::ax", "Child::x"] {
        let actual = warm.resolve_qualified(name);
        let expected = cold.resolve_qualified(name);
        assert_eq!(actual, expected, "{name}");
        assert!(
            expected.is_some(),
            "external base requires contextual fallback"
        );
    }
}
