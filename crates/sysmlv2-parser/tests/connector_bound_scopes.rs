#![cfg(feature = "json")]

use sysmlv2_parser::{json::ResolvedModel, model::Model};

#[test]
fn connector_bounds_use_body_members_without_recapturing_end_targets() {
    let source = "package P {
        item a; item b; attribute n = 99;
        succession link first [n] a then [n] b { attribute n = 1; }
        connection c connect [count] a to [count] b { attribute count = 2; }
        succession outer first [n] a then [n] b;
    }";
    let mut model = Model::new();
    model.add_source("bounds.sysml", source);
    assert!(!model.has_errors(), "{:?}", model.units()[0].diagnostics);
    let mut r = ResolvedModel::build(&model);
    assert!(
        r.unresolved_references().is_empty(),
        "{:?}",
        r.unresolved_references()
    );
    let outer = r.resolve_qualified("P::n").unwrap();
    assert_eq!(r.references_to(outer).len(), 2);
    for name in ["P::link::n", "P::c::count"] {
        let bound = r.resolve_qualified(name).unwrap();
        assert_eq!(r.references_to(bound).len(), 2, "{name}");
    }
    for name in ["P::a", "P::b"] {
        let target = r.resolve_qualified(name).unwrap();
        assert_eq!(r.references_to(target).len(), 3, "{name}");
    }
}

#[test]
fn causation_library_end_bounds_resolve_body_variables() {
    let mut model = Model::new();
    model
        .load_library_dir(&sysmlv2_testkit::library_dir())
        .unwrap();
    let r = ResolvedModel::build(&model);
    let failures: Vec<_> = r
        .unresolved_references()
        .into_iter()
        .filter(|reference| {
            model
                .unit(reference.unit)
                .name
                .ends_with("CausationConnections.sysml")
                && matches!(reference.spelling.as_str(), "nCauses" | "nEffects")
        })
        .collect();
    assert!(failures.is_empty(), "{failures:?}");
}

#[test]
fn prepared_connector_bounds_keep_local_resolution() {
    let mut source = Model::new();
    source.add_library_source(
        "bounds.sysml",
        "package L { item a; item b; succession link first [n] a then [n] b { attribute n = 1; } }",
    );
    let prepared = source.prepare_library().unwrap();
    let decoded = std::sync::Arc::new(
        sysmlv2_parser::prepared::PreparedLibrary::from_bytes(&prepared.to_bytes(1).unwrap(), 1)
            .unwrap(),
    );
    for library in [prepared, decoded] {
        let mut model = Model::new();
        library.install(&mut model).unwrap();
        model.add_source("use.sysml", "attribute check = L::link::n;");
        let r = ResolvedModel::build(&model);
        assert!(
            r.unresolved_references().is_empty(),
            "{:?}",
            r.unresolved_references()
        );
    }
}
