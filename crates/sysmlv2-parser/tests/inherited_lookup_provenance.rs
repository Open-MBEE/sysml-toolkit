#![cfg(feature = "json")]
use sysmlv2_parser::{json::ResolvedModel, model::Model};

#[test]
fn suppressed_public_aliases_are_not_reported_as_visibility_blocked() {
    let mut m = Model::new();
    m.add_source(
        "aliases.kerml",
        "class Base { private feature x; alias ax for x; alias bx for x; }
        class Mid specializes Base; class Child specializes Mid; feature useX references Child::ax;",
    );
    assert!(!m.has_errors());
    let mut r = ResolvedModel::build(&m);
    assert!(r.resolve_qualified("Child::ax").is_none());
    assert_eq!(r.unresolved_count(), 1);
    assert!(
        r.blocked_references().is_empty(),
        "semantic removal is not a visibility failure"
    );
}

#[test]
fn header_qualifiers_keep_the_selected_base_context() {
    for (source, qualifier) in [
        (
            "class A { feature x; } class Child specializes A { feature y redefines A::x; }",
            "A",
        ),
        (
            "class A { class Nested { feature x; } } class Child specializes A { feature y redefines Nested::x; }",
            "A::Nested",
        ),
    ] {
        let mut m = Model::new();
        m.add_source("qualified.kerml", source);
        assert!(!m.has_errors());
        let mut r = ResolvedModel::build(&m);
        assert_eq!(r.unresolved_count(), 0);
        let target = r.resolve_qualified(qualifier).unwrap();
        assert!(
            r.reference_sites()
                .iter()
                .any(|site| site.kind == "qualifier" && site.target == target),
            "missing qualifier {qualifier}"
        );
    }
}
