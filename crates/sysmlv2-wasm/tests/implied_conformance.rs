use sysmlv2_wasm::Session;

#[test]
fn implied_conformance_is_additive_and_guards_both_arguments() {
    let users = r#"[{"name":"p.sysml","text":"package P { part def Box; }"}]"#;
    let library =
        r#"[{"name":"Parts.kerml","text":"standard library package Parts { class Part; }"}]"#;
    let mut session = Session::from_sources_with_library(users, None, None).unwrap();
    let stale = session.resolve("P::Box").unwrap();
    session.load_library_sources(library, None).unwrap();
    let source = session.resolve("P::Box").unwrap();
    let target = session.resolve("Parts::Part").unwrap();
    assert!(!session.conforms(&source, &target).unwrap());
    assert!(session.conforms_with_implied(&source, &target).unwrap());
    assert!(session.conforms_with_implied(&stale, &target).is_err());
    assert!(session.conforms_with_implied(&source, &stale).is_err());
}
