use sysmlv2_transform::Session;

#[test]
fn rename_rewrites_explicit_and_relative_header_qualifiers() {
    for (source, target, expected) in [
        (
            "class A { feature x; } class Child specializes A { feature y redefines A::x; }",
            "A",
            "redefines Renamed::x",
        ),
        (
            "class A { class Nested { feature x; } } class Child specializes A { feature y redefines Nested::x; }",
            "A::Nested",
            "redefines Renamed::x",
        ),
    ] {
        let mut s = Session::from_sources(vec![("qualified.kerml".into(), source.into())]).unwrap();
        let target = s.resolved().resolve_qualified(target).unwrap();
        let mut edit = s.edit();
        edit.rename(target, "Renamed");
        edit.commit()
            .expect("qualifier rename preserves header identity");
        assert!(s.units().next().unwrap().2.contains(expected));
        assert_eq!(s.resolved().unresolved_count(), 0);
    }
}

#[test]
fn rename_preserves_imported_base_and_redefinition_target_identity() {
    for import in ["private import Lib::*;", "private import Lib::Base;"] {
        let source = format!(
            "package Lib {{ class Base {{ feature x; }} }}
            package P {{ {import}
                class Child specializes Base {{ feature x; feature y redefines x; }}
            }}"
        );
        let mut session = Session::from_sources(vec![("imported.kerml".into(), source)]).unwrap();
        let base = session.resolved().resolve_qualified("Lib::Base").unwrap();
        let mut edit = session.edit();
        edit.rename(base, "Renamed");
        edit.commit()
            .expect("rename preserves imported base binding");
        let slot = session
            .resolved()
            .resolve_qualified("Lib::Renamed::x")
            .unwrap();
        let mut edit = session.edit();
        edit.rename(slot, "inheritedSlot");
        edit.commit()
            .expect("rename preserves inherited header target");
        let source = session.units().next().unwrap().2;
        assert!(source.contains("specializes Renamed"));
        assert!(
            source.contains("feature x;"),
            "the local shadow keeps its name"
        );
        assert!(source.contains("redefines inheritedSlot"));
        let r = session.resolved();
        assert_eq!(r.unresolved_count(), 0);
        let expected = r.resolve_qualified("Lib::Renamed::inheritedSlot").unwrap();
        let y = r.resolve_qualified("P::Child::y").unwrap();
        let relation = r
            .owned_relationships(y)
            .into_iter()
            .find(|&e| r.element_type(e) == "Redefinition")
            .unwrap();
        assert_eq!(
            r.element_properties(relation)["redefinedFeature"]["@id"],
            r.element_id(expected).to_string()
        );
    }
}
