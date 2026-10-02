//! Bound references retain valuation identity across interchange spellings.
use sysmlv2_transform::Session;

fn check(session: &mut Session) {
    for _ in 0..2 {
        for owner in ["Child", "Renamed"] {
            for member in [
                "header",
                "body",
                "qualified",
                "global",
                "aliased",
                "named",
                "localHeader",
                "localBody",
            ] {
                let name = format!("P::{owner}::{member}");
                let r = session.resolved();
                let e = r.resolve_qualified(&name).unwrap();
                assert_eq!(r.effective_cardinality(e), Some((6, Some(6))), "{name}");
            }
        }
    }
}

#[test]
fn bound_valuation_identity_survives_compact_and_full_interchange() {
    let source = "package P { class Base { feature n default = 4;
        alias alternate for n;
        feature header[n]; feature body { multiplicity [n]; }
        feature qualified { multiplicity [Base::n]; }
        feature global { multiplicity [$::P::Base::n]; }
        feature aliased { multiplicity [alternate]; }
        multiplicity dynamic[n]; feature named { multiplicity subsets dynamic; }
    }
    class Child specializes Base { feature redefines n = 6;
        feature localHeader[Base::n]; feature localBody { multiplicity [Base::n]; }
        feature redefines header; feature redefines body; feature redefines qualified;
        feature redefines global; feature redefines aliased; feature redefines named;
    }
    class Renamed specializes Base { feature other redefines n = 6;
        feature localHeader[Base::n]; feature localBody { multiplicity [Base::n]; }
        feature redefines header; feature redefines body; feature redefines qualified;
        feature redefines global; feature redefines aliased; feature redefines named;
    } }";
    let mut original = Session::from_sources(vec![("p.kerml".into(), source.into())]).unwrap();
    check(&mut original);
    for json in [
        original.to_compact_json(),
        original.to_full_json_with(false),
    ] {
        let mut loaded =
            Session::from_interchange_json_named(&json, None, &["p.kerml".into()]).unwrap();
        check(&mut loaded);
    }
}

#[test]
fn bound_formula_dependencies_survive_compact_and_full_interchange() {
    let source = "package P { feature external = 2;
        class Base { feature n default = 3; alias alternate for n;
            feature formula = alternate + external;
            feature second = $::P::Base::formula * 2;
            feature header[second]; feature directCount = n + 1; feature direct[directCount];
            feature body { multiplicity [second]; }
            multiplicity dynamic[second]; feature named { multiplicity subsets dynamic; }
        }
        class Child specializes Base { feature other redefines n = 6;
            feature external = 100;
            feature redefines header; feature redefines direct;
            feature redefines body; feature redefines named;
        }
    }";
    fn check(session: &mut Session) {
        for _ in 0..2 {
            for (owner, value) in [("Child", 16), ("Base", 10)] {
                for member in ["header", "body", "named"] {
                    let name = format!("P::{owner}::{member}");
                    let r = session.resolved();
                    let e = r.resolve_qualified(&name).unwrap();
                    assert_eq!(
                        r.effective_cardinality(e),
                        Some((value, Some(value))),
                        "{name}"
                    );
                }
            }
            let r = session.resolved();
            let direct = r.resolve_qualified("P::Child::direct").unwrap();
            assert_eq!(r.effective_cardinality(direct), Some((7, Some(7))));
        }
    }
    let mut original =
        Session::from_sources(vec![("formulas.kerml".into(), source.into())]).unwrap();
    check(&mut original);
    for json in [
        original.to_compact_json(),
        original.to_full_json_with(false),
    ] {
        let mut loaded =
            Session::from_interchange_json_named(&json, None, &["formulas.kerml".into()]).unwrap();
        check(&mut loaded);
    }
}

#[test]
fn provider_proofs_preserve_header_body_and_interchange_reference_identity() {
    let source = "package Good { feature n = 4; }
        package P { public import Good::*; public import absent::*;
            feature header[n]; feature body { multiplicity [n]; }
        }
        class Base { public import Good::*; feature n default = 3;
            feature header[n]; feature body { multiplicity [n]; }
        }
        class Child specializes Base { feature other redefines n = 6;
            feature redefines header; feature redefines body;
        }
        class Bad specializes Base { public import absent::*;
            feature redefines header; feature redefines body;
        }";
    fn check(session: &mut Session) {
        for _ in 0..2 {
            for (owner, expected) in [
                ("P", Some((4, Some(4)))),
                ("Child", Some((6, Some(6)))),
                ("Bad", None),
            ] {
                for member in ["header", "body"] {
                    let name = format!("{owner}::{member}");
                    let r = session.resolved();
                    let e = r.resolve_qualified(&name).unwrap();
                    assert_eq!(r.effective_cardinality(e), expected, "{name}");
                }
            }
        }
    }
    let mut original =
        Session::from_sources(vec![("providers.kerml".into(), source.into())]).unwrap();
    check(&mut original);
    for json in [
        original.to_compact_json(),
        original.to_full_json_with(false),
    ] {
        let mut loaded =
            Session::from_interchange_json_named(&json, None, &["providers.kerml".into()]).unwrap();
        check(&mut loaded);
    }
}
