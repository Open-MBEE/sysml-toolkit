//! Projection gates: the usage-oriented and the
//! definition-oriented spelling of the same structure project
//! identically (the extract/inline identity, seen through the
//! authoritative structural gate), every structural mutation is
//! detected, and qualified names ride the correspondence mapping.

use sysmlv2_transform::{ElementRef, Session};

fn session(src: &str) -> Session {
    Session::from_sources(vec![("m.sysml".into(), src.into())]).expect("parses")
}

fn elem(s: &mut Session, qn: &str) -> ElementRef {
    s.resolved()
        .resolve_qualified(qn)
        .unwrap_or_else(|| panic!("`{qn}` resolves"))
}

fn project(src: &str, qn: &str) -> Vec<String> {
    let mut s = session(src);
    let e = elem(&mut s, qn);
    s.effective_member_projection(e, &|q| q.to_string())
}

/// The usage-oriented spelling…
const USAGE_ORIENTED: &str = "package P {
    attribute def Deg;
    part def A;
    part engine : A {
        attribute mass : Deg = 100;
        private attribute margin = mass * 2;
        part turbo [2] {
            attribute boost = 2;
        }
    }
}";

/// …and the definition-oriented spelling extract would produce.
const DEF_ORIENTED: &str = "package P {
    attribute def Deg;
    part def A;
    part def Engine :> A {
        attribute mass : Deg = 100;
        private attribute margin = mass * 2;
        part turbo [2] {
            attribute boost = 2;
        }
    }
    part engine : Engine;
}";

/// The extract correspondence: members move home from the usage to the
/// prospective definition — descendants map by prefix, the usage itself
/// stays. This is exactly the mapping the extract commit hands in.
fn extract_map(qn: &str) -> String {
    match qn.strip_prefix("P::engine::") {
        Some(rest) => format!("P::Engine::{rest}"),
        None => qn.to_string(),
    }
}

#[test]
fn both_modeling_styles_project_identically_under_the_correspondence() {
    let mut s = session(USAGE_ORIENTED);
    let e = elem(&mut s, "P::engine");
    let owned = s.effective_member_projection(e, &|qn| extract_map(qn));
    let inherited = project(DEF_ORIENTED, "P::engine");
    assert!(!owned.is_empty());
    assert_eq!(owned, inherited, "owned vs inherited must be invisible");
}

#[test]
fn rows_carry_the_structural_facts() {
    let rows = project(USAGE_ORIENTED, "P::engine");
    let mass = rows
        .iter()
        .find(|r| r.starts_with("mass "))
        .expect("mass row");
    assert!(mass.contains("<AttributeUsage>"), "{mass}");
    assert!(mass.contains("[P::Deg]"), "{mass}");
    assert!(mass.contains("= 100"), "{mass}");
    let margin = rows
        .iter()
        .find(|r| r.starts_with("margin "))
        .expect("margin row");
    assert!(margin.contains("vis=private"), "{margin}");
    assert!(margin.contains("refs=["), "{margin}");
    assert!(
        margin.contains("mass"),
        "value reference targets are recorded: {margin}"
    );
    let turbo = rows
        .iter()
        .find(|r| r.starts_with("turbo "))
        .expect("turbo row");
    assert!(turbo.contains("mult=2..2"), "{turbo}");
    assert!(
        rows.iter().any(|r| r.starts_with("turbo::boost ")),
        "nested members project recursively: {rows:?}"
    );
}

#[test]
fn every_structural_mutation_is_detected() {
    let base = project(DEF_ORIENTED, "P::engine");
    for (label, mutated) in [
        ("value", DEF_ORIENTED.replace("= 100", "= 101")),
        (
            "multiplicity",
            DEF_ORIENTED.replace("turbo [2]", "turbo [3]"),
        ),
        (
            "visibility",
            DEF_ORIENTED.replace("private attribute margin", "attribute margin"),
        ),
        ("typing", DEF_ORIENTED.replace("mass : Deg", "mass")),
        (
            "extra member",
            DEF_ORIENTED.replace(
                "part engine : Engine;",
                "part engine : Engine { attribute extra; }",
            ),
        ),
        (
            "nested value",
            DEF_ORIENTED.replace("boost = 2", "boost = 3"),
        ),
        (
            "member metaclass",
            DEF_ORIENTED.replace("attribute mass : Deg = 100;", "item mass : Deg = 100;"),
        ),
    ] {
        assert_ne!(
            base,
            project(&mutated, "P::engine"),
            "{label} mutation must change the projection"
        );
    }
}

#[test]
fn qualified_names_ride_the_correspondence_mapping() {
    // The same structure, with the attribute definition renamed — the
    // commit-time comparison maps old names forward and sees identity.
    let renamed = DEF_ORIENTED.replace("Deg", "Degrees");
    let mut s = session(USAGE_ORIENTED);
    let e = elem(&mut s, "P::engine");
    let mapped = s.effective_member_projection(e, &|qn| {
        let qn = extract_map(qn);
        if qn == "P::Deg" {
            "P::Degrees".to_string()
        } else if let Some(rest) = qn.strip_prefix("P::Deg::") {
            format!("P::Degrees::{rest}")
        } else {
            qn
        }
    });
    assert_eq!(mapped, project(&renamed, "P::engine"));
}

#[test]
fn shadowing_projects_the_nearest_member_once() {
    // A redefinition in the usage body shadows the inherited row: the
    // effective `mass` is the usage's, projected exactly once.
    let src = "package P {
    part def Engine {
        attribute mass = 100;
    }
    part engine : Engine {
        attribute mass = 200;
    }
}";
    let rows = project(src, "P::engine");
    let mass_rows: Vec<_> = rows.iter().filter(|r| r.starts_with("mass ")).collect();
    assert_eq!(mass_rows.len(), 1, "{rows:?}");
    assert!(mass_rows[0].contains("= 200"), "{mass_rows:?}");
}

#[test]
fn anonymous_members_survive_the_owned_to_inherited_move() {
    let usage_oriented = "package P {
    part def A { attribute mass; }
    part engine : A {
        doc /* calibration note */
        attribute :>> mass = 5;
    }
}";
    let definition_oriented = "package P {
    part def A { attribute mass; }
    part def Engine :> A {
        doc /* calibration note */
        attribute :>> mass = 5;
    }
    part engine : Engine;
}";
    let mut s = session(usage_oriented);
    let engine = elem(&mut s, "P::engine");
    let owned = s.effective_member_projection(engine, &|qn| extract_map(qn));
    let inherited = project(definition_oriented, "P::engine");
    assert_eq!(
        owned, inherited,
        "anonymous inherited rows must be retained"
    );
    assert!(
        owned.iter().any(|row| row.contains('«')),
        "an anonymous row should be visible: {owned:?}"
    );
}

#[test]
fn specialization_relationship_kind_is_structural() {
    let subsets = "package P {
    part engine {
        attribute base;
        attribute x :> base;
    }
}";
    let redefines = subsets.replace("x :> base", "x :>> base");
    assert_ne!(
        project(subsets, "P::engine"),
        project(&redefines, "P::engine"),
        "subsetting and redefinition must not collapse to one target list"
    );
}

#[test]
fn projection_has_no_arbitrary_nesting_cutoff() {
    let one = "package P {
    part root {
        part n1 { part n2 { part n3 { part n4 { part n5 { part n6 {
            attribute leaf = 1;
        } } } } } }
    }
}";
    let two = one.replace("leaf = 1", "leaf = 2");
    let rows = project(one, "P::root");
    assert!(
        rows.iter().any(|row| row.contains("n6::leaf")),
        "deepest row must be projected: {rows:?}"
    );
    assert_ne!(rows, project(&two, "P::root"));
}
