//! Semantic names and failure reporting preserve identity and source provenance.
#![cfg(feature = "json")]
use sysmlv2_parser::{
    json::{ClosurePolicy, Derived, DerivedValue, ResolvedModel},
    model::Model,
};

#[test]
fn ambiguous_references_are_included_in_unresolved_reporting() {
    let text = "package A { package B { part x; } package C { part x :> B::x; } }
                package D { public import A::**; part y :> x; part z :> missing; }";
    let mut m = Model::new();
    assert!(m.add_source("ambiguous.sysml", text).diagnostics.is_empty());
    let mut r = ResolvedModel::build(&m);
    assert_eq!(r.unresolved_count(), 2);
    let references = r.unresolved_references();
    assert_eq!(references.len(), 2);
    for (name, spelling) in [("D::y", "x"), ("D::z", "missing")] {
        let feature = r.resolve_qualified(name).unwrap();
        let rel = r
            .owned_relationships(feature)
            .into_iter()
            .find(|&e| r.element_type(e) == "Subsetting")
            .unwrap();
        let site = references.iter().find(|site| site.owner == rel).unwrap();
        assert_eq!(site.spelling, spelling);
        assert_eq!(site.unit, 0);
        assert_eq!(
            &text[site.span.start as usize..site.span.end as usize],
            spelling
        );
        assert_eq!(
            r.element_properties(rel)["subsettedFeature"]["@ref"],
            spelling
        );
    }
}

#[test]
fn anonymous_subject_takes_the_redefined_subjects_names() {
    let text = "part def Vehicle;
        requirement def Spec { subject <v> vehicle : Vehicle; }
        requirement req : Spec;
        part unit { satisfy req by unit; }";
    let mut m = Model::new();
    assert!(m.add_source("subject.sysml", text).diagnostics.is_empty());
    let mut r = ResolvedModel::build(&m);
    let memberships: Vec<_> = r
        .user_elements()
        .filter(|&e| r.element_type(e) == "SubjectMembership")
        .collect();
    let subject = memberships
        .into_iter()
        .find_map(|m| {
            let Derived::Value(DerivedValue::Element(f)) = r.derived(m, "ownedSubjectParameter")
            else {
                return None;
            };
            r.element_name(f).is_none().then_some(f)
        })
        .unwrap();
    // Reading before and after implied materialization must agree.
    for materialized in [false, true] {
        if materialized {
            r.set_closure_policy(ClosurePolicy::Closure {
                include_implied: true,
            });
        }
        assert_eq!(
            r.element_effective_name(subject).as_deref(),
            Some("vehicle")
        );
        assert_eq!(r.element_short_name(subject).as_deref(), Some("v"));
        assert_eq!(
            r.derived(subject, "name"),
            Derived::Value(DerivedValue::Str("vehicle".into()))
        );
    }
}

#[test]
fn unnamed_satisfy_locators_do_not_collide_in_recursive_imports() {
    let mut m = Model::new();
    assert!(
        m.add_source(
            "names.sysml",
            "package P {
        requirement def Spec;
        package Q {
            package Requirements { requirement spec : Spec; }
            package Parts { part v { satisfy Requirements::spec by v { part child; } } }
        }
        package U { public import Q::**; requirement r :> spec; }
        alias satisfaction for Q::Parts::v::spec;
    }"
        )
        .diagnostics
        .is_empty()
    );
    let mut r = ResolvedModel::build(&m);
    let satisfy = r.resolve_qualified("P::Q::Parts::v::spec").unwrap();
    assert_eq!(r.element_type(satisfy), "SatisfyRequirementUsage");
    assert!(r.element_effective_name(satisfy).is_none());
    assert!(
        r.resolve_semantic_qualified("P::Q::Parts::v::spec")
            .is_none()
    );
    assert!(
        r.resolve_semantic_qualified("P::Q::Parts::v::spec::child")
            .is_none()
    );
    assert_eq!(
        r.resolve_semantic_qualified("P::satisfaction"),
        Some(satisfy)
    );
    let actual = r.resolve_qualified("P::Q::Requirements::spec").unwrap();
    assert_eq!(r.resolve_semantic_qualified("P::U::spec"), Some(actual));
    let feature = r.resolve_qualified("P::U::r").unwrap();
    let rel = r
        .owned_relationships(feature)
        .into_iter()
        .find(|&e| r.element_type(e) == "Subsetting")
        .unwrap();
    assert_eq!(
        r.element_properties(rel)["subsettedFeature"]["@id"],
        r.element_id(actual).to_string()
    );
    assert!(r.unresolved_references().is_empty());
}

#[test]
fn semantic_lookup_checks_short_names_aliases_and_unresolved_redefinitions() {
    let mut m = Model::new();
    assert!(
        m.add_source(
            "qualified.kerml",
            "package <p> P {
        feature <s> named; alias <a> other for named;
        package Q { feature redefines missing; }
    }"
        )
        .diagnostics
        .is_empty()
    );
    let mut r = ResolvedModel::build(&m);
    let named = r.resolve_qualified("P::named").unwrap();
    for name in ["P::named", "p::s", "P::other", "p::a"] {
        assert_eq!(r.resolve_semantic_qualified(name), Some(named), "{name}");
    }
    assert!(r.resolve_qualified("P::Q::missing").is_some());
    assert!(r.resolve_semantic_qualified("P::Q::missing").is_none());
}

#[test]
fn subject_names_agree_with_library_backed_redefinition_and_export() {
    let mut m = Model::new();
    m.load_library_dir(&sysmlv2_testkit::library_dir()).unwrap();
    assert!(
        m.add_source(
            "subject.sysml",
            "part def Vehicle;
        requirement def Spec { subject <v> vehicle : Vehicle; }
        requirement req : Spec; part unit { satisfy req by unit; }"
        )
        .diagnostics
        .is_empty()
    );
    let mut r = ResolvedModel::build(&m);
    r.set_closure_policy(ClosurePolicy::Closure {
        include_implied: true,
    });
    let memberships: Vec<_> = r
        .user_elements()
        .filter(|&e| r.element_type(e) == "SubjectMembership")
        .collect();
    let subject = memberships
        .into_iter()
        .find_map(|m| {
            let Derived::Value(DerivedValue::Element(f)) = r.derived(m, "ownedSubjectParameter")
            else {
                return None;
            };
            r.element_name(f).is_none().then_some(f)
        })
        .unwrap();
    let target = r.resolve_qualified("Spec::vehicle").unwrap();
    let Derived::Value(DerivedValue::Elements(redefinitions)) =
        r.derived(subject, "ownedRedefinition")
    else {
        panic!()
    };
    assert_eq!(redefinitions.len(), 1);
    assert_eq!(
        r.property(redefinitions[0], "redefinedFeature").unwrap()["@id"],
        r.element_id(target).to_string()
    );
    assert_eq!(
        r.element_effective_name(subject),
        r.element_effective_name(target)
    );
    assert_eq!(r.element_short_name(subject), r.element_short_name(target));
    let full = sysmlv2_parser::full::model_to_full_json(&m);
    let row = full
        .as_array()
        .unwrap()
        .iter()
        .find(|row| row["@id"] == r.element_id(subject).to_string())
        .unwrap();
    assert_eq!(row["name"], "vehicle");
    assert_eq!(row["shortName"], "v");
}

#[test]
fn multiple_replay_locators_do_not_hide_inherited_or_imported_names() {
    let mut m = Model::new();
    assert!(
        m.add_source(
            "multiple.sysml",
            "package P {
        requirement def Spec;
        package R { requirement spec : Spec; }
        part def Base { requirement spec : Spec; }
        package Q { part v : Base { satisfy R::spec by v; satisfy R::spec by v; } }
        package U { public import Q::**; requirement r :> spec; }
    }"
        )
        .diagnostics
        .is_empty()
    );
    let mut r = ResolvedModel::build(&m);
    let inherited = r.resolve_qualified("P::Base::spec").unwrap();
    assert_eq!(r.resolve_semantic_qualified("P::U::spec"), Some(inherited));
    assert_eq!(
        r.resolve_semantic_qualified("P::Q::v::spec"),
        Some(inherited)
    );
    assert!(r.unresolved_references().is_empty());
    // Direct compatibility lookup retains its original ambiguity rather than
    // reusing a semantic import query's cached inherited candidate.
    assert!(r.resolve_qualified("P::Q::v::spec").is_none());
}

#[test]
fn recursive_imports_keep_alias_names_and_declared_shadowing() {
    let mut m = Model::new();
    assert!(
        m.add_source(
            "aliases.sysml",
            "package P {
        requirement def Spec; requirement req : Spec;
        part def Base { requirement spec : Spec; }
        package Q {
            part v : Base { requirement spec : Spec; satisfy req by v; }
            alias satisfaction for v::req;
        }
        package U { public import Q::**; requirement r :> spec; }
    }"
        )
        .diagnostics
        .is_empty()
    );
    let mut r = ResolvedModel::build(&m);
    let declared = r.resolve_qualified("P::Q::v::spec").unwrap();
    let anonymous = r.resolve_qualified("P::Q::v::req").unwrap();
    assert_eq!(r.resolve_semantic_qualified("P::U::spec"), Some(declared));
    assert_eq!(
        r.resolve_semantic_qualified("P::U::satisfaction"),
        Some(anonymous)
    );
    assert!(r.resolve_semantic_qualified("P::U::req").is_none());
    assert!(r.unresolved_references().is_empty());
}
