//! Default multiplicities as owned members: a usage without a written one
//! (SysML 7.6.3: an end feature, or an attribute, item or port usage its
//! owning type features, with no written multiplicity, subsetting or
//! redefinition) and an `individual` definition own an OwningMembership →
//! bound-less `Multiplicity`, appended last, whose implied Subsetting names
//! `Base::exactlyOne` (`Base::zeroOrOne` for the individual definition);
//! `multiplicity` answers it, the evaluator reads it, the lift drops it.

#![cfg(feature = "json")]

use sysmlv2_parser::json::{
    ClosurePolicy, Derived, DerivedValue, ElementRef, Reference, ResolvedModel, to_compact_json,
};
use sysmlv2_parser::lift::from_compact_json;
use sysmlv2_parser::model::Model;
use sysmlv2_parser::parser::parse_source;
use sysmlv2_parser::print::print_source;

/// The issue's model: every kind of usage the rule selects or passes over.
const ISSUE_73: &str = "package M {
    part def P;
    port def Q;
    connection def K { end part e1 : P; end part e2 : P; }
    part x : P[0..3];
    part def C {
        attribute n;
        item i : P;
        part v : P;
        port q : Q;
        ref r : P;
        part u :> x;
        part w : P[2];
    }
    part c : C {
        part c2 : P;
    }
}";

/// The issue's model: individual definitions beside a plain one.
const ISSUE_72: &str = "package M {
    individual part def Apollo;
    individual occurrence def Ind;
    individual def Plain;
    part def P;
}";

fn resolved(src: &str) -> ResolvedModel {
    let mut model = Model::new();
    model
        .load_library_dir(&sysmlv2_testkit::library_dir())
        .unwrap();
    model.add_source("m.sysml", src);
    assert!(!model.has_errors());
    let mut r = ResolvedModel::build(&model);
    r.set_closure_policy(ClosurePolicy::Closure {
        include_implied: true,
    });
    r
}

fn element(r: &mut ResolvedModel, qn: &str) -> ElementRef {
    r.resolve_qualified(qn)
        .unwrap_or_else(|| panic!("{qn} resolves"))
}

/// The `Multiplicity` members `e` owns (a range is one too).
fn owned_multiplicities(r: &ResolvedModel, e: ElementRef) -> Vec<ElementRef> {
    r.owned_members(e)
        .into_iter()
        .filter(|&m| {
            r.element_type(m) == "Multiplicity" || r.element_type(m) == "MultiplicityRange"
        })
        .collect()
}

/// The one bound-less default `e` owns: last among its owned members,
/// under a stored (not implied) OwningMembership, and what `multiplicity` answers.
fn the_default(r: &mut ResolvedModel, qn: &str) -> ElementRef {
    let e = element(r, qn);
    let owned = owned_multiplicities(r, e);
    assert_eq!(owned.len(), 1, "{qn} owns one multiplicity");
    let m = owned[0];
    assert_eq!(r.element_type(m), "Multiplicity", "{qn}: bound-less");
    assert_eq!(r.owned_members(e).last(), Some(&m), "{qn}: the last member");
    let membership = r.owned_relationships(e).into_iter().last().unwrap();
    assert_eq!(r.element_type(membership), "OwningMembership");
    assert_eq!(
        r.element_properties(membership).get("isImplied"),
        Some(&serde_json::json!(false)),
        "{qn}: a stored member, not an implied relationship"
    );
    assert_eq!(
        r.element_properties(m).get("declaredName"),
        None,
        "{qn}: unnamed"
    );
    assert_eq!(
        derived_multiplicity(r, e),
        Some(m),
        "{qn}: `multiplicity` answers it"
    );
    m
}

fn derived_multiplicity(r: &mut ResolvedModel, e: ElementRef) -> Option<ElementRef> {
    match r.derived(e, "multiplicity") {
        Derived::Value(DerivedValue::Element(m))
        | Derived::Value(DerivedValue::Reference(Reference::Element(m))) => Some(m),
        Derived::Value(DerivedValue::Null) => None,
        other => panic!("multiplicity: {other:?}"),
    }
}

/// The qualified names of the targets of `e`'s implied Subsettings.
fn implied_subsetting_targets(r: &mut ResolvedModel, e: ElementRef) -> Vec<String> {
    let mut targets = Vec::new();
    for rel in r.implied_relationships(e) {
        if r.element_type(rel) != "Subsetting" {
            continue;
        }
        let target = r
            .element_properties(rel)
            .get("subsettedFeature")
            .and_then(|v| v.get("@id"))
            .and_then(|v| v.as_str())
            .and_then(|id| r.element_by_id(id))
            .expect("an implied Subsetting names a loaded target");
        targets.push(r.element_qualified_name(target).unwrap());
    }
    targets.sort();
    targets
}

/// `emit(parse(print(lift(emit(parse(x)))))) == emit(parse(x))`, and the
/// lifted text.
fn round_trip(src: &str) -> String {
    let parsed = parse_source(src);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let json = to_compact_json(&parsed.unit);
    let lifted = from_compact_json(&json).expect("lifts");
    assert!(lifted.errors.is_empty(), "{:?}", lifted.errors);
    let text = print_source(&lifted.unit);
    let reparsed = parse_source(&text);
    assert!(
        reparsed.diagnostics.is_empty(),
        "{text}\n{:?}",
        reparsed.diagnostics
    );
    assert_eq!(to_compact_json(&reparsed.unit), json, "{text}");
    text
}

#[test]
fn structural_usages_a_type_features_take_the_default() {
    let mut r = resolved(ISSUE_73);
    for qn in ["M::C::n", "M::C::i", "M::C::v", "M::C::q", "M::c::c2"] {
        let m = the_default(&mut r, qn);
        let targets = implied_subsetting_targets(&mut r, m);
        assert_eq!(targets, ["Base::exactlyOne"], "{qn}: {targets:?}");
    }
}

#[test]
fn reference_ranged_subsetting_and_unfeatured_usages_take_none() {
    let mut r = resolved(ISSUE_73);
    // A reference usage, a written subsetting (7.6.3's third condition).
    for qn in ["M::C::r", "M::C::u"] {
        let e = element(&mut r, qn);
        assert!(owned_multiplicities(&r, e).is_empty(), "{qn}");
        assert_eq!(derived_multiplicity(&mut r, e), None, "{qn}");
    }
    // A written range is the one multiplicity.
    for qn in ["M::C::w", "M::x"] {
        let e = element(&mut r, qn);
        let owned = owned_multiplicities(&r, e);
        assert_eq!(owned.len(), 1, "{qn}");
        assert_eq!(r.element_type(owned[0]), "MultiplicityRange", "{qn}");
        assert_eq!(derived_multiplicity(&mut r, e), Some(owned[0]), "{qn}");
    }
    // A usage a namespace owns, a variant and an enumeration literal have
    // no owning type; a written redefinition and a reference are the
    // third condition too.
    let mut r = resolved(
        "package N {
            part def P;
            part top : P;
            part def Box { part lid : P; }
            variation part def Kind :> Box { variant part small : Kind; }
            enum def Color { red; green; }
            part def Sub :> Box { part :>> lid; part again ::> top; }
        }",
    );
    for qn in [
        "N::top",
        "N::Kind::small",
        "N::Color::red",
        "N::Sub::lid",
        "N::Sub::again",
    ] {
        let e = element(&mut r, qn);
        assert!(owned_multiplicities(&r, e).is_empty(), "{qn}");
    }
    the_default(&mut r, "N::Box::lid");
}

#[test]
fn end_features_take_the_default() {
    let mut r = resolved(ISSUE_73);
    for qn in ["M::K::e1", "M::K::e2"] {
        let m = the_default(&mut r, qn);
        let targets = implied_subsetting_targets(&mut r, m);
        assert_eq!(targets, ["Base::exactlyOne"], "{qn}: {targets:?}");
    }
    // A connector part's ends, a written end multiplicity kept.
    let mut r = resolved(
        "package N {
            part def P { port p; }
            part a : P; part b : P;
            connection c1 connect a to b;
            connection c2 connect [1] a to [0..2] b;
            interface i connect a.p to b.p;
        }",
    );
    let ends: Vec<ElementRef> = r
        .elements_of_metaclass("ReferenceUsage")
        .into_iter()
        .chain(r.elements_of_metaclass("PortUsage"))
        .filter(|&e| {
            !r.is_library_element(e)
                && r.element_properties(e).get("isEnd") == Some(&serde_json::json!(true))
        })
        .collect();
    assert_eq!(ends.len(), 6, "three binary connectors");
    let mut defaults = 0;
    for end in ends {
        let owned = owned_multiplicities(&r, end);
        assert_eq!(owned.len(), 1);
        if r.element_type(owned[0]) == "Multiplicity" {
            defaults += 1;
            assert_eq!(r.owned_members(end).last(), Some(&owned[0]));
            let targets = implied_subsetting_targets(&mut r, owned[0]);
            assert_eq!(targets, ["Base::exactlyOne"], "{targets:?}");
        }
    }
    assert_eq!(defaults, 4, "c2's written ranges stay");
}

#[test]
fn the_evaluator_reads_the_default() {
    let mut r = resolved(ISSUE_73);
    for qn in ["M::C::v", "M::C::n", "M::K::e1"] {
        let e = element(&mut r, qn);
        assert_eq!(r.effective_cardinality(e), Some((1, Some(1))), "{qn}");
        let report = r.cardinality_report(e);
        assert_eq!(
            report.bounds.map(|b| b.size()),
            Ok(Some(1)),
            "{qn}: {:?}",
            report.bounds
        );
    }
    let w = element(&mut r, "M::C::w");
    assert_eq!(r.effective_cardinality(w), Some((2, Some(2))));
}

#[test]
fn the_lift_drops_the_default_and_keeps_a_written_range() {
    let text = round_trip(ISSUE_73);
    assert!(!text.contains("multiplicity"), "{text}");
    assert!(text.contains("[2]") && text.contains("[0..3]"), "{text}");
    // A bound-less `multiplicity;` member has no SysML spelling (the
    // parser reads it as a reference usage of that name); a payload's
    // default under a usage the rule selects is dropped and written
    // again, one under any other owner is kept (`lift` unit tests).
    let src = "package W { part def P; part def A { attribute a { multiplicity; } } }";
    let mut r = resolved(src);
    let named = element(&mut r, "W::A::a::multiplicity");
    assert_eq!(r.element_type(named), "ReferenceUsage");
    the_default(&mut r, "W::A::a");
}

#[test]
fn an_individual_definition_owns_a_multiplicity() {
    let mut r = resolved(ISSUE_72);
    for qn in ["M::Apollo", "M::Ind", "M::Plain"] {
        let e = element(&mut r, qn);
        assert_eq!(
            r.element_properties(e).get("isIndividual"),
            Some(&serde_json::json!(true)),
            "{qn}"
        );
        let m = the_default(&mut r, qn);
        let targets = implied_subsetting_targets(&mut r, m);
        assert_eq!(targets, ["Base::zeroOrOne"], "{qn}: {targets:?}");
        // At most one individual: the default's own domain.
        assert_eq!(r.effective_cardinality(e), Some((0, Some(1))), "{qn}");
    }
    let p = element(&mut r, "M::P");
    assert!(owned_multiplicities(&r, p).is_empty());
    assert_eq!(derived_multiplicity(&mut r, p), None);
    let text = round_trip(ISSUE_72);
    assert!(!text.contains("multiplicity"), "{text}");
}
