#![cfg(feature = "json")]

use std::sync::Arc;
use sysmlv2_parser::{
    json::{ClosurePolicy, Derived, DerivedValue, ResolvedModel},
    model::Model,
    prepared::PreparedLibrary,
};

fn check(library: &str, source: &str, expected: Option<&str>, incomplete: bool) {
    let mut base = Model::new();
    base.add_library_source("aliases.kerml", library);
    let prepared = base.prepare_library().unwrap();
    let serialized =
        Arc::new(PreparedLibrary::from_bytes(&prepared.to_bytes(17).unwrap(), 17).unwrap());
    for mode in 0..3 {
        for warm in [false, true] {
            let mut model = Model::new();
            match mode {
                0 => {
                    model.add_library_source("aliases.kerml", library);
                }
                1 => {
                    Arc::clone(&prepared).install(&mut model).unwrap();
                }
                _ => {
                    Arc::clone(&serialized).install(&mut model).unwrap();
                }
            }
            model.add_source("user.kerml", source);
            assert!(!model.has_errors());
            let mut r = ResolvedModel::build(&model);
            let owner = r.resolve_qualified("U::Leaf").unwrap();
            let slot = r.resolve_qualified("U::Leaf::slot").unwrap();
            let expected = expected.map(|name| {
                let e = r.resolve_qualified(name).unwrap();
                r.element_id(e).to_string()
            });
            if warm {
                r.inherited_memberships(owner, true);
            }
            let targets: Vec<_> = r
                .implied_relationships(slot)
                .into_iter()
                .filter(|&edge| r.element_type(edge) == "Redefinition")
                .map(|edge| {
                    r.element_properties(edge)["redefinedFeature"]["@id"]
                        .as_str()
                        .unwrap()
                        .to_owned()
                })
                .collect();
            assert_eq!(
                targets,
                expected.iter().cloned().collect::<Vec<_>>(),
                "mode={mode}, warm={warm}"
            );
            assert_eq!(r.inheritance_incomplete(owner, true), incomplete);
            if !incomplete {
                r.set_closure_policy(ClosurePolicy::Closure {
                    include_implied: true,
                });
                let mid = r.resolve_qualified("P::Mid").unwrap();
                let Derived::Value(DerivedValue::Elements(ends)) = r.derived(mid, "endFeature")
                else {
                    panic!("endFeature must be an element collection");
                };
                let end_ids: Vec<_> = ends.iter().map(|&e| r.element_id(e).to_string()).collect();
                assert_eq!(
                    end_ids, targets,
                    "shared read and positional target disagree"
                );
            }
        }
    }
}

#[test]
fn owning_membership_and_alias_of_same_feature_remove_each_other_before_pairing() {
    check(
        "package P { assoc Base { end feature x; alias ax for x; } assoc Mid specializes Base; }",
        "package U { assoc Leaf specializes P::Mid { end feature slot; } }",
        None,
        false,
    );
}

#[test]
fn inherited_alias_redefinition_blocks_an_owning_membership() {
    check(
        "package P { assoc Values { end feature x; } assoc Redefiners specializes Values { end feature y redefines x; } assoc Base { public import Values::x; alias ay for Redefiners::y; } assoc Mid specializes Base; }",
        "package U { assoc Leaf specializes P::Mid { end feature slot; } }",
        None,
        false,
    );
}

#[test]
fn same_membership_reached_through_a_diamond_preserves_its_slot() {
    check(
        "package P { assoc Base { end feature x; } assoc Left specializes Base; assoc Right specializes Base; assoc Mid specializes Left, Right; }",
        "package U { assoc Leaf specializes P::Mid { end feature slot; } }",
        Some("P::Base::x"),
        false,
    );
}

#[test]
fn owned_alias_does_not_seed_owned_feature_redefinition_targets() {
    check(
        "package P { assoc Base { end feature x; } assoc Values specializes Base { end feature y redefines Base::x; } assoc Mid specializes Base { alias ay for Values::y; } }",
        "package U { assoc Leaf specializes P::Mid { end feature slot; } }",
        Some("P::Base::x"),
        false,
    );
}

#[test]
fn imported_aliases_participate_in_filtering_before_slot_projection() {
    for import in [
        "public import Values::*;",
        "public import Values::x; public import Values::ax;",
        "public import all Values::*;",
    ] {
        check(
            &format!(
                "package P {{ assoc Values {{ end feature x; alias ax for x; }} assoc Base {{ {import} }} assoc Mid specializes Base; }}"
            ),
            "package U { assoc Leaf specializes P::Mid { end feature slot; } }",
            None,
            false,
        );
    }
}

#[test]
fn private_aliases_do_not_block_but_protected_aliases_do() {
    for (visibility, expected) in [("private", Some("P::Base::x")), ("protected", None)] {
        check(
            &format!(
                "package P {{ assoc Base {{ end feature x; {visibility} alias ax for x; }} assoc Mid specializes Base; }}"
            ),
            "package U { assoc Leaf specializes P::Mid { end feature slot; } }",
            expected,
            false,
        );
    }
}

#[test]
fn unresolved_visible_alias_qualifies_the_plan_without_inventing_positions() {
    for (visibility, expected, incomplete) in [
        ("public", None, true),
        ("private", Some("P::Base::x"), false),
    ] {
        check(
            &format!(
                "package P {{ assoc Base {{ end feature x; {visibility} alias ax for Missing; }} assoc Mid specializes Base; }}"
            ),
            "package U { assoc Leaf specializes P::Mid { end feature slot; } }",
            expected,
            incomplete,
        );
    }
}

#[test]
fn mutual_redefinition_cycle_removes_both_memberships() {
    // Deliberately malformed semantic graph: prove both edges exist before
    // checking cycle robustness, rather than testing unresolved spellings.
    let library = "package P { assoc Root; assoc Base specializes Root { end feature x redefines Base::y; end feature y redefines Base::x; } assoc Mid specializes Base; }";
    let mut model = Model::new();
    model.add_library_source("aliases.kerml", library);
    let mut r = ResolvedModel::build(&model);
    let x = r.resolve_qualified("P::Base::x").unwrap();
    let y = r.resolve_qualified("P::Base::y").unwrap();
    for (source, target) in [(x, y), (y, x)] {
        let edge = r
            .owned_relationships(source)
            .into_iter()
            .find(|&edge| r.element_type(edge) == "Redefinition")
            .unwrap();
        assert_eq!(
            r.element_properties(edge)["redefinedFeature"]["@id"],
            r.element_id(target).to_string()
        );
    }
    check(
        library,
        "package U { assoc Leaf specializes P::Mid { end feature slot; } }",
        None,
        false,
    );
}
