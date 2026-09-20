//! Adversarial battery for inherited-membership enumeration: corner
//! cases assembled from the KerML 8.3 OCL (`inheritableMemberships` /
//! `nonPrivateMemberships` / `removeRedefinedFeatures`), the pilot's
//! serializer scope cases, and the resolver's own composition rules.
//! Enumeration must mirror the resolver; where the resolver itself
//! deviates from the spec, the deviation is recorded, never patched
//! from here.

#![cfg(feature = "json")]

use sysmlv2_parser::json::ResolvedModel;
use sysmlv2_parser::model::Model;

fn build(src: &str) -> ResolvedModel {
    let mut model = Model::new();
    model.add_source("b.sysml", src);
    assert!(!model.has_errors(), "battery model must parse clean");
    ResolvedModel::build(&model)
}

fn inherited_names(r: &mut ResolvedModel, qn: &str) -> Vec<String> {
    let e = r.resolve_qualified(qn).unwrap();
    let mut names: Vec<String> = r
        .inherited_memberships(e, false)
        .iter()
        .filter_map(|&m| r.membership_member_name(m))
        .collect();
    names.sort();
    names
}

#[test]
fn protected_members_inherit_two_levels() {
    let mut r = build(
        "package P {
            part def Base { protected attribute guarded; attribute open; }
            part def Mid :> Base;
            part def Sub :> Mid;
         }",
    );
    assert_eq!(inherited_names(&mut r, "P::Sub"), ["guarded", "open"]);
}

#[test]
fn short_name_only_member_inherits_once() {
    let mut r = build(
        "package P {
            part def Base { attribute <sn> named; }
            part def Sub :> Base;
         }",
    );
    // Registered under both spellings; the membership appears once.
    let sub = r.resolve_qualified("P::Sub").unwrap();
    assert_eq!(r.inherited_memberships(sub, false).len(), 1);
}

#[test]
fn supertype_reached_through_import_contributes() {
    // Pilot serializer case: the supertype itself arrives via an import.
    let mut r = build(
        "package P {
            package Lib { part def Basis { attribute deep; } }
            package Use {
                private import Lib::*;
                part def Sub :> Basis;
            }
         }",
    );
    assert_eq!(inherited_names(&mut r, "P::Use::Sub"), ["deep"]);
}

#[test]
fn recursive_import_descends_members_only_through_owned() {
    let mut r = build(
        "package P {
            package Other { part def Alien { part deep; } }
            package Lib {
                public import Other::*;
                part def Outer { part inner; }
            }
            part def Base { public import Lib::*::**; }
            part def Sub :> Base;
         }",
    );
    let names = inherited_names(&mut r, "P::Sub");
    assert!(
        names.contains(&"Outer".to_string()) && names.contains(&"inner".to_string()),
        "::** brings nested members: {names:?}"
    );
    assert!(
        names.contains(&"Alien".to_string()),
        "the imported member is visible at Lib itself: {names:?}"
    );
    assert!(
        !names.contains(&"deep".to_string()),
        "recursion descends owned members only, not imported ones: {names:?}"
    );
}

#[test]
fn diamond_same_feature_is_one_membership() {
    let mut r = build(
        "package P {
            part def Root { attribute x; }
            part def L :> Root;
            part def R :> Root;
            part def D :> L, R;
         }",
    );
    assert_eq!(
        inherited_names(&mut r, "P::D"),
        ["x"],
        "one membership, not two"
    );
}

#[test]
fn specialization_cycle_terminates_without_self_members() {
    let mut r = build(
        "package P {
            part def A :> B { attribute a; }
            part def B :> A { attribute b; }
         }",
    );
    // The heritage is cyclic (the checker reports it; the walk must still
    // terminate): each type inherits the other's member once, never its
    // own.
    assert_eq!(inherited_names(&mut r, "P::A"), ["b"]);
    assert_eq!(inherited_names(&mut r, "P::B"), ["a"]);
}

#[test]
fn kerml_same_name_features_both_retained() {
    // No SysML implicit usage redefinition in the KerML dialect: an
    // owned same-named feature does not remove the inherited one.
    let mut model = Model::new();
    model.add_source(
        "k.kerml",
        "package P {
            class Base { feature f; }
            class Sub specializes Base { feature f; }
         }",
    );
    assert!(!model.has_errors());
    let mut r = ResolvedModel::build(&model);
    let sub = r.resolve_qualified("P::Sub").unwrap();
    let inherited: Vec<_> = r
        .inherited_features(sub, false)
        .iter()
        .filter_map(|&m| r.element_name(m).map(str::to_string))
        .collect();
    assert_eq!(
        inherited,
        ["f"],
        "KerML keeps the inherited f (ambiguous, not shadowed)"
    );
}

#[test]
fn direct_import_filter_applies_at_first_hop() {
    let mut r = build(
        "package P {
            metadata def Safety;
            package Lib {
                part safe { @Safety; }
                part plain;
            }
            part def Base { public import Lib::*[@Safety]; }
            part def Sub :> Base;
         }",
    );
    let names = inherited_names(&mut r, "P::Sub");
    assert!(names.contains(&"safe".to_string()), "{names:?}");
    assert!(!names.contains(&"plain".to_string()), "{names:?}");
}

#[test]
fn alias_with_short_name_only_inherits() {
    let mut r = build(
        "package P {
            part def Base { attribute mass; alias <m2> for mass; }
            part def Sub :> Base;
         }",
    );
    let sub = r.resolve_qualified("P::Sub").unwrap();
    let memberships = r.inherited_memberships(sub, false);
    assert!(
        memberships.iter().any(|&m| r.membership_is_alias(m)),
        "short-name-only alias must inherit"
    );
}

#[test]
fn unnamed_redefining_feature_removes_target_only() {
    let mut r = build(
        "package P {
            part def Base { attribute a; attribute b; }
            part def Sub :> Base { attribute :>> a; }
         }",
    );
    assert_eq!(
        inherited_names(&mut r, "P::Sub"),
        ["b"],
        "the unnamed :>> a redefines a; b unaffected"
    );
}

#[test]
fn protected_import_of_a_base_inherits_a_private_one_does_not() {
    let mut r = build(
        "package P {
            package Lib { part def Shared { attribute deep; } }
            part def Guarded { protected import Lib::*; }
            part def Hidden { private import Lib::*; }
            part def SubG :> Guarded;
            part def SubH :> Hidden;
         }",
    );
    // KerML nonPrivateMemberships: the public and the protected imports of
    // a base re-export through heritage; a private one does not.
    assert_eq!(inherited_names(&mut r, "P::SubG"), ["Shared"]);
    assert!(inherited_names(&mut r, "P::SubH").is_empty());
}

#[test]
fn filtered_import_diamond_is_path_independent() {
    // A is reached filtered and unfiltered; the unfiltered member must
    // arrive whichever path the walk takes first. Two shapes: the filter
    // as an import bracket, and as a `filter` member of the re-exporting
    // package.
    let shapes = [
        (
            "public import A::*[@Safety];",
            "public import B::*;",
            "public import A::*;",
        ),
        (
            "public import A::*;",
            "public import B::*;",
            "filter @Safety; public import A::*;",
        ),
    ];
    for (direct, via_b, b_body) in shapes {
        for (first, second) in [(direct, via_b), (via_b, direct)] {
            let mut r = build(&format!(
                "package P {{
                    metadata def Safety;
                    package A {{ part def Plain; #Safety part def Safe; }}
                    package B {{ {b_body} }}
                    part def Base {{ {first} {second} }}
                    part def Sub :> Base;
                 }}"
            ));
            assert_eq!(
                inherited_names(&mut r, "P::Sub"),
                ["Plain", "Safe"],
                "B: `{b_body}`, order: {first} {second}"
            );
        }
    }
}

#[test]
fn short_name_implicit_redefinition_shadows_like_lookup() {
    let mut r = build(
        "package P {
            part def A { part <sn> long; }
            part def B :> A { part sn; }
         }",
    );
    // `sn` looked up in B resolves the owned usage over the inherited one
    // whose short name it matches, so enumeration drops the inherited one.
    assert!(inherited_names(&mut r, "P::B").is_empty());
}

#[test]
fn owned_redefinition_seed_is_one_hop() {
    // KerML removeRedefinedFeatures, second condition: the owned side
    // contributes `ownedFeature.redefinition.redefinedFeature` — one hop.
    // `z` redefines `Other::o`, which redefines `x`; `x` arrives from
    // `Base` unredefined by any inherited candidate, so it stays.
    let mut r = build(
        "package P {
            part def Base { attribute x; }
            part def Other :> Base { attribute o :>> x; }
            part def Sub :> Base { attribute z :>> Other::o; }
         }",
    );
    assert_eq!(inherited_names(&mut r, "P::Sub"), ["x"]);
}

#[test]
fn deep_heritage_reports_truncation_and_terminates() {
    // The walk shares lookup's recursion budget; past it the enumeration
    // says so instead of silently presenting a cut result.
    let chain = |n: usize| -> String {
        let mut src = String::from("package P { part def T0 { attribute a0; }");
        for i in 1..=n {
            src.push_str(&format!(
                " part def T{i} :> T{} {{ attribute a{i}; }}",
                i - 1
            ));
        }
        src.push('}');
        src
    };
    let mut r = build(&chain(10));
    let leaf = r.resolve_qualified("P::T10").unwrap();
    assert!(!r.inheritance_walk_truncated(leaf, false));
    assert_eq!(r.inherited_features(leaf, false).len(), 10);

    let mut r = build(&chain(30));
    let leaf = r.resolve_qualified("P::T30").unwrap();
    assert!(r.inheritance_walk_truncated(leaf, false));
    let n = r.inherited_features(leaf, false).len();
    assert!((24..30).contains(&n), "cut at the budget, got {n}");
    // A shallow type in the same model is complete.
    let mid = r.resolve_qualified("P::T5").unwrap();
    assert!(!r.inheritance_walk_truncated(mid, false));
}

#[test]
fn recursive_import_descends_whatever_the_import_order() {
    // A scope first reached through a plain `Q::*` import must still be
    // descended when a later `::**` import reaches it recursively: the
    // visit key carries the recursion flag, as lookup always descends.
    for imports in [
        "public import Outer::Q::*; public import Outer::**;",
        "public import Outer::**; public import Outer::Q::*;",
    ] {
        let mut r = build(&format!(
            "package P {{
                package Outer {{ package Q {{ package Deep {{ part def X; }} }} }}
                part def Base {{ {imports} }}
                part def Sub :> Base;
             }}"
        ));
        let names = inherited_names(&mut r, "P::Sub");
        assert!(names.contains(&"X".to_string()), "{imports}: {names:?}");
    }
}
