#![cfg(feature = "json")]

use sysmlv2_parser::json::{ClosurePolicy, Derived, DerivedValue, ElementRef, ResolvedModel};
use sysmlv2_parser::model::Model;

fn build(source: &str) -> ResolvedModel {
    let mut model = Model::new();
    model.add_source("positions.kerml", source);
    assert!(
        !model.has_errors(),
        "{:?}",
        model
            .units()
            .iter()
            .flat_map(|u| &u.diagnostics)
            .collect::<Vec<_>>()
    );
    ResolvedModel::build(&model)
}

fn elements(r: &mut ResolvedModel, e: ElementRef, property: &str) -> Vec<ElementRef> {
    match r.derived(e, property) {
        Derived::Value(DerivedValue::Elements(values)) => values,
        other => panic!("{property}: {other:?}"),
    }
}

fn implied_targets(r: &mut ResolvedModel, name: &str) -> Vec<String> {
    let e = r.resolve_qualified(name).unwrap();
    r.implied_relationships(e)
        .into_iter()
        .filter(|&edge| r.element_type(edge) == "Redefinition")
        .collect::<Vec<_>>()
        .into_iter()
        .map(|edge| {
            r.property(edge, "redefinedFeature").unwrap()["@id"]
                .as_str()
                .unwrap()
                .to_owned()
        })
        .collect()
}

fn id(r: &mut ResolvedModel, name: &str) -> String {
    let e = r.resolve_qualified(name).unwrap();
    r.element_id(e).to_string()
}

#[test]
fn ends_match_positions_not_names_and_preserve_compact_storage() {
    let mut r = build(
        "package P {
        assoc Base { end feature a; end feature b; }
        assoc Sub specializes Base { end feature b; end feature a; }
    }",
    );
    let base_a = id(&mut r, "P::Base::a");
    let base_b = id(&mut r, "P::Base::b");
    let sub = r.resolve_qualified("P::Sub").unwrap();
    let owned_before = r.owned_relationships(sub);
    assert_eq!(implied_targets(&mut r, "P::Sub::b"), [base_a]);
    assert_eq!(implied_targets(&mut r, "P::Sub::a"), [base_b]);
    assert_eq!(r.owned_relationships(sub), owned_before);
    assert_eq!(r.inherited_memberships(sub, false).len(), 2);
    assert_eq!(r.inherited_memberships(sub, true).len(), 0);
    assert_eq!(r.inherited_memberships(sub, false).len(), 2);
    r.set_closure_policy(ClosurePolicy::Closure {
        include_implied: true,
    });
    assert_eq!(elements(&mut r, sub, "endFeature").len(), 2);
    let mut model = Model::new();
    model.add_source(
        "positions.kerml",
        "package P { assoc A { end feature a; } assoc B specializes A { end feature b; } }",
    );
    let mut exported = ResolvedModel::build(&model);
    let full =
        sysmlv2_parser::full::resolved_to_full_json(&mut exported, &model, Default::default())
            .unwrap();
    assert!(
        full.as_array()
            .unwrap()
            .iter()
            .any(|e| e["@type"] == "Redefinition" && e["isImplied"] == true)
    );
    for e in full.as_array().unwrap() {
        if e["isImplied"] == true {
            assert_eq!(e["isImpliedIncluded"], true);
        }
    }
}

#[test]
fn parameters_and_results_use_effective_slots() {
    let mut r = build(
        "package P {
        function Base { in x; return result; }
        function Mid specializes Base;
        function Sub specializes Mid { in y; return answer; }
        function Direct specializes Base { in z; return value; }
    }",
    );
    let result = id(&mut r, "P::Base::result");
    let x = id(&mut r, "P::Base::x");
    // `Mid` inherits `x` after its (absent) own parameters, so `Sub`'s
    // first parameter pairs with it, as `Sub`'s result pairs with the
    // result `Mid` inherits.
    assert_eq!(
        implied_targets(&mut r, "P::Sub::y").as_slice(),
        std::slice::from_ref(&x)
    );
    assert_eq!(
        implied_targets(&mut r, "P::Sub::answer").as_slice(),
        std::slice::from_ref(&result)
    );
    assert_eq!(
        implied_targets(&mut r, "P::Direct::z").as_slice(),
        std::slice::from_ref(&x)
    );
    assert_eq!(implied_targets(&mut r, "P::Direct::value"), [result]);
}

#[test]
fn inherited_anonymous_return_is_redefined_by_identity() {
    let mut r = build(
        "package P {
        class Value; function Base { return : Value; }
        function Mid specializes Base;
        function Sub specializes Mid { return answer; }
    }",
    );
    let base = r.resolve_qualified("P::Base").unwrap();
    let owned = elements(&mut r, base, "ownedFeature");
    assert_eq!(owned.len(), 1);
    let expected = r.element_id(owned[0]).to_string();
    let mid = r.resolve_qualified("P::Mid").unwrap();
    assert_eq!(r.inherited_memberships(mid, true).len(), 1);
    assert_eq!(implied_targets(&mut r, "P::Sub::answer"), [expected]);
}

#[test]
fn effective_end_order_follows_direct_supertype_order() {
    let mut r = build(
        "package P {
        assoc First { end feature a; }
        assoc Second { end feature b; }
        assoc Mid specializes Second, First;
        assoc Sub specializes Mid { end feature x; end feature y; }
    }",
    );
    let a = id(&mut r, "P::First::a");
    let b = id(&mut r, "P::Second::b");
    assert_eq!(implied_targets(&mut r, "P::Sub::x"), [b]);
    assert_eq!(implied_targets(&mut r, "P::Sub::y"), [a]);
}

#[test]
fn cycles_do_not_invent_positional_targets() {
    let mut r = build(
        "package P {
        assoc A specializes B { end feature a; }
        assoc B specializes A { end feature b; }
    }",
    );
    assert!(implied_targets(&mut r, "P::A::a").is_empty());
    assert!(implied_targets(&mut r, "P::B::b").is_empty());
    let a = r.resolve_qualified("P::A").unwrap();
    assert!(r.inheritance_incomplete(a, true));
    assert!(!r.inheritance_walk_truncated(a, true));
}

#[test]
fn standard_library_subjects_results_and_binary_ends_are_not_duplicated() {
    let mut model = Model::new();
    model
        .load_library_dir(&sysmlv2_testkit::library_dir())
        .unwrap();
    model.add_source(
        "roles.sysml",
        "package P {
        requirement def R { subject selected; }
        requirement r : R;
        part a; part b; connection c connect a to b;
    }",
    );
    assert!(!model.has_errors());
    let mut r = ResolvedModel::build(&model);
    r.set_closure_policy(ClosurePolicy::Closure {
        include_implied: true,
    });
    let req = r.resolve_qualified("P::R").unwrap();
    let params = elements(&mut r, req, "parameter");
    assert_eq!(params.len(), 2);
    let usage = r.resolve_qualified("P::r").unwrap();
    assert_eq!(elements(&mut r, usage, "parameter").len(), 2);
    let connection = r.resolve_qualified("P::c").unwrap();
    assert_eq!(elements(&mut r, connection, "connectorEnd").len(), 2);
    let expected = id(&mut r, "Requirements::RequirementCheck::subj");
    assert_eq!(implied_targets(&mut r, "P::R::selected"), [expected]);
    assert_eq!(
        implied_targets(&mut r, "Requirements::RequirementConstraintCheck::result").len(),
        1
    );
}

#[test]
fn effective_inherited_slots_group_public_before_protected() {
    let mut r = build(
        "package P {
        assoc Base { protected end feature p; public end feature q; }
        assoc Mid specializes Base;
        assoc Sub specializes Mid { end feature x; end feature y; }
    }",
    );
    let p = id(&mut r, "P::Base::p");
    let q = id(&mut r, "P::Base::q");
    assert_eq!(implied_targets(&mut r, "P::Sub::x"), [q]);
    assert_eq!(implied_targets(&mut r, "P::Sub::y"), [p]);
}

#[test]
fn private_base_end_has_a_position_but_is_not_inherited() {
    let mut r = build(
        "package P {
        assoc Base { private end feature p; end feature q; }
        assoc Sub specializes Base { end feature x; end feature y; }
        assoc Mid specializes Base;
        assoc Leaf specializes Mid { end feature z; }
    }",
    );
    let q = id(&mut r, "P::Base::q");
    assert_eq!(implied_targets(&mut r, "P::Sub::x").len(), 1);
    assert_eq!(
        implied_targets(&mut r, "P::Sub::y").as_slice(),
        std::slice::from_ref(&q)
    );
    assert_eq!(implied_targets(&mut r, "P::Leaf::z"), [q]);
}

#[test]
fn prepared_library_and_query_order_preserve_positional_relationships() {
    let library = "library package L { assoc Base { end feature a; end feature b; } }";
    let source = "package P { assoc Sub specializes L::Base { end feature x; end feature y; } }";
    let mut base = Model::new();
    base.add_library_source("lib.kerml", library);
    let prepared = base.prepare_library().unwrap();
    let mut snapshots = Vec::new();
    for use_prepared in [false, true] {
        for materialize_first in [false, true] {
            let mut model = Model::new();
            if use_prepared {
                prepared.clone().install(&mut model).unwrap();
            } else {
                model.add_library_source("lib.kerml", library);
            }
            model.add_source("p.kerml", source);
            let mut r = ResolvedModel::build(&model);
            let sub = r.resolve_qualified("P::Sub").unwrap();
            if materialize_first {
                r.implied_relationships(sub);
            }
            assert_eq!(r.inherited_memberships(sub, false).len(), 2);
            assert!(r.inherited_memberships(sub, true).is_empty());
            let x = r.resolve_qualified("P::Sub::x").unwrap();
            let rels = r.implied_relationships(x);
            let snapshot: Vec<_> = rels
                .into_iter()
                .map(|e| (r.element_id(e), r.element_properties(e)))
                .collect();
            snapshots.push(snapshot);
        }
    }
    assert!(snapshots.windows(2).all(|w| w[0] == w[1]));
}

#[test]
fn unresolved_or_imported_slot_sequences_are_reported_incomplete() {
    let mut r = build(
        "package P {
        assoc Unknown specializes Missing { end feature a; }
        assoc Base { end feature x; }
        assoc Nested { public import Base::x; }
        assoc Imported { public import Nested::*; }
        assoc Sub specializes Imported { end feature b; }
    }",
    );
    for (owner, feature) in [("P::Unknown", "P::Unknown::a"), ("P::Sub", "P::Sub::b")] {
        assert!(implied_targets(&mut r, feature).is_empty());
        let owner = r.resolve_qualified(owner).unwrap();
        assert!(r.inheritance_incomplete(owner, true));
        assert!(!r.inheritance_walk_truncated(owner, true));
    }
}

#[test]
fn mixed_depth_inheritance_and_positional_targets_share_order() {
    let mut r = build(
        "package P {
        assoc A { end feature a; }
        assoc B specializes A;
        assoc C { end feature c; }
        assoc D specializes B, C;
        assoc E specializes D { end feature x; end feature y; }
    }",
    );
    let a = r.resolve_qualified("P::A::a").unwrap();
    let c = r.resolve_qualified("P::C::c").unwrap();
    let d = r.resolve_qualified("P::D").unwrap();
    r.set_closure_policy(ClosurePolicy::Closure {
        include_implied: true,
    });
    assert_eq!(elements(&mut r, d, "endFeature"), [a, c]);
    let ai = r.element_id(a).to_string();
    let ci = r.element_id(c).to_string();
    assert_eq!(implied_targets(&mut r, "P::E::x"), [ai]);
    assert_eq!(implied_targets(&mut r, "P::E::y"), [ci]);
}

#[test]
fn intermediate_owned_redefinition_removal_survives_further_inheritance() {
    let mut r = build(
        "package P {
        class A { feature x; }
        class B specializes A { feature y redefines A::x; }
        class C specializes B { feature z redefines A::x; }
        class D specializes C;
    }",
    );
    let z = r.resolve_qualified("P::C::z").unwrap();
    let d = r.resolve_qualified("P::D").unwrap();
    for implied in [false, true] {
        let members = r.inherited_memberships(d, implied);
        let features: Vec<_> = members
            .into_iter()
            .filter_map(|m| r.membership_member(m))
            .collect();
        assert_eq!(features, [z]);
    }
}

#[test]
fn every_direct_base_contributes_and_unrelated_explicit_redefinition_does_not_exempt_ends() {
    let mut r = build(
        "package P {
        assoc A { end feature a; end feature extra; }
        assoc B { end feature b; }
        assoc C specializes A, B { end feature x redefines A::extra; }
    }",
    );
    let a = id(&mut r, "P::A::a");
    let b = id(&mut r, "P::B::b");
    assert_eq!(implied_targets(&mut r, "P::C::x"), [a, b]);
}

#[test]
fn identity_overrides_preserve_positional_edges_before_and_after_materialization() {
    for materialize_first in [false, true] {
        let mut r = build(
            "package P { assoc A { end feature a; } assoc B specializes A { end feature b; } }",
        );
        let a = r.resolve_qualified("P::A::a").unwrap();
        let old_id = r.element_id(a);
        if materialize_first {
            implied_targets(&mut r, "P::B::b");
        }
        let new_id = uuid::Uuid::new_v5(&uuid::Uuid::NAMESPACE_OID, b"positional target override");
        r.override_ids(&std::collections::HashMap::from([(old_id, new_id)]));
        assert_eq!(implied_targets(&mut r, "P::B::b"), [new_id.to_string()]);
        let b = r.resolve_qualified("P::B::b").unwrap();
        assert!(r.conforms_with_implied(b, a));
    }
}

#[test]
fn semantic_incompleteness_does_not_masquerade_as_a_depth_cut() {
    let mut model = Model::new();
    model.add_source("cycle.kerml", "package P { assoc A specializes B { end feature a; } assoc B specializes A { end feature b; } }");
    let mut r = ResolvedModel::build(&model);
    let a = r.resolve_qualified("P::A").unwrap();
    assert!(r.inheritance_incomplete(a, true));
    assert!(!r.inheritance_walk_truncated(a, true));
    r.set_closure_policy(ClosurePolicy::Closure {
        include_implied: true,
    });
    assert_eq!(
        r.derived_exact(a, "endFeature"),
        Err(sysmlv2_parser::json::PropertyError::Approximate)
    );
    assert!(r.to_full_json_strict().is_err());
    let policy = sysmlv2_parser::full::EmissionPolicy {
        closures: ClosurePolicy::Closure {
            include_implied: true,
        },
        ..Default::default()
    };
    assert!(sysmlv2_parser::full::resolved_to_full_json(&mut r, &model, policy).is_ok());
}

#[test]
fn imported_feature_slots_enter_through_inheritance_not_direct_imports() {
    for import in ["public import A::a;", "public import A::*;"] {
        let mut r = build(&format!(
            "package P {{
            assoc A {{ end feature a; }}
            assoc Base {{ {import} }}
            assoc Child specializes Base {{ end feature x; }}
            assoc Grand specializes Child {{ end feature slotOne; end feature slotTwo; }}
        }}"
        ));
        r.set_closure_policy(ClosurePolicy::Closure {
            include_implied: true,
        });
        let base = r.resolve_qualified("P::Base").unwrap();
        let child = r.resolve_qualified("P::Child").unwrap();
        let a = r.resolve_qualified("P::A::a").unwrap();
        let x = r.resolve_qualified("P::Child::x").unwrap();
        assert!(elements(&mut r, base, "endFeature").is_empty());
        assert_eq!(elements(&mut r, child, "endFeature"), [x, a]);
        assert!(implied_targets(&mut r, "P::Child::x").is_empty());
        let xi = r.element_id(x).to_string();
        let ai = r.element_id(a).to_string();
        assert_eq!(implied_targets(&mut r, "P::Grand::slotOne"), [xi]);
        assert_eq!(implied_targets(&mut r, "P::Grand::slotTwo"), [ai]);
        assert!(!r.inheritance_incomplete(child, true));
    }
}

#[test]
fn imported_aliases_and_package_owned_features_do_not_create_slots() {
    let mut r = build(
        "package P {
        assoc A { end feature a; alias renamed for a; }
        package N { feature p; }
        assoc Base { public import A::renamed; public import N::p; }
        assoc Child specializes Base;
        assoc Grand specializes Child { end feature x; }
    }",
    );
    r.set_closure_policy(ClosurePolicy::Closure {
        include_implied: true,
    });
    let child = r.resolve_qualified("P::Child").unwrap();
    assert_eq!(r.inherited_memberships(child, true).len(), 2);
    assert!(elements(&mut r, child, "feature").is_empty());
    assert!(implied_targets(&mut r, "P::Grand::x").is_empty());
    assert!(!r.inheritance_incomplete(child, true));
}

#[test]
fn import_admission_controls_visibility_and_positional_order() {
    let mut r = build("package P {
        assoc A { private end feature hidden; end feature a; }
        assoc Base {
            protected end feature p;
            protected import A::a;
            public import all A::hidden;
            public end feature q;
        }
        assoc Child specializes Base;
        assoc Grand specializes Child { end feature slotOne; end feature slotTwo; end feature slotThree; end feature slotFour; }
    }");
    r.set_closure_policy(ClosurePolicy::Closure {
        include_implied: true,
    });
    let child = r.resolve_qualified("P::Child").unwrap();
    let expected: Vec<_> = ["P::Base::q", "P::A::hidden", "P::Base::p", "P::A::a"]
        .into_iter()
        .map(|name| r.resolve_qualified(name).unwrap())
        .collect();
    assert_eq!(elements(&mut r, child, "endFeature"), expected);
    for (name, target) in ["slotOne", "slotTwo", "slotThree", "slotFour"]
        .into_iter()
        .zip(expected)
    {
        let target = r.element_id(target).to_string();
        assert_eq!(
            implied_targets(&mut r, &format!("P::Grand::{name}")),
            [target]
        );
    }
}

#[test]
fn imported_memberships_enter_effective_results_and_parameters() {
    let mut r = build(
        "package P {
        function F { in a; return r; alias namedResult for r; }
        function Base { public import F::r; public import F::a; }
        function Child specializes Base;
        function Grand specializes Child { in x; return answer; }
        function AliasBase { public import F::namedResult; }
        function AliasChild specializes AliasBase;
        function AliasGrand specializes AliasChild { return answer; }
    }",
    );
    let result = id(&mut r, "P::F::r");
    let a = id(&mut r, "P::F::a");
    assert_eq!(implied_targets(&mut r, "P::Grand::answer"), [result]);
    assert_eq!(implied_targets(&mut r, "P::Grand::x"), [a]);
    assert!(implied_targets(&mut r, "P::AliasGrand::answer").is_empty());
}

#[test]
fn imported_slots_agree_for_fresh_prepared_and_serialized_prepared_libraries() {
    use std::sync::Arc;
    use sysmlv2_parser::prepared::PreparedLibrary;
    let library = "standard library package P { assoc A { end feature a; } assoc Base { public import A::a; } assoc Child specializes Base; }";
    let user = "assoc Grand specializes P::Child { end feature slotOne; }";
    let mut base = Model::new();
    base.add_library_source("imports.kerml", library);
    let prepared = base.prepare_library().unwrap();
    let serialized =
        Arc::new(PreparedLibrary::from_bytes(&prepared.to_bytes(11).unwrap(), 11).unwrap());
    let mut targets = Vec::new();
    for mode in 0..3 {
        let mut model = Model::new();
        if mode == 0 {
            model.add_library_source("imports.kerml", library);
        } else if mode == 1 {
            Arc::clone(&prepared).install(&mut model).unwrap();
        } else {
            Arc::clone(&serialized).install(&mut model).unwrap();
        }
        model.add_source("user.kerml", user);
        let mut r = ResolvedModel::build(&model);
        let child = r.resolve_qualified("P::Child").unwrap();
        assert_eq!(r.inherited_memberships(child, true).len(), 1);
        let expected = id(&mut r, "P::A::a");
        let actual = implied_targets(&mut r, "Grand::slotOne");
        assert_eq!(actual, [expected]);
        targets.push(actual);
    }
    assert!(targets.windows(2).all(|pair| pair[0] == pair[1]));
}

#[test]
fn visibility_specific_import_slots_retain_same_names_and_exclude_private_paths() {
    let mut r = build(
        "package P {
        assoc A { end feature x; }
        assoc B { end feature x; }
        assoc C { end feature x; }
        assoc Base { protected import B::x; private import C::x; public import A::x; }
        assoc Child specializes Base;
        assoc Grand specializes Child { end feature slotOne; end feature slotTwo; }
    }",
    );
    r.set_closure_policy(ClosurePolicy::Closure {
        include_implied: true,
    });
    let a = r.resolve_qualified("P::A::x").unwrap();
    let b = r.resolve_qualified("P::B::x").unwrap();
    let child = r.resolve_qualified("P::Child").unwrap();
    assert_eq!(elements(&mut r, child, "endFeature"), [a, b]);
    let ai = r.element_id(a).to_string();
    let bi = r.element_id(b).to_string();
    assert_eq!(implied_targets(&mut r, "P::Grand::slotOne"), [ai]);
    assert_eq!(implied_targets(&mut r, "P::Grand::slotTwo"), [bi]);
}

#[test]
fn unresolved_import_provider_heritage_does_not_supply_partial_positions() {
    let mut r = build(
        "package P {
        assoc Provider specializes Unknown { end feature a; }
        assoc Base { public import Provider::*; }
        assoc Child specializes Base;
        assoc Grand specializes Child { end feature slot; }
    }",
    );
    let grand = r.resolve_qualified("P::Grand").unwrap();
    assert!(implied_targets(&mut r, "P::Grand::slot").is_empty());
    assert!(r.inheritance_incomplete(grand, true));
}

#[test]
fn inheritance_preserves_alias_positions_among_owned_and_imported_memberships() {
    let mut r = build(
        "package P {
        class Values { feature imported; class AliasTarget; }
        class Base {
            feature a;
            alias publicAlias for Values::AliasTarget;
            public import Values::imported;
            protected feature b;
            protected alias protectedAlias for Values::AliasTarget;
        }
        class Child specializes Base;
    }",
    );
    let child = r.resolve_qualified("P::Child").unwrap();
    let memberships = r.inherited_memberships(child, false);
    let names: Vec<_> = memberships
        .into_iter()
        .map(|m| r.membership_member_name(m).unwrap())
        .collect();
    assert_eq!(
        names,
        ["a", "publicAlias", "imported", "b", "protectedAlias"]
    );
}

#[test]
fn library_flow_and_succession_ends_redefine_their_actual_bases() {
    let mut model = Model::new();
    model
        .load_library_dir(&sysmlv2_testkit::library_dir())
        .unwrap();
    model.add_source(
        "flows.sysml",
        r#"package P {
        port def Out { out attribute v : ScalarValues::Real; }
        part def Box { port o : Out; port i : ~Out; }
        part def System {
            part a : Box; part b : Box;
            flow from a.o.v to b.i.v;
        }
        action def Steps { action a; action b; first a then b; }
    }"#,
    );
    assert!(!model.has_errors());
    let mut r = ResolvedModel::build(&model);
    r.set_closure_policy(ClosurePolicy::Closure {
        include_implied: true,
    });
    let connectors: Vec<_> = r
        .user_elements()
        .filter(|&e| matches!(r.element_type(e), "FlowUsage" | "SuccessionAsUsage"))
        .collect();
    assert_eq!(connectors.len(), 2);
    for connector in connectors {
        let ends = elements(&mut r, connector, "ownedEndFeature");
        assert_eq!(ends.len(), 2);
        assert_eq!(elements(&mut r, connector, "connectorEnd"), ends);
        for end in ends {
            assert!(
                r.implied_relationships(end)
                    .into_iter()
                    .any(|edge| r.element_type(edge) == "Redefinition"),
                "{} has no implied end redefinition",
                r.element_type(connector)
            );
        }
        assert!(!r.inheritance_incomplete(connector, true));
    }
    for name in [
        "Flows::MessageAction",
        "Flows::messages",
        "Transfers::flowTransfers",
    ] {
        let base = r.resolve_qualified(name).unwrap();
        assert!(!r.inheritance_incomplete(base, true), "cyclic base: {name}");
    }
}
