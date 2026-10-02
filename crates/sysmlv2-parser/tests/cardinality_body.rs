//! Body and named multiplicity domains retain exact bounds and stored identity.
#![cfg(feature = "json")]

use std::sync::Arc;
use sysmlv2_parser::{
    eval::Value, json::ResolvedModel, libcache::LibraryCache, model::Model,
    prepared::PreparedLibrary,
};

fn models(library: &str, user: &str) -> Vec<ResolvedModel> {
    let mut base = Model::new();
    let unit = base.add_library_source("bounds.kerml", library);
    assert!(unit.diagnostics.is_empty(), "{:?}", unit.diagnostics);
    assert!(!base.has_errors());
    base.record_library_cache();
    ResolvedModel::build(&base);
    let cache =
        LibraryCache::from_bytes(&base.take_recorded_library_cache().unwrap().to_bytes()).unwrap();
    let prepared = base.prepare_library().unwrap();
    let decoded =
        Arc::new(PreparedLibrary::from_bytes(&prepared.to_bytes(31).unwrap(), 31).unwrap());
    (0..4)
        .map(|mode| {
            let mut model = Model::new();
            match mode {
                2 => Arc::clone(&prepared).install(&mut model).unwrap(),
                3 => Arc::clone(&decoded).install(&mut model).unwrap(),
                _ => {
                    model.add_library_source("bounds.kerml", library);
                    if mode == 1 {
                        model.set_library_cache(cache.clone());
                    }
                }
            }
            let unit = model.add_source("user.kerml", user);
            assert!(unit.diagnostics.is_empty(), "{:?}", unit.diagnostics);
            assert!(!model.has_errors());
            ResolvedModel::build(&model)
        })
        .collect()
}

fn bounds(r: &mut ResolvedModel, name: &str, expected: Option<(i128, Option<i128>)>) {
    let e = r.resolve_qualified(name).unwrap();
    assert_eq!(r.effective_cardinality(e), expected, "{name}");
}

#[test]
fn body_ranges_match_header_bounds_without_rounding() {
    for mut r in models(
        "",
        "package P {
        feature exact { multiplicity [4]; }
        feature interval { multiplicity [2..5]; }
        feature empty { multiplicity [0]; }
        feature any { multiplicity [*]; }
        feature anyRange { multiplicity [0..*]; }
        feature big { multiplicity [9223372036854775809]; }
        feature overflow { multiplicity [170141183460469231731687303715884105728]; }
        feature reversed { multiplicity [5..2]; }
        feature real { multiplicity [2.5]; }
        feature missing { multiplicity [absent]; }
        feature negative = -1;
        feature invalidNegative { multiplicity [negative]; }
        feature infinity = *;
        feature invalidLower { multiplicity [infinity..5]; }
        feature duplicateBody { multiplicity [1]; multiplicity [2]; }
        feature base[2];
        feature local subsets base { multiplicity [4]; }
        feature duplicate[1] { multiplicity [2]; }
        feature answer = size(exact);
        feature emptyAnswer = isEmpty(empty);
        feature nonemptyAnswer = notEmpty(interval);
        feature badIndex = exact#(5);
    }",
    ) {
        for (name, expected) in [
            ("exact", Some((4, Some(4)))),
            ("interval", Some((2, Some(5)))),
            ("empty", Some((0, Some(0)))),
            ("any", Some((0, None))),
            ("anyRange", Some((0, None))),
            (
                "big",
                Some((9223372036854775809, Some(9223372036854775809))),
            ),
            ("overflow", None),
            ("reversed", None),
            ("real", None),
            ("missing", None),
            ("invalidNegative", None),
            ("invalidLower", None),
            ("duplicateBody", None),
            ("local", Some((4, Some(4)))),
            ("duplicate", None),
        ] {
            bounds(&mut r, &format!("P::{name}"), expected);
        }
        for (name, expected) in [
            ("answer", Value::Integer(4)),
            ("emptyAnswer", Value::Boolean(true)),
            ("nonemptyAnswer", Value::Boolean(true)),
        ] {
            let e = r.resolve_qualified(&format!("P::{name}")).unwrap();
            assert_eq!(r.evaluate(e), Ok(expected));
        }
        let e = r.resolve_qualified("P::badIndex").unwrap();
        assert!(matches!(
            r.evaluate(e),
            Err(sysmlv2_parser::eval::EvalError::Type(_))
        ));
    }
}

#[test]
fn named_domains_follow_aliases_and_do_not_become_feature_cardinalities() {
    for mut r in models(
        "package A {
        multiplicity four[4];
        alias rangeAlias for four;
        multiplicity chain subsets rangeAlias;
        feature base { multiplicity subsets chain; }
    }",
        "package B {
        feature direct { multiplicity subsets A::four; }
        feature indirect { multiplicity subsets A::chain; }
        feature inherited subsets A::base;
        feature unrelated { alias named for A::four; }
    }",
    ) {
        for _ in 0..2 {
            for name in ["B::direct", "B::indirect", "B::inherited", "A::base"] {
                bounds(&mut r, name, Some((4, Some(4))));
            }
            for name in ["A::four", "B::unrelated"] {
                bounds(&mut r, name, Some((0, None)));
            }
        }
        bounds(&mut r, "A::chain", None);
        // Force the UUID lookup index before changing both kinds of endpoint.
        let a = r.resolve_qualified("A::four").unwrap();
        let b = r.resolve_qualified("A::chain").unwrap();
        r.override_ids(&std::collections::HashMap::from([
            (
                r.element_id(a),
                "11111111-1111-4111-8111-111111111111".parse().unwrap(),
            ),
            (
                r.element_id(b),
                "22222222-2222-4222-8222-222222222222".parse().unwrap(),
            ),
        ]));
        bounds(&mut r, "B::direct", Some((4, Some(4))));
        bounds(&mut r, "B::indirect", Some((4, Some(4))));
    }
}

#[test]
fn unresolved_cycles_and_non_multiplicity_targets_stay_unknown() {
    for mut r in models(
        "package A {
        multiplicity bare subsets missing;
        multiplicity a subsets b;
        multiplicity b subsets a;
        feature ordinary[4];
    }",
        "package B {
        feature noDomain { multiplicity subsets A::bare; }
        feature cyclic { multiplicity subsets A::a; }
        feature absent { multiplicity subsets A::missing; }
        feature wrongKind { multiplicity subsets A::ordinary; }
    }",
    ) {
        for _ in 0..2 {
            for name in ["noDomain", "cyclic", "absent", "wrongKind"] {
                bounds(&mut r, &format!("B::{name}"), None);
            }
        }
    }
}

#[test]
fn graph_bounds_use_recorded_lexical_identity_and_restore_lambda_environment() {
    for mut r in models(
        "package A {
        feature n = 4;
        alias count for n;
        multiplicity four[count];
        feature base { multiplicity [count]; }
    }",
        "package B {
        feature n = 2;
        feature narrowed subsets A::base;
        feature named { multiplicity subsets A::four; }
        feature answer = (2, 3)->collect { in n; size(A::base) + n };
    }",
    ) {
        bounds(&mut r, "B::narrowed", Some((4, Some(4))));
        bounds(&mut r, "B::named", Some((4, Some(4))));
        let e = r.resolve_qualified("B::answer").unwrap();
        assert_eq!(
            r.evaluate(e),
            Ok(Value::Sequence(vec![Value::Integer(6), Value::Integer(7)]))
        );
        let n = r.resolve_qualified("A::n").unwrap();
        r.override_ids(&std::collections::HashMap::from([(
            r.element_id(n),
            "33333333-3333-4333-8333-333333333333".parse().unwrap(),
        )]));
        bounds(&mut r, "B::narrowed", Some((4, Some(4))));
        bounds(&mut r, "B::named", Some((4, Some(4))));
    }
}

#[test]
fn graph_bounds_select_valuations_independently_of_spelling() {
    for mut r in models(
        "package A { class Base {
        feature n = 4;
        feature simple { multiplicity [n]; }
        feature qualified { multiplicity [Base::n]; }
        alias countAlias for n;
        feature aliased { multiplicity [countAlias]; }
    } }",
        "package B { class Child specializes A::Base {
        feature redefines n = 6;
        feature redefines simple;
        feature redefines qualified;
        feature redefines aliased;
    } }",
    ) {
        bounds(&mut r, "A::Base::simple", Some((4, Some(4))));
        bounds(&mut r, "A::Base::qualified", Some((4, Some(4))));
        bounds(&mut r, "B::Child::simple", Some((6, Some(6))));
        bounds(&mut r, "B::Child::qualified", Some((6, Some(6))));
        bounds(&mut r, "B::Child::aliased", Some((6, Some(6))));
    }
}

#[test]
fn bound_value_and_domain_cycles_terminate() {
    for mut r in models(
        "",
        "package P {
        feature n = size(f);
        multiplicity recursive[n];
        feature f { multiplicity subsets recursive; }
        feature valid { multiplicity [3]; }
    }",
    ) {
        for _ in 0..2 {
            bounds(&mut r, "P::f", None);
            bounds(&mut r, "P::valid", Some((3, Some(3))));
        }
    }
}

#[test]
fn body_cardinality_preserves_unknown_receivers_and_call_arguments() {
    for mut r in models(
        "",
        "package P {
        class Rack { feature count default = 4;
            feature slots { multiplicity [count]; }
            feature fixed { multiplicity [4]; }
        }
        function Inputs { in unit : Rack[1]; }
        feature unknownCount = size(Inputs::unit.slots);
        feature fixedCount = size(Inputs::unit.fixed);
        function Count { in n default = 4;
            feature p { multiplicity [n]; } return result = size(p);
        }
        feature called = Count(2);
    }",
    ) {
        for (name, expected) in [
            ("unknownCount", Value::Indeterminate),
            ("fixedCount", Value::Integer(4)),
            ("called", Value::Indeterminate),
        ] {
            let e = r.resolve_qualified(&format!("P::{name}")).unwrap();
            assert_eq!(r.evaluate(e), Ok(expected), "{name}");
        }
    }
}

#[test]
fn contextual_named_domains_keep_receiver_identity() {
    for mut r in models(
        "package A { class Base {
            feature n = 4;
            multiplicity dynamic[n];
            multiplicity pinned[$::A::Base::n];
            feature slots { multiplicity subsets dynamic; }
            feature fixed { multiplicity subsets pinned; }
            alias <short> 'bound alias' for n;
            feature viaAlias { multiplicity ['bound alias']; }
            feature viaShort { multiplicity [short]; }
        } }",
        "package B {
            class Child specializes A::Base { feature redefines n = 6;
                feature redefines slots; feature redefines fixed;
                feature redefines viaAlias; feature redefines viaShort;
            }
            class Other specializes A::Base { feature redefines n = 9;
                feature redefines slots; feature redefines fixed;
            }
            class Shadow specializes A::Base { feature n = 7;
                feature redefines slots;
                feature 'bound alias' = 8; feature redefines viaAlias;
            }
            class Formula specializes A::Base { feature redefines n = 2+3;
                feature redefines slots;
            }
        }",
    ) {
        for _ in 0..2 {
            for (name, expected) in [
                ("B::Child::slots", Some((6, Some(6)))),
                ("B::Other::slots", Some((9, Some(9)))),
                ("A::Base::slots", Some((4, Some(4)))),
                ("B::Child::fixed", Some((6, Some(6)))),
                ("B::Other::fixed", Some((9, Some(9)))),
                ("B::Child::viaAlias", Some((6, Some(6)))),
                ("B::Child::viaShort", Some((6, Some(6)))),
                ("B::Shadow::slots", None),
                ("B::Shadow::viaAlias", None),
                ("B::Formula::slots", Some((5, Some(5)))),
            ] {
                bounds(&mut r, name, expected);
                let e = r.resolve_qualified(name).unwrap();
                r.implied_relationships(e);
            }
        }
        let n = r.resolve_qualified("A::Base::n").unwrap();
        r.override_ids(&std::collections::HashMap::from([(
            r.element_id(n),
            "55555555-5555-4555-8555-555555555555".parse().unwrap(),
        )]));
        bounds(&mut r, "B::Child::slots", Some((6, Some(6))));
        bounds(&mut r, "B::Child::fixed", Some((6, Some(6))));
    }
}

#[test]
fn contextual_graph_references_preserve_lexical_names_and_rebind_formula_dependencies() {
    for mut r in models(
        "package A { feature external = 4;
            class Base { feature n = 3; feature formula = n + 1;
                feature lexical { multiplicity [external]; }
                feature dependent { multiplicity [formula]; }
            }
        }",
        "package B { class Child specializes A::Base {
            feature external = 9; feature redefines n = 6;
            feature redefines lexical; feature redefines dependent;
        } }",
    ) {
        bounds(&mut r, "B::Child::lexical", Some((4, Some(4))));
        bounds(&mut r, "A::Base::dependent", Some((4, Some(4))));
        bounds(&mut r, "B::Child::dependent", Some((7, Some(7))));
    }
}

#[test]
fn identity_bound_referent_selects_redefinitions_after_id_changes() {
    let id = "66666666-6666-4666-8666-666666666666";
    let mut model = Model::new();
    let unit = model.add_source(
        "ids.kerml",
        &format!(
            "package P {{
        class Base {{ feature n = 4;
            feature slots {{ multiplicity ['{id}']; }}
        }}
        class Child specializes Base {{ feature redefines n = 6; feature redefines slots; }}
    }}"
        ),
    );
    assert!(unit.diagnostics.is_empty(), "{:?}", unit.diagnostics);
    let mut r = ResolvedModel::build(&model);
    let n = r.resolve_qualified("P::Base::n").unwrap();
    r.override_ids(&std::collections::HashMap::from([(
        r.element_id(n),
        id.parse().unwrap(),
    )]));
    assert!(
        r.bind_id_spelled_references()
            .contains(&id.parse().unwrap())
    );
    bounds(&mut r, "P::Child::slots", Some((6, Some(6))));
    r.override_ids(&std::collections::HashMap::from([(
        id.parse().unwrap(),
        "77777777-7777-4777-8777-777777777777".parse().unwrap(),
    )]));
    bounds(&mut r, "P::Child::slots", Some((6, Some(6))));
}

#[test]
fn bound_identity_is_scoped_to_its_source_unit() {
    let id = "88888888-8888-4888-8888-888888888888";
    let mut model = Model::new();
    for package in ["A", "B"] {
        let source = format!(
            "package {package} {{ class Base {{
            feature source = 4; feature '{id}' = 8;
            feature slots {{ multiplicity ['{id}']; }}
        }} class Child specializes Base {{
            feature redefines '{id}' = 9; feature redefines slots;
        }} }}"
        );
        let unit = model.add_source(format!("{package}.kerml"), &source);
        assert!(unit.diagnostics.is_empty(), "{:?}", unit.diagnostics);
    }
    let mut r = ResolvedModel::build(&model);
    let source = r.resolve_qualified("A::Base::source").unwrap();
    r.override_ids(&std::collections::HashMap::from([(
        r.element_id(source),
        id.parse().unwrap(),
    )]));
    let slots = r.resolve_qualified("A::Base::slots").unwrap();
    let multiplicity = r.owned_members(slots)[0];
    let expression = r.owned_members(multiplicity)[0];
    let membership = r.owned_relationships(expression)[0];
    let mut hints = std::collections::HashMap::from([(
        (r.element_id(membership), "memberElement".into()),
        id.parse().unwrap(),
    )]);
    assert!(
        r.bind_id_spelled_references_with(&mut hints)
            .contains(&id.parse().unwrap())
    );
    for _ in 0..2 {
        bounds(&mut r, "A::Child::slots", Some((4, Some(4))));
        bounds(&mut r, "B::Child::slots", Some((9, Some(9))));
    }
}

#[test]
fn contextual_bounds_do_not_hydrate_prepared_syntax() {
    let mut base = Model::new();
    base.add_library_source(
        "base.kerml",
        "package A { class Base {
        feature n = 4; feature formula = n + 1; multiplicity dynamic[formula];
        feature slots { multiplicity subsets dynamic; }
    } }",
    );
    let bytes = base.prepare_library().unwrap().to_bytes(31).unwrap();
    let library = Arc::new(PreparedLibrary::from_bytes(&bytes, 31).unwrap());
    let mut model = Model::new();
    library.install(&mut model).unwrap();
    model.add_source(
        "user.kerml",
        "package B { class Child specializes A::Base {
        feature redefines n = 6; feature redefines slots;
    } }",
    );
    assert_eq!(model.loaded_library_unit_count(), 0);
    let mut r = ResolvedModel::build(&model);
    for _ in 0..2 {
        bounds(&mut r, "B::Child::slots", Some((7, Some(7))));
    }
    assert_eq!(model.loaded_library_unit_count(), 0);
}

#[test]
fn identity_selection_requires_unique_redefinitions_and_complete_heritage() {
    for mut r in models("package A { class Base { feature n = 4;
        feature slots { multiplicity [n]; }
    } }", "package B {
        class Renamed specializes A::Base { feature other redefines n = 6; feature redefines slots; }
        class Shadow specializes A::Base { feature n = 7; feature redefines slots; }
        class Subset specializes A::Base { feature other subsets n = 7; feature redefines slots; }
        class Left specializes A::Base { feature left redefines n = 6; }
        class Right specializes A::Base { feature right redefines n = 6; }
        class Ambiguous specializes Left, Right { feature redefines slots; }
        class Middle specializes Renamed;
        class Diamond specializes Renamed, Middle { feature redefines slots; }
        class Incomplete specializes Renamed, absent { feature redefines slots; }
        class IncompleteChild specializes Incomplete { feature redefines slots; }
        class CycleA specializes A::Base, CycleB { feature redefines slots; }
        class CycleB specializes CycleA;
        class Two specializes A::Base { feature one redefines n = 6;
            feature two redefines n = 6; feature redefines slots; }
        class Bad specializes A::Base { feature other redefines missing = 7; feature redefines slots; }
    }") {
        bounds(&mut r, "B::Renamed::slots", Some((6, Some(6))));
        bounds(&mut r, "B::Shadow::slots", Some((4, Some(4))));
        bounds(&mut r, "B::Subset::slots", Some((4, Some(4))));
        bounds(&mut r, "B::Diamond::slots", Some((6, Some(6))));
        for name in ["B::Ambiguous::slots", "B::Incomplete::slots", "B::Bad::slots", "B::IncompleteChild::slots", "B::CycleA::slots", "B::Two::slots"] {
            bounds(&mut r, name, None);
        }
    }
}

#[test]
fn reference_selection_checks_local_uniqueness_and_unrelated_receivers() {
    for mut r in models(
        "package A { feature constant = 4;
            class Base { feature n = 4; }
            class Root; class Local specializes Root { feature n = 4; feature other redefines Local::n = 6;
                feature header[n]; feature body { multiplicity [n]; }
            }
            class Formula { feature n = 3; feature sum = n + 1;
                feature header[sum]; feature body { multiplicity [sum]; }
            }
        }",
        "package B { class Other {
            feature header[A::Base::n]; feature body { multiplicity [A::Base::n]; }
            feature constant[A::constant];
        } }",
    ) {
        let original = r.resolve_qualified("A::Local::n").unwrap();
        let other = r.resolve_qualified("A::Local::other").unwrap();
        assert_eq!(r.redefinition_targets(other), vec![original]);
        for name in [
            "A::Local::header",
            "A::Local::body",
            "B::Other::header",
            "B::Other::body",
        ] {
            bounds(&mut r, name, None);
        }
        for name in [
            "A::Formula::header",
            "A::Formula::body",
            "B::Other::constant",
        ] {
            bounds(&mut r, name, Some((4, Some(4))));
        }
    }
}

#[test]
fn complete_imported_candidate_providers_are_admitted_but_missing_and_filtered_are_unknown() {
    for mut r in models(
        "package A { package Source { feature extra = 7; }
            class Missing { public import absent::*; feature n = 4;
                feature slots { multiplicity [n]; }
            }
            class Imported { public import Source::*; feature n = 4;
                feature slots { multiplicity [n]; }
            }
            class Filtered { filter true; feature n = 4;
                feature slots { multiplicity [n]; }
            }
        }",
        "package B {
            class Child specializes A::Missing { feature other redefines n = 6; feature redefines slots; }
            class Known specializes A::Imported { feature other redefines n = 6; feature redefines slots; }
        }",
    ) {
        bounds(&mut r, "A::Imported::slots", Some((4, Some(4))));
        bounds(&mut r, "B::Known::slots", Some((6, Some(6))));
        for name in ["A::Missing::slots", "B::Child::slots", "A::Filtered::slots"] {
            bounds(&mut r, name, None);
        }
    }
}

#[test]
fn complete_provider_proofs_preserve_imported_feature_membership_and_visibility() {
    for mut r in models(
        "package A {
            class Base { feature n default = 4; feature formula = n + 1;
                feature slots { multiplicity [formula]; }
            }
            class Provider specializes Base { feature other redefines n = 8; }
            class Public specializes Base { public import Provider::*; feature redefines slots; }
            class Protected specializes Base { protected import Provider::*; feature redefines slots; }
            class Private specializes Base { private import Provider::*; feature redefines slots; }
            class OtherProvider specializes Base { feature rival redefines n = 10; }
            class Both specializes Base { public import Provider::*; public import OtherProvider::*; }
            class Member specializes Base { public import Provider::other; }
            class Alias specializes Base { alias selected for Provider::other; }
            class SharedLeft specializes Base { public import Provider::other; }
            class SharedRight specializes Base { public import Provider::other; }
        }",
        "package B {
            class PublicChild specializes A::Public { feature redefines slots; }
            class ProtectedChild specializes A::Protected { feature redefines slots; }
            class PrivateChild specializes A::Private { feature redefines slots; }
            class BothChild specializes A::Both { feature redefines slots; }
            class MemberChild specializes A::Member { feature redefines slots; }
            class AliasChild specializes A::Alias { feature redefines slots; }
            class Diamond specializes A::SharedLeft, A::SharedRight { feature redefines slots; }
        }",
    ) {
        for _ in 0..2 {
            bounds(&mut r, "A::Public::slots", Some((5, Some(5))));
            bounds(&mut r, "B::PublicChild::slots", Some((9, Some(9))));
            bounds(&mut r, "B::ProtectedChild::slots", Some((9, Some(9))));
            bounds(&mut r, "B::PrivateChild::slots", Some((5, Some(5))));
            bounds(&mut r, "B::BothChild::slots", None);
            bounds(&mut r, "B::MemberChild::slots", Some((9, Some(9))));
            bounds(&mut r, "B::AliasChild::slots", None);
            bounds(&mut r, "B::Diamond::slots", Some((9, Some(9))));
        }
    }
}

#[test]
fn provider_proof_rejects_transitive_gaps_but_exact_member_imports_remain_local() {
    for mut r in models(
        "package A {
            package Good { feature extra = 7; }
            package Bad { public import absent::*; feature extra = 7; }
            package Transitive { public import Bad::*; }
            package CycleA { public import CycleB::*; }
            package CycleB { public import CycleA::*; }
            class Base { feature n = 4; feature slots { multiplicity [n]; } }
        }",
        "package B {
            class Known specializes A::Base { public import A::Good::*; feature redefines slots; }
            class Exact specializes A::Base { public import A::Bad::extra; feature redefines slots; }
            class Alias specializes A::Base { alias selected for A::Bad::extra; feature redefines slots; }
            class Missing specializes A::Base { public import absent::*; feature redefines slots; }
            class Transitive specializes A::Base { public import A::Transitive::*; feature redefines slots; }
            class Recursive specializes A::Base { public import A::Good::*::**; feature redefines slots; }
            class Cycle specializes A::Base { public import A::CycleA::*; feature redefines slots; }
            class MissingMember specializes A::Base { public import A::Good::absent; feature redefines slots; }
            class MissingAlias specializes A::Base { alias selected for A::Good::absent; feature redefines slots; }
            feature recovered = if size(Missing::slots) == 4 and false ? 0
                else size(Known::slots) + size(Exact::slots);
        }",
    ) {
        for _ in 0..2 {
            for name in ["Missing", "Transitive", "Recursive", "Cycle", "MissingMember", "MissingAlias"] {
                bounds(&mut r, &format!("B::{name}::slots"), None);
            }
            for name in ["Known", "Exact", "Alias"] {
                bounds(&mut r, &format!("B::{name}::slots"), Some((4, Some(4))));
            }
            let recovered = r.resolve_qualified("B::recovered").unwrap();
            assert_eq!(r.evaluate(recovered), Ok(Value::Integer(8)));
        }
    }
}

#[test]
fn lexical_resolution_stays_separate_from_receiver_provider_completeness() {
    for (imports, expected) in [
        ("public import Good::*;", Some((5, Some(5)))),
        (
            "public import Good::*; public import absent::*;",
            Some((5, Some(5))),
        ),
        ("public import Good::*; public import Other::*;", None),
    ] {
        let library = format!(
            "package A {{ package Good {{ feature n = 4; }}
            package Other {{ feature n = 6; }}
            package Formulas {{ {imports} feature count = n + 1;
                class Base {{ feature slots {{ multiplicity [count]; }} }}
            }}
        }}"
        );
        for mut r in models(
            &library,
            "package B { class Child specializes A::Formulas::Base { feature redefines slots; } }",
        ) {
            bounds(&mut r, "B::Child::slots", expected);
        }
    }
}
