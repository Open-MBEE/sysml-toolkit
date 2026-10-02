//! Evaluation reports retain causes hidden by inherited-default fallback.
#![cfg(feature = "json")]

use std::{collections::HashMap, sync::Arc};
use sysmlv2_parser::{
    eval::{EvalError, Value},
    json::ResolvedModel,
    libcache::LibraryCache,
    model::Model,
    prepared::PreparedLibrary,
};

fn models(library: &str, user: &str) -> Vec<(Model, ResolvedModel)> {
    models_with_users(library, &[("receivers.kerml", user)])
}

fn models_with_users(library: &str, users: &[(&str, &str)]) -> Vec<(Model, ResolvedModel)> {
    let mut base = Model::new();
    let unit = base.add_library_source("defaults.kerml", library);
    assert!(unit.diagnostics.is_empty(), "{:?}", unit.diagnostics);
    base.record_library_cache();
    ResolvedModel::build(&base);
    let cache =
        LibraryCache::from_bytes(&base.take_recorded_library_cache().unwrap().to_bytes()).unwrap();
    let prepared = base.prepare_library().unwrap();
    let decoded =
        Arc::new(PreparedLibrary::from_bytes(&prepared.to_bytes(37).unwrap(), 37).unwrap());
    (0..4)
        .map(|mode| {
            let mut model = Model::new();
            match mode {
                2 => Arc::clone(&prepared).install(&mut model).unwrap(),
                3 => Arc::clone(&decoded).install(&mut model).unwrap(),
                _ => {
                    model.add_library_source("defaults.kerml", library);
                    if mode == 1 {
                        model.set_library_cache(cache.clone());
                    }
                }
            }
            for &(name, source) in users {
                let unit = model.add_source(name, source);
                assert!(unit.diagnostics.is_empty(), "{:?}", unit.diagnostics);
            }
            assert!(!model.has_errors());
            let resolved = ResolvedModel::build(&model);
            (model, resolved)
        })
        .collect()
}

fn same_error_kind(actual: &EvalError, expected: &EvalError) {
    assert_eq!(
        std::mem::discriminant(actual),
        std::mem::discriminant(expected),
        "{actual:?} versus {expected:?}"
    );
}

#[test]
fn inherited_errors_preserve_causes_and_provider_locations_in_every_representation() {
    let library = "package A { class Base {
        feature absent default = missing;
        feature zero default = 1/0;
        feature badType default = true+1;
        feature unsupported default = ~1;
        feature budget default = 1..1000001;
    } }";
    let user = "package B { class Child specializes A::Base {
        feature redefines absent; feature redefines zero; feature redefines badType;
        feature redefines unsupported; feature redefines budget;
    } }";
    for (model, mut r) in models(library, user) {
        let loaded = model.loaded_library_unit_count();
        let owner = r.resolve_qualified("B::Child").unwrap();
        let receiver = r.element_scope(owner).unwrap();
        for name in ["absent", "zero", "badType", "unsupported", "budget"] {
            let origin = r.resolve_qualified(&format!("A::Base::{name}")).unwrap();
            let requested = r.resolve_qualified(&format!("B::Child::{name}")).unwrap();
            let source_span = r.value_expr(origin).unwrap().1.span;
            let direct = r.evaluate_report(origin);
            assert!(!direct.diagnostics_truncated);
            let expected = direct.result.unwrap_err();
            assert!(direct.inherited_default_failures.is_empty());
            let legacy = r.evaluate(requested);
            for _ in 0..2 {
                let report = r.evaluate_report(requested);
                assert!(!report.diagnostics_truncated);
                assert_eq!(report.result, legacy, "{name}");
                assert_eq!(report.inherited_default_failures.len(), 1, "{name}");
                let failure = &report.inherited_default_failures[0];
                assert_eq!(failure.requested, requested);
                assert_eq!(failure.origin, origin);
                assert_eq!(failure.receiver, receiver);
                assert_eq!(failure.source_unit, 0);
                assert_eq!(failure.source_span, source_span);
                assert_eq!(failure.error, expected);
                let terminal = failure.dependency_path.last().unwrap();
                assert_eq!(terminal.requested, requested);
                assert_eq!(terminal.origin, origin);
                assert_eq!(terminal.receiver, receiver);
            }
        }
        assert_eq!(model.loaded_library_unit_count(), loaded);
    }
}

#[test]
fn inherited_recursion_reports_cycle_without_changing_the_fallback() {
    for (model, mut r) in models(
        "package A { class Base { feature loop default = loop; } }",
        "package B { class Child specializes A::Base { feature redefines loop; } }",
    ) {
        let loaded = model.loaded_library_unit_count();
        let origin = r.resolve_qualified("A::Base::loop").unwrap();
        let requested = r.resolve_qualified("B::Child::loop").unwrap();
        let legacy = r.evaluate(requested);
        let report = r.evaluate_report(requested);
        assert!(!report.diagnostics_truncated);
        assert_eq!(report.result, legacy);
        assert!(!report.inherited_default_failures.is_empty());
        assert!(report.inherited_default_failures.iter().any(|failure| {
            failure.requested == requested
                && failure.origin == origin
                && matches!(failure.error, EvalError::Cycle(_))
        }));
        assert_eq!(model.loaded_library_unit_count(), loaded);
    }
}

#[test]
fn nested_fallback_remains_visible_when_the_result_is_concrete() {
    for (model, mut r) in models(
        "package A { class Base { feature inner[0] default = 1/0;
            feature outer default = size(inner);
        } }",
        "package B { class Child specializes A::Base {
            feature redefines inner; feature redefines outer;
            feature masked = size(inner);
        } }",
    ) {
        let loaded = model.loaded_library_unit_count();
        let inner = r.resolve_qualified("B::Child::inner").unwrap();
        let origin = r.resolve_qualified("A::Base::inner").unwrap();
        for name in ["outer", "masked"] {
            let outer = r.resolve_qualified(&format!("B::Child::{name}")).unwrap();
            let legacy = r.evaluate(outer);
            let report = r.evaluate_report(outer);
            assert!(!report.diagnostics_truncated);
            assert_eq!(report.result, legacy);
            assert_eq!(report.result, Ok(Value::Integer(0)));
            assert_eq!(report.inherited_default_failures.len(), 1);
            let failure = &report.inherited_default_failures[0];
            assert_eq!(failure.requested, inner);
            assert_eq!(failure.origin, origin);
            assert_eq!(failure.error, EvalError::DivisionByZero);
            assert!(failure.dependency_path.iter().any(|d| d.requested == outer));
            assert_eq!(failure.dependency_path.last().unwrap().requested, inner);
            let rejected = report.into_checked_result().unwrap_err();
            assert_eq!(rejected.result, Ok(Value::Integer(0)));
            assert_eq!(rejected.inherited_default_failures.len(), 1);
        }
        let masked = r.resolve_qualified("B::Child::masked").unwrap();
        let (scope, expr) = r.value_expr(masked).unwrap();
        let legacy = r.evaluate_in(scope, &expr);
        let report = r.evaluate_in_report(scope, &expr);
        assert!(!report.diagnostics_truncated);
        assert_eq!(report.result, legacy);
        assert_eq!(report.inherited_default_failures.len(), 1);
        assert_eq!(report.inherited_default_failures[0].requested, inner);
        assert_eq!(model.loaded_library_unit_count(), loaded);
    }
}

#[test]
fn ordinary_unknowns_successful_defaults_and_unvisited_branches_are_not_failures() {
    for (model, mut r) in models(
        "package A { class Base { feature empty; feature fixed = 7;
            feature good default = 4; feature broken default = 1/0;
        } }",
        "package B { class Child specializes A::Base {
            feature redefines empty; feature redefines fixed; feature redefines good;
            feature override redefines A::Base::broken = 9;
            feature redefines broken;
            feature dead = if true ? 3 else broken;
        } }",
    ) {
        let loaded = model.loaded_library_unit_count();
        let broken = r.resolve_qualified("B::Child::broken").unwrap();
        assert!(
            !r.evaluate_report(broken)
                .inherited_default_failures
                .is_empty()
        );
        for (name, expected) in [
            ("empty", None),
            ("fixed", None),
            ("good", Some(Value::Integer(4))),
            ("override", Some(Value::Integer(9))),
            ("dead", Some(Value::Integer(3))),
        ] {
            let e = r.resolve_qualified(&format!("B::Child::{name}")).unwrap();
            let legacy = r.evaluate(e);
            let report = r.evaluate_report(e);
            assert!(!report.diagnostics_truncated);
            assert_eq!(report.result, legacy);
            if let Some(expected) = expected {
                assert_eq!(report.result, Ok(expected));
            }
            assert!(report.inherited_default_failures.is_empty(), "{name}");
            let checked = report.into_checked_result().unwrap();
            if matches!(name, "empty" | "fixed") {
                assert!(matches!(checked, Value::Unbound(_)));
            }
        }
        assert_eq!(model.loaded_library_unit_count(), loaded);
    }
}

#[test]
fn separate_receivers_and_terminal_errors_keep_their_own_failure_context() {
    for (model, mut r) in models(
        "package A { class Base { feature broken[0] default = 1/0; } }",
        "package B {
            class Left specializes A::Base { feature redefines broken; }
            class Right specializes A::Base { feature redefines broken; }
            feature answer = (Left::broken, Right::broken, 1/0);
        }",
    ) {
        let loaded = model.loaded_library_unit_count();
        let answer = r.resolve_qualified("B::answer").unwrap();
        let legacy = r.evaluate(answer);
        let report = r.evaluate_report(answer);
        assert!(!report.diagnostics_truncated);
        assert_eq!(report.result, legacy);
        same_error_kind(&report.result.unwrap_err(), &EvalError::DivisionByZero);
        assert_eq!(report.inherited_default_failures.len(), 2);
        for (failure, name) in report
            .inherited_default_failures
            .iter()
            .zip(["Left", "Right"])
        {
            let owner = r.resolve_qualified(&format!("B::{name}")).unwrap();
            let feature = r.resolve_qualified(&format!("B::{name}::broken")).unwrap();
            assert_eq!(failure.requested, feature);
            assert_eq!(failure.receiver, r.element_scope(owner).unwrap());
            assert_eq!(failure.error, EvalError::DivisionByZero);
        }
        assert_eq!(model.loaded_library_unit_count(), loaded);
    }
}

#[test]
fn unknown_receiver_default_is_not_an_attempted_failure() {
    let mut model = Model::new();
    let unit = model.add_source(
        "receiver.sysml",
        "part def Base { attribute broken default = 1/0; }
        part def Child :> Base { attribute :>> broken; }
        requirement def R { subject unit : Child[1]; }
        attribute answer = R::unit.broken;",
    );
    assert!(unit.diagnostics.is_empty(), "{:?}", unit.diagnostics);
    let mut r = ResolvedModel::build(&model);
    let answer = r.resolve_qualified("answer").unwrap();
    let legacy = r.evaluate(answer);
    let report = r.evaluate_report(answer);
    assert!(!report.diagnostics_truncated);
    assert_eq!(report.result, legacy);
    assert_eq!(report.result, Ok(Value::Indeterminate));
    assert!(report.inherited_default_failures.is_empty());
}

#[test]
fn inherited_id_bound_defaults_report_the_authored_provider_not_the_reference_target() {
    const ID: &str = "99999999-9999-4999-8999-999999999999";
    for foreign_zero in [true, false] {
        let foreign = if foreign_zero { 0 } else { 1 };
        let ordinary = if foreign_zero { 1 } else { 0 };
        let library = format!("package Support {{ feature denominator = {foreign}; }}");
        let a = format!(
            "package A {{ class Base {{ feature '{ID}' = {ordinary}; feature v default = 1/'{ID}'; }} }}"
        );
        let b = a.replacen("package A", "package B", 1);
        let receivers = "package C {
            class Left specializes A::Base { feature redefines v; }
            class Right specializes B::Base { feature redefines v; }
        }";
        for (mode, (model, mut r)) in models_with_users(
            &library,
            &[
                ("a.kerml", &a),
                ("b.kerml", &b),
                ("receivers.kerml", receivers),
            ],
        )
        .into_iter()
        .enumerate()
        {
            let loaded = model.loaded_library_unit_count();
            let foreign = r.resolve_qualified("Support::denominator").unwrap();
            let ordinary_a = r.resolve_qualified(&format!("A::Base::'{ID}'")).unwrap();
            let sites = r.references_to(ordinary_a);
            assert_eq!(sites.len(), 1);
            assert_eq!(sites[0].unit, 1);
            let mut hints = HashMap::from([(
                (r.element_id(sites[0].owner), sites[0].kind.clone()),
                ID.parse().unwrap(),
            )]);
            r.override_ids(&HashMap::from([(
                r.element_id(foreign),
                ID.parse().unwrap(),
            )]));
            assert!(
                r.bind_id_spelled_references_with(&mut hints)
                    .contains(&ID.parse().unwrap())
            );
            let a_origin = r.resolve_qualified("A::Base::v").unwrap();
            let b_origin = r.resolve_qualified("B::Base::v").unwrap();
            // Equal expression spans make a wrong source origin choose a real,
            // differently bound reference instead of merely failing lookup.
            let a_span = r.value_expr(a_origin).unwrap().1.span;
            let b_span = r.value_expr(b_origin).unwrap().1.span;
            assert_eq!(a_span, b_span);
            for _ in 0..2 {
                for (side, origin, unit, fails) in [
                    ("Left", a_origin, 1, foreign_zero),
                    ("Right", b_origin, 2, !foreign_zero),
                ] {
                    let owner = r.resolve_qualified(&format!("C::{side}")).unwrap();
                    let requested = r.resolve_qualified(&format!("C::{side}::v")).unwrap();
                    let receiver = r.element_scope(owner).unwrap();
                    let legacy = r.evaluate(requested);
                    let report = r.evaluate_report(requested);
                    assert!(!report.diagnostics_truncated);
                    assert_eq!(report.result, legacy, "mode={mode} {side}");
                    assert_eq!(report.inherited_default_failures.len(), usize::from(fails));
                    if fails {
                        assert!(matches!(report.result, Ok(Value::Unbound(_))));
                        let failure = &report.inherited_default_failures[0];
                        assert_eq!(failure.requested, requested);
                        assert_eq!(failure.origin, origin);
                        assert_eq!(failure.receiver, receiver);
                        assert_eq!(failure.source_unit, unit);
                        assert_eq!(failure.source_span, a_span);
                        assert_eq!(failure.error, EvalError::DivisionByZero);
                        let terminal = failure.dependency_path.last().unwrap();
                        assert_eq!(terminal.requested, requested);
                        assert_eq!(terminal.origin, origin);
                        assert_eq!(terminal.receiver, receiver);
                        assert!(report.into_checked_result().is_err());
                    } else {
                        assert_eq!(report.into_checked_result().unwrap(), Value::Integer(1));
                    }
                    // Error provenance belongs to the provider expression in
                    // unit 1/2, never the foreign denominator in library unit 0
                    // or the receiving redefinition in user unit 3.
                    let direct = r.evaluate_report(origin);
                    assert!(!direct.diagnostics_truncated);
                    assert!(direct.inherited_default_failures.is_empty());
                    assert_eq!(direct.result, r.evaluate(origin));
                    if fails {
                        assert_eq!(direct.result, Err(EvalError::DivisionByZero));
                    }
                }
            }
            assert_eq!(model.loaded_library_unit_count(), loaded);
            if mode == 3 {
                assert_eq!(loaded, 0);
            }
        }
    }
}

#[test]
fn exhausted_reporting_capacity_preserves_the_legacy_value_and_rejects_checked_conversion() {
    let reads = std::iter::repeat_n("Child::broken", 300)
        .collect::<Vec<_>>()
        .join(",");
    let user = format!(
        "package B {{ class Child specializes A::Base {{ feature redefines broken; }}
         feature answer = ({reads}); }}"
    );
    for (mode, (model, mut r)) in models(
        "package A { class Base { feature broken[0] default = 1/0; } }",
        &user,
    )
    .into_iter()
    .enumerate()
    {
        let loaded = model.loaded_library_unit_count();
        let answer = r.resolve_qualified("B::answer").unwrap();
        let requested = r.resolve_qualified("B::Child::broken").unwrap();
        let origin = r.resolve_qualified("A::Base::broken").unwrap();
        let legacy = r.evaluate(answer);
        assert_eq!(legacy, Ok(Value::Sequence(Vec::new())));
        for _ in 0..2 {
            let report = r.evaluate_report(answer);
            assert_eq!(report.result, legacy, "mode={mode}");
            assert!(report.diagnostics_truncated);
            assert_eq!(report.inherited_default_failures.len(), 256);
            for failure in &report.inherited_default_failures {
                assert_eq!(failure.requested, requested);
                assert_eq!(failure.origin, origin);
                assert_eq!(failure.error, EvalError::DivisionByZero);
                assert_eq!(failure.dependency_path.first().unwrap().requested, answer);
                assert_eq!(failure.dependency_path.last().unwrap().requested, requested);
            }
            let rejected = report.into_checked_result().unwrap_err();
            assert_eq!(rejected.result, legacy);
            assert!(rejected.diagnostics_truncated);
        }
        let direct = r.evaluate_report(origin);
        assert_eq!(direct.result, Err(EvalError::DivisionByZero));
        assert!(direct.inherited_default_failures.is_empty());
        assert!(!direct.diagnostics_truncated);
        assert_eq!(model.loaded_library_unit_count(), loaded);
        if mode == 3 {
            assert_eq!(loaded, 0);
        }
    }
}

#[test]
fn warmed_unit_reductions_cannot_hide_failed_inherited_conversion_defaults() {
    for (expression, cycle) in [("1/0", false), ("conversionFactor", true)] {
        let library = format!(
            "package A {{ class C {{ feature conversionFactor default = {expression}; }}
             feature s; }}"
        );
        let user = "package B {
            feature unit {
                feature unitConversion : A::C {
                    feature referenceUnit = A::s;
                    feature redefines conversionFactor;
                }
            }
            feature answer = 1[unit];
        }";
        for (mode, (model, _)) in models(&library, user).into_iter().enumerate() {
            let loaded = model.loaded_library_unit_count();
            for legacy_first in [true, false] {
                let mut r = ResolvedModel::build(&model);
                let answer = r.resolve_qualified("B::answer").unwrap();
                let requested = r
                    .resolve_qualified("B::unit::unitConversion::conversionFactor")
                    .unwrap();
                let origin = r.resolve_qualified("A::C::conversionFactor").unwrap();
                let source_span = r.value_expr(origin).unwrap().1.span;
                let (scope, expr) = r.value_expr(answer).unwrap();
                let mut legacy = legacy_first.then(|| r.evaluate_in(scope, &expr));
                for _ in 0..3 {
                    let report = r.evaluate_in_report(scope, &expr);
                    assert!(!report.diagnostics_truncated);
                    assert!(matches!(report.result, Ok(Value::Quantity(..))));
                    if let Some(expected) = &legacy {
                        assert_eq!(&report.result, expected);
                    }
                    assert_eq!(
                        report.inherited_default_failures.len(),
                        1,
                        "mode={mode} cycle={cycle} legacy_first={legacy_first}"
                    );
                    let failure = &report.inherited_default_failures[0];
                    assert_eq!(failure.requested, requested);
                    assert_eq!(failure.origin, origin);
                    assert_eq!(failure.source_unit, 0);
                    assert_eq!(failure.source_span, source_span);
                    if cycle {
                        assert!(matches!(failure.error, EvalError::Cycle(_)));
                    } else {
                        assert_eq!(failure.error, EvalError::DivisionByZero);
                    }
                    let result = report.result.clone();
                    assert!(report.into_checked_result().is_err());
                    legacy = Some(r.evaluate_in(scope, &expr));
                    assert_eq!(legacy.as_ref().unwrap(), &result);
                }
            }
            assert_eq!(model.loaded_library_unit_count(), loaded);
            if mode == 3 {
                assert_eq!(loaded, 0);
            }
        }
    }
}
