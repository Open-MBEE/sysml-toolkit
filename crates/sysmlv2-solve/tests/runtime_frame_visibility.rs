//! Runtime frame visibility cannot reactivate through a declaration read.
use std::{collections::HashMap, sync::Arc};
use sysmlv2_model::{
    check::ConstraintVerdict, json::ResolvedModel, libcache::LibraryCache, model::Model,
    prepared::PreparedLibrary,
};
use sysmlv2_solve::{
    PropagateOutcome, SolveOutcome, SolverConfig, propagate_constraints_with,
    solve_constraints_with, z3_version,
};
const ID: &str = "88888888-8888-4888-8888-888888888888";
fn native_solve(
    r: &mut ResolvedModel,
    model: &Model,
    cfg: &SolverConfig,
) -> Vec<sysmlv2_solve::SolvedConstraint> {
    if z3_version(cfg).is_err() {
        return Vec::new();
    }
    solve_constraints_with(r, model, cfg).unwrap()
}
fn models(source: &str) -> Vec<Model> {
    let lib = "package ScalarValues { datatype Integer; }";
    let mut base = Model::new();
    base.add_library_source("lib.kerml", lib);
    base.record_library_cache();
    ResolvedModel::build(&base);
    let cache =
        LibraryCache::from_bytes(&base.take_recorded_library_cache().unwrap().to_bytes()).unwrap();
    let prepared = base.prepare_library().unwrap();
    let decoded =
        Arc::new(PreparedLibrary::from_bytes(&prepared.to_bytes(43).unwrap(), 43).unwrap());
    (0..4)
        .map(|mode| {
            let mut m = Model::new();
            match mode {
                2 => Arc::clone(&prepared).install(&mut m).unwrap(),
                3 => Arc::clone(&decoded).install(&mut m).unwrap(),
                _ => {
                    m.add_library_source("lib.kerml", lib);
                    if mode == 1 {
                        m.set_library_cache(cache.clone());
                    }
                }
            }
            for pkg in ["A", "B"] {
                m.add_source(
                    format!("{pkg}.sysml"),
                    &format!("package {pkg} {{ attribute x[1]:ScalarValues::Integer; {source} }}"),
                );
            }
            assert!(!m.has_errors());
            m
        })
        .collect()
}

fn assert_solver_truth(r: &mut ResolvedModel, model: &Model, satisfiable: bool, label: &str) {
    let propagated = propagate_constraints_with(r, model, &Default::default());
    assert_eq!(propagated.constraints.len(), 2, "{label}");
    for c in propagated.constraints {
        if satisfiable {
            assert_eq!(
                c.propagate,
                Some(PropagateOutcome::Satisfied),
                "{label}: {c:?}"
            );
        } else {
            assert!(
                matches!(
                    c.propagate,
                    Some(PropagateOutcome::Unsatisfiable | PropagateOutcome::Violated)
                ),
                "{label}: {c:?}"
            );
        }
    }
    for c in native_solve(r, model, &Default::default()) {
        if satisfiable {
            assert!(
                matches!(
                    c.solve,
                    Some(SolveOutcome::Satisfiable(_) | SolveOutcome::Valid)
                ) || c.verdict == ConstraintVerdict::Satisfied,
                "{label}: {c:?}"
            );
        } else {
            assert!(
                c.solve == Some(SolveOutcome::Unsatisfiable)
                    || c.verdict == ConstraintVerdict::Violated,
                "{label}: {c:?}"
            );
        }
    }
}

fn check_transitive_case(label: &str, declarations: &str, expected: i128, wrong: i128) {
    for asserted in [expected, wrong] {
        let source = format!(
            "{declarations} attribute direct=Base(7); assert constraint c {{Base(x)=={asserted} & x==7}}"
        );
        for (mode, model) in models(&source).into_iter().enumerate() {
            let mut r = ResolvedModel::build(&model);
            for _ in 0..2 {
                for pkg in ["B", "A"] {
                    let value = r.resolve_qualified(&format!("{pkg}::direct")).unwrap();
                    assert_eq!(
                        r.evaluate(value),
                        Ok(sysmlv2_model::eval::Value::Integer(expected)),
                        "{label} mode={mode} {pkg}"
                    );
                }
                assert_solver_truth(
                    &mut r,
                    &model,
                    asserted == expected,
                    &format!("{label} mode={mode}"),
                );
            }
            if mode == 3 {
                assert_eq!(model.loaded_library_unit_count(), 0);
            }
        }
    }
}

#[test]
fn transitive_unrelated_calculation() {
    check_transitive_case(
        "unrelated calculation",
        "calc def G { Base::p } calc def Base { in q default 1; attribute p=q; G() }",
        1,
        7,
    );
}

#[test]
fn transitive_package_bridge() {
    check_transitive_case(
        "package bridge",
        "package P { attribute bridge=Base::p; } calc def Base { in q default 1; attribute p=q; P::bridge }",
        1,
        7,
    );
}

#[test]
fn transitive_two_unrelated_calculations() {
    check_transitive_case(
        "two unrelated calculations",
        "calc def H { Base::p } calc def G { H() } calc def Base { in q default 1; attribute p=q; G() }",
        1,
        7,
    );
}

#[test]
fn transitive_restore_after_calculation() {
    check_transitive_case(
        "restore after calculation",
        "calc def G { Base::p } calc def Base { in q default 1; attribute p=q; G()+p }",
        8,
        14,
    );
}

#[test]
fn transitive_restore_after_package() {
    check_transitive_case(
        "restore after package",
        "package P { attribute bridge=Base::p; } calc def Base { in q default 1; attribute p=q; P::bridge+p }",
        8,
        14,
    );
}

#[test]
fn transitive_nested_lexical_capture() {
    check_transitive_case(
        "nested lexical capture",
        "calc def Base { in q default 1; attribute p=q; calc def G { Base::p } G() }",
        7,
        1,
    );
}

#[test]
fn transitive_forward_actual_before_masking() {
    check_transitive_case(
        "forward actual before masking",
        "calc def G { in explicitArg; explicitArg } calc def Base { in q default 1; attribute p=q; G(p) }",
        7,
        1,
    );
}

#[test]
fn transitive_forward_actual_plus_hidden_read() {
    check_transitive_case(
        "forward actual plus hidden read",
        "calc def G { in explicitArg; explicitArg+Base::p } calc def Base { in q default 1; attribute p=q; G(p) }",
        8,
        14,
    );
}

#[test]
fn a_fresh_recursive_activation_gets_its_own_visible_arguments() {
    // The evaluator supports bounded recursive execution. Symbolic recursion
    // remains outside the solver fragment, so this is an evaluator control.
    let source = "calc def G { Base(3) } calc def Base { in q default 1; attribute p=q; if q==7 ? G()+p else p } attribute direct=Base(7);";
    for (mode, model) in models(source).into_iter().enumerate() {
        let mut r = ResolvedModel::build(&model);
        for _ in 0..2 {
            for pkg in ["B", "A"] {
                let value = r.resolve_qualified(&format!("{pkg}::direct")).unwrap();
                assert_eq!(
                    r.evaluate(value),
                    Ok(sysmlv2_model::eval::Value::Integer(10)),
                    "mode={mode} {pkg}"
                );
            }
        }
        if mode == 3 {
            assert_eq!(model.loaded_library_unit_count(), 0);
        }
    }
}

#[test]
fn lowered_lambda_default_reads_cannot_reactivate_hidden_parameter_bindings() {
    let source = format!(
        "calc def G {{ '{ID}' }} attribute direct=(7,9)->reduce {{ in q default 1; in p default q; G() }};"
    );
    for (mode, model) in models(&source).into_iter().enumerate() {
        let mut r = ResolvedModel::build(&model);
        // Bind the reference by exact identity rather than an invented name for
        // the anonymous expression. Both source sites intentionally target A.
        let direct = r.resolve_qualified("A::direct").unwrap();
        let candidates: Vec<_> = r
            .elements()
            .filter(|&element| {
                r.element_properties(element)
                    .get("declaredName")
                    .and_then(|v| v.as_str())
                    == Some("p")
            })
            .collect();
        let parameter = candidates
            .into_iter()
            .find(|&element| {
                let mut owner = r.owner(element);
                while let Some(at) = owner {
                    if at == direct {
                        return true;
                    }
                    owner = r.owner(at);
                }
                false
            })
            .unwrap();
        r.override_ids(&HashMap::from([(
            r.element_id(parameter),
            ID.parse().unwrap(),
        )]));
        assert!(
            r.bind_id_spelled_references()
                .contains(&ID.parse().unwrap())
        );
        for _ in 0..2 {
            for pkg in ["B", "A"] {
                let value = r.resolve_qualified(&format!("{pkg}::direct")).unwrap();
                assert_eq!(
                    r.evaluate(value),
                    Ok(sysmlv2_model::eval::Value::Integer(1)),
                    "mode={mode} {pkg}"
                );
            }
        }
        if mode == 3 {
            assert_eq!(model.loaded_library_unit_count(), 0);
        }
    }
}

#[test]
fn query_lambda_bindings_restore_and_do_not_enter_unrelated_model_formulas() {
    use sysmlv2_syntax::parser::parse_expression;
    let source = "calc def Base {in q default 1; attribute p=q; p} calc def G {Base::p}";
    for (mode, model) in models(source).into_iter().enumerate() {
        let mut r = ResolvedModel::build(&model);
        for _ in 0..2 {
            for (expression, expected) in [
                ("(7,9)->reduce { in q; in p; A::G() }", 1),
                ("(7,9)->reduce { in q; in p; A::G()+q+p }", 17),
                ("(7,9)->reduce { in q; in p; A::Base(q)+p }", 16),
                (
                    "(7,9)->reduce { in q; in p; (1,2)->reduce { in a; in b; q+p+a+b } }",
                    19,
                ),
            ] {
                let parsed = parse_expression(expression);
                assert!(
                    parsed.diagnostics.is_empty(),
                    "{expression}: {:?}",
                    parsed.diagnostics
                );
                let root = r.root_scope();
                assert_eq!(
                    r.query(root, &parsed.expr.unwrap()),
                    Ok(sysmlv2_model::eval::Value::Integer(expected)),
                    "mode={mode} {expression}"
                );
            }
        }
        if mode == 3 {
            assert_eq!(model.loaded_library_unit_count(), 0);
        }
    }
}

#[test]
fn lowered_quantifiers_preserve_lexical_capture_without_reactivating_hidden_frames() {
    for body in [
        "(1,2)->forAll {in memberValue; G()==1}",
        "(1,2)->forAll {in memberValue; G()==1 & q==7 & memberValue>0}",
    ] {
        for asserted in [true, false] {
            let source = format!(
                "calc def G {{Base::p}} calc def Base {{in q default 1; attribute p=q; {body}}} attribute direct=Base(7); assert constraint c {{Base(x)=={asserted} & x==7}}"
            );
            for (mode, model) in models(&source).into_iter().enumerate() {
                let mut r = ResolvedModel::build(&model);
                for _ in 0..2 {
                    for pkg in ["B", "A"] {
                        let value = r.resolve_qualified(&format!("{pkg}::direct")).unwrap();
                        assert_eq!(
                            r.evaluate(value),
                            Ok(sysmlv2_model::eval::Value::Boolean(true)),
                            "mode={mode} body={body} {pkg}"
                        );
                    }
                    assert_solver_truth(
                        &mut r,
                        &model,
                        asserted,
                        &format!("mode={mode} body={body}"),
                    );
                }
                if mode == 3 {
                    assert_eq!(model.loaded_library_unit_count(), 0);
                }
            }
        }
    }
}

#[test]
fn inherited_signature_actual_stays_visible_in_the_specializing_calculation() {
    check_transitive_case(
        "inherited signature actual",
        "calc def Ancestor {in q default 1; attribute p=q;} calc def Base :> Ancestor {p}",
        7,
        1,
    );
}

#[test]
fn inherited_signature_actual_stays_hidden_after_an_unrelated_bridge() {
    check_transitive_case(
        "inherited signature bridge and restore",
        "calc def Ancestor {in q default 1; attribute p=q;} calc def G {Ancestor::p} calc def Base :> Ancestor {G()+p}",
        8,
        14,
    );
}

#[test]
fn inherited_omitted_parameter_default_retains_the_active_signature_context() {
    for body in ["Base::p", "sum(Base::p)"] {
        for asserted in [7, 2] {
            let source = format!(
                "calc def Base {{in p default 1;}}
                 calc def Child :>Base {{in q :>>Base::p default r; in r default 1;}}
                 calc def Grand :>Child {{{body}}}
                 attribute direct=Grand(r=7);
                 assert constraint c {{Grand(r=x)=={asserted} & x==7}}"
            );
            for (mode, model) in models(&source).into_iter().enumerate() {
                let mut r = ResolvedModel::build(&model);
                for _ in 0..2 {
                    for pkg in ["B", "A"] {
                        let value = r.resolve_qualified(&format!("{pkg}::direct")).unwrap();
                        assert_eq!(
                            r.evaluate(value),
                            Ok(sysmlv2_model::eval::Value::Integer(7)),
                            "mode={mode} body={body} {pkg}"
                        );
                    }
                    assert_solver_truth(
                        &mut r,
                        &model,
                        asserted == 7,
                        &format!("inherited omitted default mode={mode} body={body}"),
                    );
                }
                if mode == 3 {
                    assert_eq!(model.loaded_library_unit_count(), 0);
                }
            }
        }
    }
}

#[test]
fn swallowed_inherited_default_error_restores_the_callers_visible_arguments() {
    // Inherited defaults retain the established best-effort fallback. The
    // unrelated declaration and failed nested call must restore visibility
    // before the caller evaluates its next operand.
    let source = "part def General {attribute bad[0] default G();}
        part child[1]:General {attribute :>>bad;}
        calc def G {1/0}
        calc def Base {in q default 1; attribute p=q; size(child.bad)+p}
        attribute direct=Base(7);";
    for (mode, model) in models(source).into_iter().enumerate() {
        let mut r = ResolvedModel::build(&model);
        for _ in 0..2 {
            for pkg in ["B", "A"] {
                let value = r.resolve_qualified(&format!("{pkg}::direct")).unwrap();
                assert_eq!(
                    r.evaluate(value),
                    Ok(sysmlv2_model::eval::Value::Integer(7)),
                    "mode={mode} {pkg}"
                );
            }
        }
        if mode == 3 {
            assert_eq!(model.loaded_library_unit_count(), 0);
        }
    }
}

#[test]
fn empty_argument_environment_does_not_erase_active_default_selection() {
    // No explicit actuals means the translator's argument environment is
    // empty, but its activation still selects Child::q for Base::p. The free
    // x prevents folding the entire calculation before symbolic translation.
    for asserted in [3, 2] {
        let source = format!(
            "calc def Base {{in p default 1;}}
             calc def Child :>Base {{in q :>>Base::p default 2;}}
             calc def Grand :>Child {{Base::p+x}}
             assert constraint c {{Grand()=={asserted} & x==1}}"
        );
        for (mode, model) in models(&source).into_iter().enumerate() {
            let mut r = ResolvedModel::build(&model);
            for _ in 0..2 {
                assert_solver_truth(
                    &mut r,
                    &model,
                    asserted == 3,
                    &format!("empty argument environment mode={mode} asserted={asserted}"),
                );
            }
            if mode == 3 {
                assert_eq!(model.loaded_library_unit_count(), 0);
            }
        }
    }
}
