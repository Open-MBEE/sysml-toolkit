//! Receiver admission preserves lexical values and supported specializing contexts.
use std::{collections::HashMap, sync::Arc};
use sysmlv2_model::{
    check::ConstraintVerdict, json::ResolvedModel, libcache::LibraryCache, model::Model,
    prepared::PreparedLibrary,
};
use sysmlv2_solve::{
    PropagateOutcome, SolveOutcome, SolverConfig, propagate_constraints_with,
    solve_constraints_with, z3_version,
};
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
fn check_known(source: &str, expected_value: i128, satisfiable: bool, label: &str) {
    use sysmlv2_model::eval::Value;
    for (mode, model) in models(source).into_iter().enumerate() {
        let mut resolved = ResolvedModel::build(&model);
        for _ in 0..2 {
            for name in ["A::direct", "B::direct"] {
                let element = resolved.resolve_qualified(name).unwrap();
                assert_eq!(
                    resolved.evaluate(element),
                    Ok(Value::Integer(expected_value)),
                    "{label} mode={mode} {name}"
                );
            }
            let propagated = propagate_constraints_with(&mut resolved, &model, &Default::default());
            assert_eq!(propagated.constraints.len(), 2, "{label} mode={mode}");
            for constraint in propagated.constraints {
                if satisfiable {
                    assert_eq!(
                        constraint.propagate,
                        Some(PropagateOutcome::Satisfied),
                        "{label} mode={mode}: {constraint:?}"
                    );
                } else {
                    assert!(
                        matches!(
                            constraint.propagate,
                            Some(PropagateOutcome::Unsatisfiable | PropagateOutcome::Violated)
                        ),
                        "{label} mode={mode}: {constraint:?}"
                    );
                }
            }
            for constraint in native_solve(&mut resolved, &model, &Default::default()) {
                if satisfiable {
                    assert!(
                        matches!(
                            constraint.solve,
                            Some(SolveOutcome::Satisfiable(_) | SolveOutcome::Valid)
                        ) || constraint.verdict == ConstraintVerdict::Satisfied,
                        "{label} mode={mode}: {constraint:?}"
                    );
                } else {
                    assert!(
                        constraint.verdict == ConstraintVerdict::Violated
                            || constraint.solve == Some(SolveOutcome::Unsatisfiable),
                        "{label} mode={mode}: {constraint:?}"
                    );
                }
            }
        }
        if mode == 3 {
            assert_eq!(model.loaded_library_unit_count(), 0);
        }
    }
}

#[test]
fn unrelated_type_values_keep_their_own_lexical_scope() {
    for inputs in ["in p default 2;", "in unused; attribute p=2;"] {
        for body in ["v", "sum(v)"] {
            for expected in [1, 2] {
                let source = format!(
                    "part def Box {{ attribute p=1; attribute v=p; }}
                     calc def Child {{ {inputs} alias v for Box::v; {body} }}
                     attribute direct=Child(7);
                     assert constraint c {{Child(x)=={expected} & x==7}}"
                );
                check_known(
                    &source,
                    1,
                    expected == 1,
                    &format!("inputs={inputs} body={body} expected={expected}"),
                );
            }
        }
    }
}

#[test]
fn valid_receiver_contexts_keep_specialized_values() {
    for (declarations, value, open_value) in [
        (
            "calc def Base {in p default 1; attribute v=p;}
             calc def Child :> Base {in q :>>Base::p; v}",
            "Child(7)",
            "Child(x)",
        ),
        (
            "part def Base {attribute p=1; attribute v=p;}
             part child[1]:Base {attribute :>>p=7;}",
            "child.v",
            "child.v",
        ),
        (
            "part def Base {attribute p=1; attribute v default p;}
             part child[1]:Base {attribute :>>p=7; attribute :>>v;}",
            "child.v",
            "child.v",
        ),
        (
            "part def Base {attribute p=1; attribute v=p;}
             part child[1]:Base {attribute :>>p=7; attribute nested=v+0;}",
            "child.nested",
            "child.nested",
        ),
        (
            "calc def Outer {in p; calc def Nested {attribute v=p; v} Nested()}",
            "Outer(7)",
            "Outer(x)",
        ),
    ] {
        for expected in [7, 2] {
            let source = format!(
                "{declarations} attribute direct={value}; assert constraint c {{{open_value}=={expected} & x==7}}"
            );
            check_known(
                &source,
                7,
                expected == 7,
                &format!("{value} expected={expected}"),
            );
        }
    }
}

#[test]
fn incomplete_receiver_relationships_do_not_establish_value_context() {
    for heritage in [
        "calc def Child :> Missing",
        "calc def Loop :> Loop; calc def Child :> Loop",
        "calc def Left :> Right; calc def Right :> Left; calc def Child :> Left",
    ] {
        for body in ["v", "sum(v)"] {
            let source = format!(
                "part def Box {{attribute p=1; attribute v=p;}}
                 {heritage} {{in p default 2; alias v for Box::v; {body}}}
                 attribute direct=Child(7);
                 attribute wrapped[1]:ScalarValues::Integer=Child(x);
                 assert constraint c {{wrapped==2 & x==7}}"
            );
            for (mode, model) in models(&source).into_iter().enumerate() {
                let mut resolved = ResolvedModel::build(&model);
                for _ in 0..2 {
                    for name in ["A::direct", "B::direct", "A::wrapped", "B::wrapped"] {
                        let element = resolved.resolve_qualified(name).unwrap();
                        assert!(
                            resolved.evaluate(element).is_err(),
                            "heritage={heritage} body={body} mode={mode} {name}"
                        );
                    }
                    let propagated =
                        propagate_constraints_with(&mut resolved, &model, &Default::default());
                    assert_eq!(propagated.constraints.len(), 2);
                    for constraint in propagated.constraints {
                        assert!(
                            matches!(constraint.propagate, Some(PropagateOutcome::Unsupported(_))),
                            "heritage={heritage} body={body} mode={mode}: {constraint:?}"
                        );
                    }
                    for constraint in native_solve(&mut resolved, &model, &Default::default()) {
                        assert!(
                            matches!(constraint.solve, Some(SolveOutcome::Unknown(_))),
                            "heritage={heritage} body={body} mode={mode}: {constraint:?}"
                        );
                    }
                }
                if mode == 3 {
                    assert_eq!(model.loaded_library_unit_count(), 0);
                }
            }
        }
    }
}

#[test]
fn absent_lexical_dependency_stays_unsupported_after_receiver_proof() {
    for body in ["v", "sum(v)"] {
        for (mode, model) in models(&format!(
            "part def Box {{attribute v=p;}}
             calc def Child {{in p default 2; alias v for Box::v; {body}}}
             attribute direct=Child(7);
             assert constraint c {{Child(x)==2 & x==7}}"
        ))
        .into_iter()
        .enumerate()
        {
            let mut resolved = ResolvedModel::build(&model);
            for _ in 0..2 {
                for name in ["A::direct", "B::direct"] {
                    let element = resolved.resolve_qualified(name).unwrap();
                    assert!(
                        resolved.evaluate(element).is_err(),
                        "body={body} mode={mode}"
                    );
                }
                for constraint in
                    propagate_constraints_with(&mut resolved, &model, &Default::default())
                        .constraints
                {
                    assert!(
                        matches!(constraint.propagate, Some(PropagateOutcome::Unsupported(_))),
                        "body={body} mode={mode}: {constraint:?}"
                    );
                }
                for constraint in native_solve(&mut resolved, &model, &Default::default()) {
                    assert!(
                        matches!(constraint.solve, Some(SolveOutcome::Unknown(_))),
                        "body={body} mode={mode}: {constraint:?}"
                    );
                }
            }
            if mode == 3 {
                assert_eq!(model.loaded_library_unit_count(), 0);
            }
        }
    }
}

#[test]
fn exact_foreign_value_identity_keeps_source_and_lexical_owner() {
    use sysmlv2_model::eval::Value;
    const ID: &str = "88888888-8888-4888-8888-888888888888";
    for reverse in [false, true] {
        let (actual, ordinary) = if reverse { (9, 1) } else { (1, 9) };
        for (mode, model) in models(&format!(
            "part def Box {{attribute p={actual}; attribute v=p;}}
             calc def Child {{in q; attribute p=2; attribute '{ID}'={ordinary}; '{ID}'}}
             attribute direct=Child(7);
             assert constraint c {{Child(x)==1 & x==7}}"
        ))
        .into_iter()
        .enumerate()
        {
            let mut r = ResolvedModel::build(&model);
            let target = r.resolve_qualified("A::Box::v").unwrap();
            let child = r.resolve_qualified("A::Child").unwrap();
            let result = r.members_via(child, "ResultExpressionMembership")[0];
            let edge = r
                .owned_relationships(result)
                .into_iter()
                .find(|e| r.element_type(*e) == "Membership")
                .unwrap();
            r.override_ids(&HashMap::from([(
                r.element_id(target),
                ID.parse().unwrap(),
            )]));
            let mut hints = HashMap::from([(
                (r.element_id(edge), "memberElement".into()),
                ID.parse().unwrap(),
            )]);
            assert!(
                r.bind_id_spelled_references_with(&mut hints)
                    .contains(&ID.parse().unwrap())
            );
            for _ in 0..2 {
                for (pkg, value) in [("A", actual), ("B", ordinary)] {
                    let e = r.resolve_qualified(&format!("{pkg}::direct")).unwrap();
                    assert_eq!(
                        r.evaluate(e),
                        Ok(Value::Integer(value)),
                        "mode={mode} reverse={reverse} {pkg}"
                    );
                }
                for c in propagate_constraints_with(&mut r, &model, &Default::default()).constraints
                {
                    let sat = (model.unit(c.unit).name == "A.sysml") != reverse;
                    let got = match c.verdict {
                        ConstraintVerdict::Satisfied => true,
                        ConstraintVerdict::Violated => false,
                        _ => match c.propagate {
                            Some(PropagateOutcome::Satisfied) => true,
                            Some(PropagateOutcome::Unsatisfiable | PropagateOutcome::Violated) => {
                                false
                            }
                            _ => panic!("{c:?}"),
                        },
                    };
                    assert_eq!(got, sat, "mode={mode} reverse={reverse}");
                }
                for c in native_solve(&mut r, &model, &Default::default()) {
                    let sat = (model.unit(c.unit).name == "A.sysml") != reverse;
                    let got = match c.verdict {
                        ConstraintVerdict::Satisfied => true,
                        ConstraintVerdict::Violated => false,
                        _ => match c.solve {
                            Some(SolveOutcome::Satisfiable(_) | SolveOutcome::Valid) => true,
                            Some(SolveOutcome::Unsatisfiable) => false,
                            _ => panic!("{c:?}"),
                        },
                    };
                    assert_eq!(got, sat, "mode={mode} reverse={reverse}");
                }
            }
            if mode == 3 {
                assert_eq!(model.loaded_library_unit_count(), 0);
            }
        }
    }
}

fn custom_models(lib: &str, filename: &str, source: &str) -> Vec<Model> {
    let mut base = Model::new();
    base.add_library_source("parts.sysml", lib);
    base.record_library_cache();
    ResolvedModel::build(&base);
    let cache =
        LibraryCache::from_bytes(&base.take_recorded_library_cache().unwrap().to_bytes()).unwrap();
    let prepared = base.prepare_library().unwrap();
    let decoded =
        Arc::new(PreparedLibrary::from_bytes(&prepared.to_bytes(46).unwrap(), 46).unwrap());
    (0..4)
        .map(|mode| {
            let mut m = Model::new();
            match mode {
                2 => Arc::clone(&prepared).install(&mut m).unwrap(),
                3 => Arc::clone(&decoded).install(&mut m).unwrap(),
                _ => {
                    m.add_library_source("parts.sysml", lib);
                    if mode == 1 {
                        m.set_library_cache(cache.clone());
                    }
                }
            };
            m.add_source(filename, source);
            assert!(!m.has_errors());
            m
        })
        .collect()
}

#[test]
fn inherited_library_base_and_typed_receiver_keep_overrides() {
    use sysmlv2_model::{eval::Value, json::ValueScopeDecision};
    let lib =
        "standard library package Parts {part def Part {attribute p=1;attribute v=p;} part parts;}";
    let src = "part def Child {attribute :>>p=7;} part child[1]:Child; attribute direct=child.v;";
    for (mode, m) in custom_models(lib, "user.sysml", src)
        .into_iter()
        .enumerate()
    {
        let mut r = ResolvedModel::build(&m);
        let v = r.resolve_qualified("Parts::Part::v").unwrap();
        for _ in 0..2 {
            for name in ["Child", "child"] {
                let elem = r.resolve_qualified(name).unwrap();
                let scope = r.element_scope(elem).unwrap();
                assert_eq!(
                    r.value_scope_decision_with_steps(v, Some(scope), &mut 0),
                    ValueScopeDecision::Receiver(scope),
                    "mode={mode} {name}"
                );
            }
            let value = r.resolve_qualified("direct").unwrap();
            assert_eq!(r.evaluate(value), Ok(Value::Integer(7)), "mode={mode}");
        }
        if mode == 3 {
            assert_eq!(m.loaded_library_unit_count(), 0);
        }
    }
}

#[test]
fn conjugated_receiver_uses_original_type_values() {
    use sysmlv2_model::{eval::Value, json::ValueScopeDecision};
    let src = "classifier A {feature p=1;feature v=p;} classifier C conjugates A {feature redefines p=7;} feature direct=C.v;";
    for (mode, m) in custom_models("package Empty;", "conjugation.kerml", src)
        .into_iter()
        .enumerate()
    {
        let mut r = ResolvedModel::build(&m);
        let v = r.resolve_qualified("A::v").unwrap();
        let conjugated = r.resolve_qualified("C").unwrap();
        let scope = r.element_scope(conjugated).unwrap();
        for _ in 0..2 {
            assert_eq!(
                r.value_scope_decision_with_steps(v, Some(scope), &mut 0),
                ValueScopeDecision::Receiver(scope),
                "mode={mode}"
            );
            let e = r.resolve_qualified("direct").unwrap();
            assert_eq!(r.evaluate(e), Ok(Value::Integer(7)), "mode={mode}");
        }
        if mode == 3 {
            assert_eq!(m.loaded_library_unit_count(), 0);
        }
    }
}
