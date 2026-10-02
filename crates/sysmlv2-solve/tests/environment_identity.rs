//! Runtime arguments retain declaration identity across lexical scopes and replay.
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
fn run(form: &str) {
    let cfg = SolverConfig::default();
    for reverse in [false, true] {
        let (actual, argument) = if reverse { (2, 1) } else { (1, 5) };
        let other = if reverse { 1 } else { 2 };
        let (source, target, site_owner, da, db, sata, satb) = match form {
            "global" => (
                format!(
                    "attribute Actual={actual}; calc def F {{ in '{ID}'; '{ID}' }} attribute direct=F({argument}); assert constraint c {{ F(x)==1 & x=={argument} }}"
                ),
                "A::Actual",
                "A::F",
                format!("Integer({actual})"),
                format!("Integer({argument})"),
                !reverse,
                reverse,
            ),
            "parameter" => (
                format!(
                    "calc def F {{ in p; in '{ID}'; '{ID}' }} attribute direct=F({actual},{argument}); assert constraint c {{ F({actual},x)==1 & x=={argument} }}"
                ),
                "A::F::p",
                "A::F",
                format!("Integer({actual})"),
                format!("Integer({argument})"),
                !reverse,
                reverse,
            ),
            "cross_call" => (
                format!(
                    "attribute Actual={actual}; attribute '{ID}'={other}; calc def G {{ in p; '{ID}' }} calc def F {{ in '{ID}'; G(0) }} attribute direct=F(5); assert constraint c {{ F(x)==1 & x==5 }}"
                ),
                "A::Actual",
                "A::G",
                format!("Integer({actual})"),
                format!("Integer({other})"),
                !reverse,
                reverse,
            ),
            "lambda_global" => (
                format!(
                    "attribute Actual={actual}; calc def F {{ in p; p->forAll {{ in '{ID}':ScalarValues::Integer; '{ID}'==1 }} }} attribute direct=F({argument}); assert constraint c {{ F(x) & x=={argument} }}"
                ),
                "A::Actual",
                "lambda",
                format!("Boolean({})", !reverse),
                format!("Boolean({reverse})"),
                !reverse,
                reverse,
            ),
            "lambda_parameter" => (
                format!(
                    "attribute '{ID}'={other}; calc def F {{ in p; p->forAll {{ in memberValue:ScalarValues::Integer; '{ID}'==1 }} }} attribute direct=F({actual}); assert constraint c {{ F(x) & x=={actual} }}"
                ),
                "lambda_parameter",
                "lambda",
                format!("Boolean({})", !reverse),
                format!("Boolean({reverse})"),
                !reverse,
                reverse,
            ),
            _ => unreachable!(),
        };
        for (mode, m) in models(&source).into_iter().enumerate() {
            let mut r = ResolvedModel::build(&m);
            let target = if target == "lambda_parameter" {
                let f = r.resolve_qualified("A::F").unwrap();
                let candidates: Vec<_> = r
                    .elements()
                    .filter(|e| {
                        r.element_properties(*e)
                            .get("declaredName")
                            .and_then(|v| v.as_str())
                            == Some("memberValue")
                    })
                    .collect();
                candidates
                    .into_iter()
                    .find(|e| {
                        let mut cur = r.owner(*e);
                        while let Some(owner) = cur {
                            if owner == f {
                                return true;
                            }
                            cur = r.owner(owner);
                        }
                        false
                    })
                    .unwrap()
            } else {
                r.resolve_qualified(target).unwrap()
            };
            let edge = if site_owner == "lambda" {
                let candidates: Vec<_> = r
                    .elements()
                    .filter(|e| {
                        r.element_properties(*e)
                            .get("declaredName")
                            .and_then(|v| v.as_str())
                            == Some(ID)
                    })
                    .collect();
                candidates
                    .into_iter()
                    .flat_map(|e| r.references_to(e))
                    .find(|s| m.unit(s.unit).name == "A.sysml")
                    .unwrap()
                    .owner
            } else {
                let owner = r.resolve_qualified(site_owner).unwrap();
                let expr = r.members_via(owner, "ResultExpressionMembership")[0];
                r.owned_relationships(expr)
                    .into_iter()
                    .find(|e| r.element_type(*e) == "Membership")
                    .unwrap()
            };
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
                for (pkg, expected) in [("B", &db), ("A", &da)] {
                    let e = r.resolve_qualified(&format!("{pkg}::direct")).unwrap();
                    assert_eq!(
                        format!("{:?}", r.evaluate(e).unwrap()),
                        *expected,
                        "{form} reverse={reverse} mode={mode} {pkg}"
                    );
                }
                for c in propagate_constraints_with(&mut r, &m, &Default::default()).constraints {
                    let sat = if m.unit(c.unit).name == "A.sysml" {
                        sata
                    } else {
                        satb
                    };
                    let got = match c.verdict {
                        ConstraintVerdict::Satisfied => true,
                        ConstraintVerdict::Violated => false,
                        _ => match c.propagate {
                            Some(PropagateOutcome::Satisfied) => true,
                            Some(PropagateOutcome::Unsatisfiable)
                            | Some(PropagateOutcome::Violated) => false,
                            _ => panic!("unexpected {c:?}"),
                        },
                    };
                    assert_eq!(got, sat, "{form} mode{mode}");
                }
                for c in native_solve(&mut r, &m, &cfg) {
                    let sat = if m.unit(c.unit).name == "A.sysml" {
                        sata
                    } else {
                        satb
                    };
                    let got = match c.verdict {
                        ConstraintVerdict::Satisfied => true,
                        ConstraintVerdict::Violated => false,
                        _ => match c.solve {
                            Some(SolveOutcome::Satisfiable(_)) | Some(SolveOutcome::Valid) => true,
                            Some(SolveOutcome::Unsatisfiable) => false,
                            _ => panic!("unexpected {c:?}"),
                        },
                    };
                    assert_eq!(got, sat, "{form} mode{mode}");
                }
            }
            if mode == 3 {
                assert_eq!(m.loaded_library_unit_count(), 0);
            }
        }
    }
}
#[test]
fn exact_global_beats_unrelated_same_named_parameter() {
    run("global")
}
#[test]
fn exact_parameter_identity_reads_its_runtime_argument() {
    run("parameter")
}
#[test]
fn a_separate_callee_cannot_capture_callers_parameter() {
    run("cross_call")
}
#[test]
fn exact_global_beats_typed_lambda_parameter_spelling() {
    run("lambda_global")
}
#[test]
fn exact_typed_lambda_parameter_identity_reads_runtime_member() {
    run("lambda_parameter")
}

#[test]
fn lexical_nested_calculation_and_lambda_capture_remains_supported() {
    for source in [
        "calc def F { in p; calc def G { p } G() }",
        "calc def F { in p; (1,2)->forAll { in q; q>0 & p==5 } }",
    ] {
        let condition = if source.contains("G()") {
            "F(x)==x & x==5"
        } else {
            "F(x) & x==5"
        };
        for (mode, m) in models(&format!(
            "{source} attribute direct=F(5); assert constraint c {{ {condition} }}"
        ))
        .into_iter()
        .enumerate()
        {
            let mut r = ResolvedModel::build(&m);
            for _ in 0..2 {
                for pkg in ["B", "A"] {
                    let e = r.resolve_qualified(&format!("{pkg}::direct")).unwrap();
                    let v = format!("{:?}", r.evaluate(e).unwrap());
                    assert_eq!(
                        v,
                        if source.contains("G()") {
                            "Integer(5)"
                        } else {
                            "Boolean(true)"
                        },
                        "mode{mode}"
                    );
                }
                for c in propagate_constraints_with(&mut r, &m, &Default::default()).constraints {
                    assert_eq!(
                        c.propagate,
                        Some(PropagateOutcome::Satisfied),
                        "{source}: {c:?}"
                    );
                }
                for c in native_solve(&mut r, &m, &Default::default()) {
                    assert!(
                        matches!(c.solve, Some(SolveOutcome::Satisfiable(_))),
                        "{source}: {c:?}"
                    );
                }
            }
            if mode == 3 {
                assert_eq!(m.loaded_library_unit_count(), 0);
            }
        }
    }
}

#[test]
fn exact_callee_identity_bypasses_unrelated_noncallable_parameter() {
    let source = format!(
        "calc def Actual {{ in p; p+1 }} calc def F {{ in '{ID}'; in n; '{ID}'(n) }} attribute direct=F(5,0); assert constraint c {{ F(5,x)==1 & x==0 }}"
    );
    let cfg = SolverConfig::default();
    for (mode, m) in models(&source).into_iter().enumerate() {
        let mut r = ResolvedModel::build(&m);
        let actual = r.resolve_qualified("A::Actual").unwrap();
        let f = r.resolve_qualified("A::F").unwrap();
        let expr = r.members_via(f, "ResultExpressionMembership")[0];
        let edge = r
            .owned_relationships(expr)
            .into_iter()
            .find(|e| r.element_type(*e) == "Membership")
            .unwrap();
        r.override_ids(&HashMap::from([(
            r.element_id(actual),
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
            let a = r.resolve_qualified("A::direct").unwrap();
            let b = r.resolve_qualified("B::direct").unwrap();
            assert_eq!(
                format!("{:?}", r.evaluate(a).unwrap()),
                "Integer(1)",
                "mode{mode}"
            );
            assert!(r.evaluate(b).is_err());
            for c in propagate_constraints_with(&mut r, &m, &Default::default()).constraints {
                if m.unit(c.unit).name == "A.sysml" {
                    assert_eq!(c.propagate, Some(PropagateOutcome::Satisfied));
                } else {
                    assert!(matches!(
                        c.propagate,
                        Some(PropagateOutcome::Unsupported(_))
                    ));
                }
            }
            for c in native_solve(&mut r, &m, &cfg) {
                if m.unit(c.unit).name == "A.sysml" {
                    assert!(matches!(c.solve, Some(SolveOutcome::Satisfiable(_))));
                } else {
                    assert!(matches!(c.solve, Some(SolveOutcome::Unknown(_))));
                }
            }
        }
        if mode == 3 {
            assert_eq!(m.loaded_library_unit_count(), 0);
        }
    }
}

#[test]
fn qualified_enclosing_parameters_and_recursive_defaults_keep_separate_frames() {
    use sysmlv2_model::eval::Value;
    let source = "calc def Outer { in x; calc def Inner { in x; x + Outer::x } Inner(2) }
        calc def Recur { in n; in x default 2; if n > 0 ? Recur(n - 1) else x }
        calc def Required { in n; in x; if n > 0 ? Required(n - 1) else x }
        attribute direct = Outer(5);
        attribute recursiveDefault = Recur(1,9);
        attribute recursiveMissing = Required(1,9);
        attribute recovery = Recur(0,8);
        assert constraint c { Outer(x)==7 & x==5 }";
    for (mode, m) in models(source).into_iter().enumerate() {
        let mut r = ResolvedModel::build(&m);
        for _ in 0..2 {
            for pkg in ["A", "B"] {
                for (name, expected) in [("direct", 7), ("recursiveDefault", 2), ("recovery", 8)] {
                    let e = r.resolve_qualified(&format!("{pkg}::{name}")).unwrap();
                    assert_eq!(
                        r.evaluate(e),
                        Ok(Value::Integer(expected)),
                        "{pkg}::{name} mode{mode}"
                    );
                }
                let e = r
                    .resolve_qualified(&format!("{pkg}::recursiveMissing"))
                    .unwrap();
                assert!(r.evaluate(e).is_err());
            }
            for c in propagate_constraints_with(&mut r, &m, &Default::default()).constraints {
                assert_eq!(c.propagate, Some(PropagateOutcome::Satisfied));
            }
            for c in native_solve(&mut r, &m, &Default::default()) {
                assert!(matches!(c.solve, Some(SolveOutcome::Satisfiable(_))));
            }
        }
        if mode == 3 {
            assert_eq!(m.loaded_library_unit_count(), 0);
        }
    }
}

#[test]
fn inherited_parameter_dependencies_use_the_active_call_argument() {
    use sysmlv2_model::eval::Value;
    for (name, body) in [
        ("p", "v"),
        ("q", "v"),
        ("q", "sum(v)"),
        ("p", "Base::p"),
        ("q", "Base::p"),
        ("q", "alias old for Base::p; old"),
        ("q", "calc def Nested { Base::p } Nested()"),
    ] {
        let source = format!(
            "calc def Base {{ in p default 1; attribute v=p; }}
            calc def Child :>Base {{ in {name} :>> Base::p default 2; {body} }}
            attribute direct=Child(7); attribute defaulted=Child();
            assert constraint c {{ Child(x)==7 & x==7 }}"
        );
        for (mode, m) in models(&source).into_iter().enumerate() {
            let mut r = ResolvedModel::build(&m);
            for _ in 0..2 {
                for pkg in ["A", "B"] {
                    for (member, value) in [("direct", 7), ("defaulted", 2)] {
                        let e = r.resolve_qualified(&format!("{pkg}::{member}")).unwrap();
                        assert_eq!(
                            r.evaluate(e),
                            Ok(Value::Integer(value)),
                            "name={name} body={body} mode={mode} {member}"
                        );
                    }
                }
                for c in propagate_constraints_with(&mut r, &m, &Default::default()).constraints {
                    assert_eq!(
                        c.propagate,
                        Some(PropagateOutcome::Satisfied),
                        "name={name} body={body} mode={mode}"
                    );
                }
                for c in native_solve(&mut r, &m, &Default::default()) {
                    assert!(
                        matches!(c.solve, Some(SolveOutcome::Satisfiable(_))),
                        "name={name} body={body} mode={mode}"
                    );
                }
            }
            if mode == 3 {
                assert_eq!(m.loaded_library_unit_count(), 0);
            }
        }
    }
}

#[test]
fn unrelated_declarations_do_not_capture_specialized_arguments() {
    use sysmlv2_model::eval::Value;
    let source = "calc def Base {in p default 1;}
        attribute packageValue = Base::p;
        calc def Other { Base::p }
        calc def Child :>Base { in q :>>Base::p; Other()+packageValue }
        attribute direct=Child(7);
        assert constraint c {Child(x)==2 & x==7}";
    for m in models(source) {
        let mut r = ResolvedModel::build(&m);
        for pkg in ["A", "B"] {
            let e = r.resolve_qualified(&format!("{pkg}::direct")).unwrap();
            assert_eq!(r.evaluate(e), Ok(Value::Integer(2)));
        }
        for c in propagate_constraints_with(&mut r, &m, &Default::default()).constraints {
            assert_eq!(c.propagate, Some(PropagateOutcome::Satisfied));
        }
        for c in native_solve(&mut r, &m, &Default::default()) {
            assert!(matches!(c.solve, Some(SolveOutcome::Satisfiable(_))));
        }
    }
}

#[test]
fn root_and_package_values_keep_lexical_dependencies_in_calls() {
    use sysmlv2_model::eval::Value;
    for root in [false, true] {
        for body in ["v", "sum(v)"] {
            for expected in [1, 2] {
                let globals = if root {
                    "attribute p=1; attribute v=p;"
                } else {
                    "package Values { attribute p=1; attribute v=p; }
                     private import Values::*;"
                };
                let source = format!(
                    "{globals} calc def Child {{ in p default 2; {body} }}
                     attribute direct=Child(7);
                     assert constraint c {{Child(x)=={expected} & x==7}}"
                );
                let fixtures = if root { models("") } else { models(&source) };
                for (mode, mut model) in fixtures.into_iter().enumerate() {
                    if root {
                        model.add_source(
                            "root.sysml",
                            &format!("attribute x[1]:ScalarValues::Integer; {source}"),
                        );
                        assert!(!model.has_errors());
                    }
                    let mut resolved = ResolvedModel::build(&model);
                    for _ in 0..2 {
                        for name in if root {
                            &["direct"][..]
                        } else {
                            &["A::direct", "B::direct"][..]
                        } {
                            let value = resolved.resolve_qualified(name).unwrap();
                            assert_eq!(
                                resolved.evaluate(value),
                                Ok(Value::Integer(1)),
                                "root={root} body={body} expected={expected} mode={mode}",
                            );
                        }
                        for constraint in
                            propagate_constraints_with(&mut resolved, &model, &Default::default())
                                .constraints
                        {
                            if expected == 1 {
                                assert_eq!(constraint.propagate, Some(PropagateOutcome::Satisfied));
                            } else {
                                assert!(matches!(
                                    constraint.propagate,
                                    Some(
                                        PropagateOutcome::Unsatisfiable
                                            | PropagateOutcome::Violated
                                    )
                                ));
                            }
                        }
                        for constraint in native_solve(&mut resolved, &model, &Default::default()) {
                            if expected == 1 {
                                assert!(matches!(
                                    constraint.solve,
                                    Some(SolveOutcome::Satisfiable(_))
                                ));
                            } else {
                                assert!(
                                    constraint.verdict == ConstraintVerdict::Violated
                                        || constraint.solve == Some(SolveOutcome::Unsatisfiable)
                                );
                            }
                        }
                    }
                    if mode == 3 {
                        assert_eq!(model.loaded_library_unit_count(), 0);
                    }
                }
            }
        }
    }
}

#[test]
fn exact_parameter_identity_requires_lexical_frame_visibility() {
    use sysmlv2_model::eval::Value;
    for (source, expected) in [
        (
            "calc def Other { Base::p }
             calc def Base { in p default 1; Other() }",
            1,
        ),
        (
            "attribute bridge=Base::p;
             calc def Base { in p default 1; bridge }",
            1,
        ),
        (
            "calc def Base { in p default 1;
                 calc def Nested { Base::p } Nested() }",
            7,
        ),
    ] {
        for (mode, model) in models(&format!(
            "{source} attribute direct=Base(7);
             assert constraint c {{ Base(x)=={expected} & x==7 }}"
        ))
        .into_iter()
        .enumerate()
        {
            let mut resolved = ResolvedModel::build(&model);
            for _ in 0..2 {
                for name in ["A::direct", "B::direct"] {
                    let element = resolved.resolve_qualified(name).unwrap();
                    assert_eq!(
                        resolved.evaluate(element),
                        Ok(Value::Integer(expected)),
                        "mode={mode} source={source}",
                    );
                }
                for constraint in
                    propagate_constraints_with(&mut resolved, &model, &Default::default())
                        .constraints
                {
                    assert_eq!(constraint.propagate, Some(PropagateOutcome::Satisfied));
                }
                for constraint in native_solve(&mut resolved, &model, &Default::default()) {
                    assert!(matches!(
                        constraint.solve,
                        Some(SolveOutcome::Satisfiable(_))
                    ));
                }
            }
            if mode == 3 {
                assert_eq!(model.loaded_library_unit_count(), 0);
            }
        }
    }
}

#[test]
fn unrelated_type_values_cannot_fall_back_to_same_named_inputs() {
    for body in ["v", "sum(v)"] {
        for lexical_parameter in ["attribute p=1;", ""] {
            for (mode, model) in models(&format!(
                "part def Box {{{lexical_parameter} attribute v=p;}}
             calc def Child {{in p default 2; alias v for Box::v; {body}}}
             attribute direct=Child(7);
             attribute wrapped[1]:ScalarValues::Integer=Child(x);
             assert constraint c {{Child(x)==2 & x==7}}
             assert constraint wrappedConstraint {{wrapped==2 & x==7}}"
            ))
            .into_iter()
            .enumerate()
            {
                let mut resolved = ResolvedModel::build(&model);
                for _ in 0..2 {
                    for name in ["A::direct", "B::direct", "A::wrapped", "B::wrapped"] {
                        let element = resolved.resolve_qualified(name).unwrap();
                        let value = resolved.evaluate(element);
                        if lexical_parameter.is_empty() {
                            assert!(value.is_err());
                        } else {
                            assert_eq!(
                                value,
                                Ok(sysmlv2_model::eval::Value::Integer(1)),
                                "mode={mode} body={body} name={name}"
                            );
                        }
                    }
                    for constraint in
                        propagate_constraints_with(&mut resolved, &model, &Default::default())
                            .constraints
                    {
                        assert!(
                            if lexical_parameter.is_empty() {
                                matches!(
                                    constraint.propagate,
                                    Some(PropagateOutcome::Unsupported(_))
                                )
                            } else {
                                matches!(
                                    constraint.propagate,
                                    Some(
                                        PropagateOutcome::Unsatisfiable
                                            | PropagateOutcome::Violated
                                    )
                                )
                            },
                            "mode={mode} body={body} lexical={lexical_parameter}: {constraint:?}",
                        );
                    }
                    for constraint in native_solve(&mut resolved, &model, &Default::default()) {
                        assert!(
                            if lexical_parameter.is_empty() {
                                matches!(constraint.solve, Some(SolveOutcome::Unknown(_)))
                            } else {
                                constraint.solve == Some(SolveOutcome::Unsatisfiable)
                                    || constraint.verdict == ConstraintVerdict::Violated
                            },
                            "mode={mode} body={body} lexical={lexical_parameter}: {constraint:?}",
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
fn ambiguous_or_incomplete_runtime_parameter_redefinitions_never_use_a_base_default() {
    for parameters in [
        "in p :>>Base::p; in q :>>Base::p;",
        "in q :>>Base::p; in p :>>Base::p;",
        "in p :>>Missing; in q;",
        "in p :>>q; in q :>>p;",
    ] {
        for m in models(&format!(
            "calc def Base {{in p default 1;}} calc def Child :>Base {{ {parameters} Base::p }} attribute direct=Child(7,8); assert constraint c {{Child(x,8)==1 & x==7}}"
        )) {
            let mut r = ResolvedModel::build(&m);
            for pkg in ["A", "B"] {
                let e = r.resolve_qualified(&format!("{pkg}::direct")).unwrap();
                assert!(r.evaluate(e).is_err(), "{parameters}");
            }
            for c in propagate_constraints_with(&mut r, &m, &Default::default()).constraints {
                assert!(
                    matches!(c.propagate, Some(PropagateOutcome::Unsupported(_))),
                    "{parameters}: {c:?}"
                );
            }
            for c in native_solve(&mut r, &m, &Default::default()) {
                assert!(
                    matches!(c.solve, Some(SolveOutcome::Unknown(_))),
                    "{parameters}: {c:?}"
                );
            }
        }
    }
}

#[test]
fn exact_general_parameter_identity_uses_the_supported_contextual_slot() {
    use sysmlv2_model::eval::Value;
    for reverse in [false, true] {
        let (argument, ordinary) = if reverse { (9, 7) } else { (7, 9) };
        let source = format!(
            "calc def Base {{in p default 1;}} calc def Child :>Base {{in q :>>Base::p; attribute '{ID}'={ordinary}; '{ID}'}} attribute direct=Child({argument}); assert constraint c {{Child(x)==7 & x=={argument}}}"
        );
        for (mode, m) in models(&source).into_iter().enumerate() {
            let mut r = ResolvedModel::build(&m);
            let target = r.resolve_qualified("A::Base::p").unwrap();
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
                for (pkg, value) in [("A", argument), ("B", ordinary)] {
                    let e = r.resolve_qualified(&format!("{pkg}::direct")).unwrap();
                    assert_eq!(
                        r.evaluate(e),
                        Ok(Value::Integer(value)),
                        "reverse={reverse} mode={mode} {pkg}"
                    );
                }
                for c in propagate_constraints_with(&mut r, &m, &Default::default()).constraints {
                    let sat = (m.unit(c.unit).name == "A.sysml") != reverse;
                    assert_eq!(
                        c.propagate,
                        Some(if sat {
                            PropagateOutcome::Satisfied
                        } else if m.unit(c.unit).name == "B.sysml" {
                            PropagateOutcome::Violated
                        } else {
                            PropagateOutcome::Unsatisfiable
                        })
                    );
                }
                for c in native_solve(&mut r, &m, &Default::default()) {
                    let sat = (m.unit(c.unit).name == "A.sysml") != reverse;
                    assert!(if sat {
                        matches!(c.solve, Some(SolveOutcome::Satisfiable(_)))
                    } else {
                        matches!(c.solve, Some(SolveOutcome::Unsatisfiable))
                    });
                }
            }
            if mode == 3 {
                assert_eq!(m.loaded_library_unit_count(), 0);
            }
        }
    }
}
