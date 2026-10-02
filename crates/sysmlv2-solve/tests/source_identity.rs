//! Symbolic translation must agree with the graph's source-bound identities.
use std::{collections::HashMap, sync::Arc};
use sysmlv2_model::{
    json::ResolvedModel, libcache::LibraryCache, model::Model, prepared::PreparedLibrary,
};
use sysmlv2_solve::{
    PropagateOutcome, SolveOutcome, SolverConfig, propagate_constraints_with,
    solve_constraints_with, verify_constraints_with, z3_version,
};
const ID: &str = "88888888-8888-4888-8888-888888888888";
fn models(source: &str, use_expr: Option<&str>) -> Vec<Model> {
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
            if let Some(expr) = use_expr {
                for pkg in ["A", "B"] {
                    m.add_source(
                        format!("use{pkg}.sysml"),
                        &format!(
                            "package Use{pkg} {{ assert constraint c {{ {} }} }}",
                            expr.replace("PKG", pkg)
                        ),
                    );
                }
            }
            assert!(!m.has_errors());
            m
        })
        .collect()
}
fn bind(r: &mut ResolvedModel) {
    let actual = r.resolve_qualified("A::Actual").unwrap();
    let ordinary = r.resolve_qualified(&format!("A::'{ID}'")).unwrap();
    let sites = r.references_to(ordinary);
    assert_eq!(sites.len(), 1, "{sites:?}");
    r.override_ids(&HashMap::from([(
        r.element_id(actual),
        ID.parse().unwrap(),
    )]));
    let mut hints = HashMap::from([(
        (r.element_id(sites[0].owner), sites[0].kind.clone()),
        ID.parse().unwrap(),
    )]);
    assert!(
        r.bind_id_spelled_references_with(&mut hints)
            .contains(&ID.parse().unwrap())
    );
}
#[test]
fn symbolic_roots_and_nested_declarations_preserve_source_across_replay() {
    let cfg = SolverConfig::default();
    let native = z3_version(&cfg).is_ok();
    for form in ["root", "feature", "calc", "default", "sequence", "callee"] {
        for reverse in [false, true] {
            let (actual, spelled) = if reverse { (2, 1) } else { (1, 2) };
            let prefix = format!("attribute Actual={actual}; attribute '{ID}'={spelled};");
            let (source, caller) = match form {
                "root" => (
                    format!("{prefix} assert constraint c {{ x=='{ID}' & x==1 }}"),
                    None,
                ),
                "feature" => (
                    format!("{prefix} attribute bridge=x+'{ID}';"),
                    Some("PKG::bridge==1 & PKG::x==0"),
                ),
                "calc" => (
                    format!("{prefix} calc def F {{ in p; p+'{ID}' }}"),
                    Some("PKG::F(PKG::x)==1 & PKG::x==0"),
                ),
                "default" => (
                    format!("{prefix} calc def F {{ in p; in q default '{ID}'; p+q }}"),
                    Some("PKG::F(PKG::x)==1 & PKG::x==0"),
                ),
                "sequence" => (
                    format!("{prefix} attribute xs=(x,'{ID}');"),
                    Some("sum(PKG::xs)==1 & PKG::x==0"),
                ),
                _ => (
                    format!(
                        "calc def Actual {{ in p; p+{actual} }} calc def '{ID}' {{ in p; p+{spelled} }} calc def F {{ in p; '{ID}'(p) }}"
                    ),
                    Some("PKG::F(PKG::x)==1 & PKG::x==0"),
                ),
            };
            for (mode, model) in models(&source, caller).into_iter().enumerate() {
                let mut r = ResolvedModel::build(&model);
                bind(&mut r);
                for _ in 0..2 {
                    let result = propagate_constraints_with(&mut r, &model, &Default::default());
                    assert_eq!(result.constraints.len(), 2);
                    for c in result.constraints {
                        let name = &model.unit(c.unit).name;
                        let a = name
                            == if caller.is_some() {
                                "useA.sysml"
                            } else {
                                "A.sysml"
                            };
                        let sat = a != reverse;
                        assert_eq!(
                            c.propagate,
                            Some(if sat {
                                PropagateOutcome::Satisfied
                            } else {
                                PropagateOutcome::Unsatisfiable
                            }),
                            "{form} reverse={reverse} mode={mode} {name}"
                        );
                    }
                }
                if native {
                    let result = solve_constraints_with(&mut r, &model, &cfg).unwrap();
                    assert_eq!(result.len(), 2);
                    for c in result {
                        let name = &model.unit(c.unit).name;
                        let a = name
                            == if caller.is_some() {
                                "useA.sysml"
                            } else {
                                "A.sysml"
                            };
                        let sat = a != reverse;
                        assert!(
                            if sat {
                                matches!(c.solve, Some(SolveOutcome::Satisfiable(_)))
                            } else {
                                matches!(c.solve, Some(SolveOutcome::Unsatisfiable))
                            },
                            "{form} reverse={reverse} mode={mode} {name}: {:?}",
                            c.solve
                        );
                    }
                }
                let result =
                    verify_constraints_with(&mut r, &model, None, &Default::default()).unwrap();
                assert_eq!(result.constraints.len(), 2);
                for c in result.constraints {
                    let name = &model.unit(c.unit).name;
                    let a = name
                        == if caller.is_some() {
                            "useA.sysml"
                        } else {
                            "A.sysml"
                        };
                    assert_eq!(
                        c.propagate,
                        Some(if a != reverse {
                            PropagateOutcome::Satisfied
                        } else {
                            PropagateOutcome::Unsatisfiable
                        }),
                        "verify {form} reverse={reverse} mode={mode} {name}"
                    );
                }
                if mode == 3 {
                    assert_eq!(model.loaded_library_unit_count(), 0);
                }
            }
        }
    }
}
