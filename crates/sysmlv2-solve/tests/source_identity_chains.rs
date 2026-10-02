//! Two-link singleton navigation retains source-bound member identities.
use std::{collections::HashMap, sync::Arc};
use sysmlv2_model::{
    json::ResolvedModel, libcache::LibraryCache, model::Model, prepared::PreparedLibrary,
};
use sysmlv2_solve::{
    PropagateOutcome, SolveOutcome, SolverConfig, propagate_constraints_with,
    solve_constraints_with, z3_version,
};
const ID: &str = "88888888-8888-4888-8888-888888888888";

#[test]
fn singleton_two_link_member_identity_crosses_units_without_capturing_equal_spans() {
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
    let cfg = SolverConfig::default();
    let native = z3_version(&cfg).is_ok();
    for reverse in [false, true] {
        for mode in 0..4 {
            let mut model = Model::new();
            match mode {
                2 => Arc::clone(&prepared).install(&mut model).unwrap(),
                3 => Arc::clone(&decoded).install(&mut model).unwrap(),
                _ => {
                    model.add_library_source("lib.kerml", lib);
                    if mode == 1 {
                        model.set_library_cache(cache.clone());
                    }
                }
            }
            for pkg in ["A", "B"] {
                let alias = if reverse { "Actual" } else { "Other" };
                model.add_source(format!("{pkg}.sysml"), &format!("package {pkg} {{ part def Leaf {{ attribute value:ScalarValues::Integer; }} part def Node {{ part Actual:Leaf[1]; part Other:Leaf[1]; alias '{ID}' for {alias}; }} part p:Node[1]; }}"));
            }
            for pkg in ["A", "B"] {
                model.add_source(format!("use{pkg}.sysml"), &format!("package Use{pkg} {{ assert constraint c {{ {pkg}::p.Actual.value == 0 & {pkg}::p->forAll {{ in i:{pkg}::Node; i.'{ID}'.value == 1 }} }} }}"));
            }
            assert!(!model.has_errors());
            let mut r = ResolvedModel::build(&model);
            let target = r
                .resolve_qualified(if reverse {
                    "A::Node::Other"
                } else {
                    "A::Node::Actual"
                })
                .unwrap();
            let ordinary = r.resolve_qualified(&format!("A::Node::'{ID}'")).unwrap();
            let a_site = r
                .references_to(ordinary)
                .into_iter()
                .find(|s| {
                    model.unit(s.unit).name == "useA.sysml"
                        && s.name_span.end - s.name_span.start == 38
                })
                .unwrap();
            let b_ordinary = r.resolve_qualified(&format!("B::Node::'{ID}'")).unwrap();
            let b_site = r
                .references_to(b_ordinary)
                .into_iter()
                .find(|s| {
                    model.unit(s.unit).name == "useB.sysml"
                        && s.name_span.end - s.name_span.start == 38
                })
                .unwrap();
            assert_eq!(
                a_site.name_span, b_site.name_span,
                "intentional cross-unit source-span collision"
            );
            r.override_ids(&HashMap::from([(
                r.element_id(target),
                ID.parse().unwrap(),
            )]));
            let mut hints = HashMap::from([(
                (r.element_id(a_site.owner), a_site.kind),
                ID.parse().unwrap(),
            )]);
            assert!(
                r.bind_id_spelled_references_with(&mut hints)
                    .contains(&ID.parse().unwrap())
            );
            for _ in 0..2 {
                let result = propagate_constraints_with(&mut r, &model, &Default::default());
                assert_eq!(result.constraints.len(), 2);
                for c in result.constraints {
                    let a = model.unit(c.unit).name == "useA.sysml";
                    let unsat = a != reverse;
                    assert_eq!(
                        c.propagate,
                        Some(if unsat {
                            PropagateOutcome::Unsatisfiable
                        } else {
                            PropagateOutcome::Satisfied
                        }),
                        "reverse={reverse} mode={mode} A={a}"
                    );
                }
            }
            if native {
                for c in solve_constraints_with(&mut r, &model, &cfg).unwrap() {
                    let a = model.unit(c.unit).name == "useA.sysml";
                    let unsat = a != reverse;
                    assert!(
                        if unsat {
                            matches!(c.solve, Some(SolveOutcome::Unsatisfiable))
                        } else {
                            matches!(c.solve, Some(SolveOutcome::Satisfiable(_)))
                        },
                        "reverse={reverse} mode={mode} A={a}: {:?}",
                        c.solve
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
fn null_coalescing_reads_bound_identity_before_selecting_a_symbolic_branch() {
    let cfg = SolverConfig::default();
    let native = z3_version(&cfg).is_ok();
    for reverse in [false, true] {
        let (actual, ordinary) = if reverse {
            ("0", "null")
        } else {
            ("null", "0")
        };
        let mut model = Model::new();
        for pkg in ["A", "B"] {
            model.add_source(format!("{pkg}.sysml"),&format!("package {pkg} {{ attribute def Integer; attribute x[1]:Integer; attribute Actual={actual}; attribute '{ID}'={ordinary}; assert constraint c {{ ('{ID}' ?? x)+x == 1 & x == 1 }} }}"));
        }
        assert!(!model.has_errors());
        let mut r = ResolvedModel::build(&model);
        let target = r.resolve_qualified("A::Actual").unwrap();
        let ordinary = r.resolve_qualified(&format!("A::'{ID}'")).unwrap();
        let sites = r.references_to(ordinary);
        assert_eq!(sites.len(), 1);
        r.override_ids(&HashMap::from([(
            r.element_id(target),
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
        for _ in 0..2 {
            let result = propagate_constraints_with(&mut r, &model, &Default::default());
            assert_eq!(result.constraints.len(), 2);
            for c in result.constraints {
                let unsat = (model.unit(c.unit).name == "A.sysml") != reverse;
                assert_eq!(
                    c.propagate,
                    Some(if unsat {
                        PropagateOutcome::Unsatisfiable
                    } else {
                        PropagateOutcome::Satisfied
                    }),
                    "reverse={reverse}: {c:?}"
                );
            }
        }
        if native {
            for c in solve_constraints_with(&mut r, &model, &cfg).unwrap() {
                let unsat = (model.unit(c.unit).name == "A.sysml") != reverse;
                assert!(
                    if unsat {
                        matches!(c.solve, Some(SolveOutcome::Unsatisfiable))
                    } else {
                        matches!(c.solve, Some(SolveOutcome::Satisfiable(_)))
                    },
                    "reverse={reverse}: {c:?}"
                );
            }
        }
    }
}
