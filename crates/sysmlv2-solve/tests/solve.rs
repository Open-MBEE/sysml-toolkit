//! Unit tests for constraint solving over small self-contained models.
//!
//! Every test needs a `z3` binary on PATH; when it is missing the suite
//! skips (with a note) rather than failing, so `cargo test` stays mid on
//! machines without Z3.

use sysmlv2_model::check::ConstraintVerdict;
use sysmlv2_model::model::Model;
use sysmlv2_solve::{SolveOutcome, SolverConfig, WitnessValue, solve_constraints, z3_version};

fn solve(src: &str) -> Option<Vec<sysmlv2_solve::SolvedConstraint>> {
    let cfg = SolverConfig::default();
    if z3_version(&cfg).is_err() {
        eprintln!("skipping: no z3 on PATH");
        return None;
    }
    let mut model = Model::new();
    let unit = model.add_source("test.sysml", src);
    assert!(
        unit.diagnostics.is_empty(),
        "test source must parse clean: {:?}",
        unit.diagnostics
    );
    Some(solve_constraints(&model, &cfg).expect("z3 available"))
}

/// The single undecided constraint's solve outcome.
fn outcome(src: &str) -> Option<SolveOutcome> {
    let solved = solve(src)?;
    let undecided: Vec<_> = solved
        .iter()
        .filter(|s| matches!(s.verdict, ConstraintVerdict::Undecided(_)))
        .collect();
    assert_eq!(
        undecided.len(),
        1,
        "expected exactly one undecided constraint: {solved:?}"
    );
    Some(undecided[0].solve.clone().expect("undecided ⇒ solved"))
}

#[test]
fn integer_witness() {
    let Some(out) = outcome(
        "package P {
            attribute def Integer;
            attribute x : Integer;
            assert constraint c { x > 3 & x < 5 }
        }",
    ) else {
        return;
    };
    let SolveOutcome::Satisfiable(w) = out else {
        panic!("expected a witness, got {out:?}");
    };
    assert_eq!(w, vec![("x".to_string(), WitnessValue::Int(4))]);
}

#[test]
fn integer_unsatisfiable() {
    let Some(out) = outcome(
        "package P {
            attribute def Integer;
            attribute x : Integer;
            assert constraint c { x > 5 & x < 4 }
        }",
    ) else {
        return;
    };
    assert_eq!(out, SolveOutcome::Unsatisfiable);
}

#[test]
fn parity_scaling_unsatisfiable_over_integers() {
    // 2x = 5 has no integer solution (but does have a real one) — the
    // declared type must drive the sort.
    let Some(out) = outcome(
        "package P {
            attribute def Integer;
            attribute x : Integer;
            assert constraint c { x * 2 == 5 }
        }",
    ) else {
        return;
    };
    assert_eq!(out, SolveOutcome::Unsatisfiable);
}

#[test]
fn real_witness_by_default_sort() {
    // No declared type: x defaults to Real, so an integer-free interval is
    // still satisfiable.
    let Some(out) = outcome(
        "package P {
            attribute x;
            assert constraint c { x > 3 & x < 4 }
        }",
    ) else {
        return;
    };
    let SolveOutcome::Satisfiable(w) = out else {
        panic!("expected a witness, got {out:?}");
    };
    assert_eq!(w.len(), 1);
    match w[0].1 {
        WitnessValue::Real(f) => assert!(f > 3.0 && f < 4.0, "witness {f} out of range"),
        ref v => panic!("expected a real witness, got {v:?}"),
    }
}

#[test]
fn boolean_tautology_is_valid() {
    let Some(out) = outcome(
        "package P {
            attribute def Boolean;
            attribute b : Boolean;
            assert constraint c { b or not b }
        }",
    ) else {
        return;
    };
    assert_eq!(out, SolveOutcome::Valid);
}

#[test]
fn negated_assert_flips_the_goal() {
    // `assert not` of a contradiction holds for every x.
    let Some(out) = outcome(
        "package P {
            attribute x;
            assert not constraint c { x != x }
        }",
    ) else {
        return;
    };
    assert_eq!(out, SolveOutcome::Valid);
}

#[test]
fn enum_witness_and_unsat() {
    let Some(solved) = solve(
        "package P {
            enum def Phase { halt; mid; init; }
            attribute c : Phase;
            assert constraint pick { c != Phase::halt & c != Phase::mid }
            assert constraint clash { c == Phase::halt & c == Phase::mid }
        }",
    ) else {
        return;
    };
    let outs: Vec<_> = solved.iter().filter_map(|s| s.solve.clone()).collect();
    assert_eq!(outs.len(), 2, "{solved:?}");
    assert_eq!(
        outs[0],
        SolveOutcome::Satisfiable(vec![(
            "c".to_string(),
            WitnessValue::Enum("init".to_string())
        )])
    );
    assert_eq!(outs[1], SolveOutcome::Unsatisfiable);
}

/// A variation's `variant` members are its closed set of legal
/// choices — they solve as a finite sort exactly like enum literals.
#[test]
fn variant_values_solve_as_finite_sorts() {
    let Some(solved) = solve(
        "package P {
            variation part def Engine {
                variant part engine4Cyl;
                variant part engine6Cyl;
            }
            part engine : Engine;
            assert constraint pick { engine != Engine::engine4Cyl }
            assert constraint clash {
                engine == Engine::engine4Cyl & engine == Engine::engine6Cyl
            }
        }",
    ) else {
        return;
    };
    let outs: Vec<_> = solved.iter().filter_map(|s| s.solve.clone()).collect();
    assert_eq!(outs.len(), 2, "{solved:?}");
    assert_eq!(
        outs[0],
        SolveOutcome::Satisfiable(vec![(
            "engine".to_string(),
            WitnessValue::Enum("engine6Cyl".to_string())
        )])
    );
    assert_eq!(outs[1], SolveOutcome::Unsatisfiable);
}

/// Invocations translate *through* user-calculation bodies: arguments
/// bind to parameters and the body inlines symbolically.
#[test]
fn calculation_bodies_inline() {
    let Some(solved) = solve(
        "package P {
            attribute def Integer;
            calc def Double { in x; x * 2 }
            attribute y : Integer;
            assert constraint c { Double(y) == 14 }
            assert constraint t { Double(y) == y * 2 }
        }",
    ) else {
        return;
    };
    let outs: Vec<_> = solved.iter().filter_map(|s| s.solve.clone()).collect();
    assert_eq!(outs.len(), 2, "{solved:?}");
    assert_eq!(
        outs[0],
        SolveOutcome::Satisfiable(vec![("y".to_string(), WitnessValue::Int(7))])
    );
    // The second restates the body — a tautology, proven valid.
    assert_eq!(outs[1], SolveOutcome::Valid);
}

/// Same-dimension quantities in different units convert through their
/// measurement references: `x <= 2 [min]` and `x >= 90 [s]` constrain
/// one variable, and the witness stays in the first unit seen.
#[test]
fn units_convert_across_scales() {
    let Some(out) = outcome(
        "package P {
            attribute def Integer;
            attribute s; attribute m;
            attribute min {
                attribute unitConversion {
                    attribute referenceUnit = s;
                    attribute conversionFactor = 60;
                }
            }
            attribute x : Integer;
            assert constraint c { x * 1 [min] <= 2 [min] & x * 1 [min] >= 90 [s] }
        }",
    ) else {
        return;
    };
    // 90 s = 1.5 min, so x*1min in [1.5 min, 2 min] — x integer = 2.
    assert_eq!(
        out,
        SolveOutcome::Satisfiable(vec![("x".to_string(), WitnessValue::Int(2))])
    );
}

/// `a ?? b`: a translatable left side denotes a present scalar and
/// wins; a left side the evaluator proves null yields the right side.
#[test]
fn null_coalescing_translates() {
    let Some(out) = outcome(
        "package P {
            attribute def Integer;
            attribute x : Integer;
            assert constraint c { (x ?? 99) == 7 }
        }",
    ) else {
        return;
    };
    assert_eq!(
        out,
        SolveOutcome::Satisfiable(vec![("x".to_string(), WitnessValue::Int(7))])
    );
    let Some(out) = outcome(
        "package P {
            attribute def Integer;
            attribute a = null;
            attribute y : Integer;
            assert constraint c { (a ?? y) == 3 }
        }",
    ) else {
        return;
    };
    assert_eq!(
        out,
        SolveOutcome::Satisfiable(vec![("y".to_string(), WitnessValue::Int(3))])
    );
}

#[test]
fn chained_definitions_inline() {
    // y is defined in terms of the unbound x: the definition inlines and
    // the witness is over x.
    let Some(out) = outcome(
        "package P {
            attribute def Integer;
            attribute x : Integer;
            attribute y : Integer = x * x;
            assert constraint c { y == 49 & x < 0 }
        }",
    ) else {
        return;
    };
    let SolveOutcome::Satisfiable(w) = out else {
        panic!("expected a witness, got {out:?}");
    };
    assert!(
        w.contains(&("x".to_string(), WitnessValue::Int(-7))),
        "{w:?}"
    );
}

#[test]
fn natural_lower_bound_side_constraint() {
    let Some(out) = outcome(
        "package P {
            attribute def Natural;
            attribute n : Natural;
            assert constraint c { n < 0 }
        }",
    ) else {
        return;
    };
    assert_eq!(out, SolveOutcome::Unsatisfiable);
}

#[test]
fn int_real_mixing_coerces() {
    let Some(out) = outcome(
        "package P {
            attribute def Integer;
            attribute x : Integer;
            assert constraint c { x + 0.5 > 2.4 & x < 3 }
        }",
    ) else {
        return;
    };
    let SolveOutcome::Satisfiable(w) = out else {
        panic!("expected a witness, got {out:?}");
    };
    assert_eq!(w, vec![("x".to_string(), WitnessValue::Int(2))]);
}

#[test]
fn independent_units_solve_with_tagged_witnesses() {
    // Two comparisons in two different units are fine as long as each
    // variable lives in one unit — witnesses carry the inferred unit.
    let Some(out) = outcome(
        "package P {
            attribute d; attribute kB;
            attribute duration;
            attribute volume;
            assert constraint c { duration >= 30 [d] & volume >= 100 [kB] }
        }",
    ) else {
        return;
    };
    let SolveOutcome::Satisfiable(w) = out else {
        panic!("expected a witness, got {out:?}");
    };
    let shown: Vec<String> = w.iter().map(|(n, v)| format!("{n} = {v}")).collect();
    assert_eq!(shown, ["duration = 30 [d]", "volume = 100 [kB]"], "{w:?}");
}

#[test]
fn one_variable_in_two_unrelated_units_is_unknown() {
    // `h` and `min` here are *opaque local attributes* — no measurement
    // references relate them, so no conversion exists and the honest
    // answer stays unknown. (Same-dimension units convert:
    // `variable_converts_across_same_dimension_units`.)
    let Some(out) = outcome(
        "package P {
            attribute h; attribute min;
            attribute duration;
            assert constraint c { duration <= 2 [h] & duration >= 30 [min] }
        }",
    ) else {
        return;
    };
    let SolveOutcome::Unknown(m) = out else {
        panic!("expected unknown, got {out:?}");
    };
    assert!(m.contains("no unit conversion"), "{m}");
}

/// A variable tagged in one unit and later *demanded* in another unit
/// of the same dimension converts at the occurrence: the variable keeps
/// its own unit (and its witness prints in it); the demanding context
/// reads `var × (scale_var / scale_ctx)`. Conversion factors 4 and 16
/// are exact in binary, so the witness is exact.
#[test]
fn variable_converts_across_same_dimension_units() {
    let Some(out) = outcome(
        "package P {
            attribute s;
            attribute beat {
                attribute unitConversion {
                    attribute referenceUnit = s;
                    attribute conversionFactor = 4;
                }
            }
            attribute bar {
                attribute unitConversion {
                    attribute referenceUnit = s;
                    attribute conversionFactor = 16;
                }
            }
            attribute x; attribute y;
            assert constraint c { x >= 8 [beat] & x + y == 5 [bar] & y == 0 [bar] }
        }",
    ) else {
        return;
    };
    // 5 bar = 80 s = 20 beat; y pinned to 0 → x = 20 (in beats).
    let SolveOutcome::Satisfiable(w) = out else {
        panic!("expected satisfiable, got {out:?}");
    };
    let x = w.iter().find(|(n, _)| n == "x").expect("x in witness");
    assert_eq!(
        x.1,
        WitnessValue::WithUnit(Box::new(WitnessValue::Real(20.0)), "beat".to_string()),
        "{w:?}"
    );
}

#[test]
fn unit_propagates_through_addition_and_linked_vars() {
    // `a + b <= 5 [h]` tags both addends; `b == c` links c; a later
    // `c >= 30 [min]` must then conflict.
    let Some(out) = outcome(
        "package P {
            attribute h; attribute min;
            attribute a; attribute b; attribute c;
            assert constraint k { a + b <= 5 [h] & b == c & c >= 1 [min] }
        }",
    ) else {
        return;
    };
    assert!(
        matches!(&out, SolveOutcome::Unknown(m) if m.contains("no unit conversion")),
        "{out:?}"
    );
}

#[test]
fn scalar_scaling_keeps_the_unit() {
    let Some(out) = outcome(
        "package P {
            attribute mm;
            attribute width;
            assert constraint c { 2 * width <= 10 [mm] & width >= 4 [mm] }
        }",
    ) else {
        return;
    };
    let SolveOutcome::Satisfiable(w) = out else {
        panic!("expected a witness, got {out:?}");
    };
    // 2·width ≤ 10 ∧ width ≥ 4 → width ∈ [4, 5], tagged mm.
    match &w[0].1 {
        sysmlv2_solve::WitnessValue::WithUnit(v, u) => {
            assert_eq!(u, "mm");
            match **v {
                sysmlv2_solve::WitnessValue::Real(f) => {
                    assert!((4.0..=5.0).contains(&f), "{f}")
                }
                ref other => panic!("unexpected witness {other:?}"),
            }
        }
        other => panic!("expected a unit-tagged witness, got {other:?}"),
    }
}

#[test]
fn unsupported_construct_is_unknown() {
    let Some(out) = outcome(
        "package P {
            attribute def Integer;
            attribute x : Integer;
            assert constraint c { (1..x)->size() == 2 }
        }",
    ) else {
        return;
    };
    let SolveOutcome::Unknown(m) = out else {
        panic!("expected unknown, got {out:?}");
    };
    assert!(m.contains("not in the solvable fragment"), "{m}");
}

#[test]
fn missing_z3_binary_reports_unavailable() {
    let cfg = SolverConfig {
        z3_path: Some("/nonexistent/z3-binary".into()),
        ..Default::default()
    };
    let mut model = Model::new();
    model.add_source("test.sysml", "package P { }");
    let err = solve_constraints(&model, &cfg);
    assert!(matches!(
        err,
        Err(sysmlv2_solve::SolveError::SolverUnavailable(_))
    ));
}

#[test]
fn modulo_truncated_semantics() {
    // `%` is the evaluator's (Rust's) truncated remainder: the sign
    // follows the dividend, not SMT's Euclidean `mod`.
    let Some(out) = outcome(
        "package P {
            attribute def Integer;
            attribute x : Integer;
            assert constraint c { x > -10 & x < 0 & x % 3 == -1 }
        }",
    ) else {
        return;
    };
    let SolveOutcome::Satisfiable(w) = out else {
        panic!("expected a witness, got {out:?}");
    };
    let (name, WitnessValue::Int(v)) = &w[0] else {
        panic!("expected an integer witness, got {w:?}");
    };
    assert_eq!(name, "x");
    assert_eq!(v % 3, -1, "witness {v} must satisfy truncated `%`");
}

#[test]
fn modulo_unsatisfiable_range() {
    // Euclidean `mod` would admit x = -2 (mod 3 = 1); truncated `%`
    // gives -2 % 3 = -2, so no negative x in range has x % 3 == 1
    // except those ≡ 1 under truncation: -10 < x < 0 has none with
    // x % 3 == 2 and x even… keep it provable: x % 3 == 2 & x == -1
    // is UNSAT (-1 % 3 == -1).
    let Some(out) = outcome(
        "package P {
            attribute def Integer;
            attribute x : Integer;
            assert constraint c { x == -1 & x % 3 == 2 }
        }",
    ) else {
        return;
    };
    assert!(
        matches!(out, SolveOutcome::Unsatisfiable),
        "-1 % 3 is -1 under truncated semantics, got {out:?}"
    );
}

#[test]
fn string_equality_witness() {
    let Some(out) = outcome(
        "package P {
            attribute def String;
            attribute s : String;
            assert constraint c { s == \"on\" }
        }",
    ) else {
        return;
    };
    let SolveOutcome::Satisfiable(w) = out else {
        panic!("expected a witness, got {out:?}");
    };
    assert_eq!(w[0].0, "s");
    assert!(
        w[0].1.to_string().contains("on"),
        "string witness should carry the value, got {:?}",
        w[0].1
    );
}

#[test]
fn string_disequality_unsatisfiable() {
    let Some(out) = outcome(
        "package P {
            attribute def String;
            attribute s : String;
            assert constraint c { s == \"on\" & s != \"on\" }
        }",
    ) else {
        return;
    };
    assert!(
        matches!(out, SolveOutcome::Unsatisfiable),
        "expected UNSAT, got {out:?}"
    );
}

/// A quantity bracket over an *unbound* magnitude (`x [min]`) translates
/// structurally — the magnitude becomes the term, the unit expression is
/// read on its own — so the direct spelling works without the
/// `x * 1 [min]` scaling workaround, converting across scales like any
/// tagged term.
#[test]
fn bracket_over_unbound_magnitude() {
    let Some(out) = outcome(
        "package P {
            attribute def Integer;
            attribute s;
            attribute min {
                attribute unitConversion {
                    attribute referenceUnit = s;
                    attribute conversionFactor = 60;
                }
            }
            attribute x : Integer;
            assert constraint c { x [min] <= 2 [min] & x [min] >= 90 [s] }
        }",
    ) else {
        return;
    };
    // 90 s = 1.5 min, so x in [1.5, 2] — x integer = 2.
    assert_eq!(
        out,
        SolveOutcome::Satisfiable(vec![("x".to_string(), WitnessValue::Int(2))])
    );
}

/// A bracketed compound magnitude tags the whole subterm.
#[test]
fn bracket_over_compound_magnitude() {
    let Some(out) = outcome(
        "package P {
            attribute def Integer;
            attribute s;
            attribute x : Integer;
            assert constraint c { (x + 1) [s] == 3 [s] }
        }",
    ) else {
        return;
    };
    assert_eq!(
        out,
        SolveOutcome::Satisfiable(vec![("x".to_string(), WitnessValue::Int(2))])
    );
}

/// Brackets in two different dimensions on one comparison stay outside
/// the fragment, same as constant quantities.
#[test]
fn bracket_units_mismatch_is_unknown() {
    let Some(out) = outcome(
        "package P {
            attribute def Integer;
            attribute kg; attribute s;
            attribute x : Integer;
            assert constraint c { x [kg] > 2 [s] }
        }",
    ) else {
        return;
    };
    let SolveOutcome::Unknown(m) = out else {
        panic!("expected Unknown, got {out:?}");
    };
    assert!(m.contains("no unit conversion"), "{m}");
}

/// A bracket whose unit cancels dimensionally (`[km/m]`) folds its
/// residual scale into the number, mirroring the evaluator. (The factor
/// is chosen f64-exact: SMT reals are exact rationals, so a factor like
/// `0.001` — not representable in binary — would make integer-witness
/// equalities genuinely unsatisfiable.)
#[test]
fn bracket_dimensionless_scale_folds() {
    let Some(out) = outcome(
        "package P {
            attribute def Integer;
            attribute m;
            attribute km {
                attribute unitConversion {
                    attribute referenceUnit = m;
                    attribute conversionFactor = 1000;
                }
            }
            attribute x : Integer;
            assert constraint c { x [km/m] == 5000 & x > 0 }
        }",
    ) else {
        return;
    };
    assert_eq!(
        out,
        SolveOutcome::Satisfiable(vec![("x".to_string(), WitnessValue::Int(5))])
    );
}

// -- KFL sequence intrinsics over known-arity arguments -----------------------

/// The Mass-Roll-up shape: `sum` over a feature whose value is a
/// sequence of unbound scalars — the fold pins the total.
#[test]
fn sum_over_bound_sequence() {
    let Some(out) = outcome(
        "package P {
            attribute def Integer;
            attribute total : Integer;
            attribute a : Integer;
            attribute b : Integer;
            attribute ps : Integer[0..*] = (a, b);
            assert constraint c { total == sum(ps) & a == 2 & b == 3 }
        }",
    ) else {
        return;
    };
    let SolveOutcome::Satisfiable(w) = out else {
        panic!("expected a witness, got {out:?}");
    };
    assert!(
        w.contains(&("total".to_string(), WitnessValue::Int(5))),
        "total should be forced to 5: {w:?}"
    );
}

/// Sequence arguments flatten (KerML sequences are flat): a nested
/// spelling counts its scalars, and `size` folds to a constant.
#[test]
fn size_flattens_nested_sequences() {
    let Some(out) = outcome(
        "package P {
            attribute def Integer;
            attribute n : Integer;
            attribute a : Integer;
            attribute b : Integer;
            attribute c : Integer;
            attribute ps : Integer[0..*] = (a, (b, c));
            assert constraint k { n == size(ps) & notEmpty(ps) }
        }",
    ) else {
        return;
    };
    assert_eq!(
        out,
        SolveOutcome::Satisfiable(vec![("n".to_string(), WitnessValue::Int(3))])
    );
}

/// `max`/`min` fold to `ite` chains — both the one-sequence and the
/// two-scalar spellings.
#[test]
fn max_min_fold_to_ite_chains() {
    let Some(out) = outcome(
        "package P {
            attribute def Integer;
            attribute hi : Integer;
            attribute lo : Integer;
            attribute a : Integer;
            attribute b : Integer;
            assert constraint c {
                hi == max((a, b)) & lo == min(a, b) & a == 2 & b == 7
            }
        }",
    ) else {
        return;
    };
    let SolveOutcome::Satisfiable(w) = out else {
        panic!("expected a witness, got {out:?}");
    };
    assert!(
        w.contains(&("hi".to_string(), WitnessValue::Int(7))),
        "{w:?}"
    );
    assert!(
        w.contains(&("lo".to_string(), WitnessValue::Int(2))),
        "{w:?}"
    );
}

/// `product`, `abs`, `head`, `last` — the rest of the fold table.
#[test]
fn product_abs_head_last_fold() {
    let Some(out) = outcome(
        "package P {
            attribute def Integer;
            attribute p : Integer;
            attribute y : Integer;
            attribute h : Integer;
            attribute l : Integer;
            attribute a : Integer;
            attribute b : Integer;
            assert constraint c {
                p == product((a, b)) & y == abs(0 - a) &
                h == head((a, b)) & l == last((a, b)) &
                a == 3 & b == 4
            }
        }",
    ) else {
        return;
    };
    let SolveOutcome::Satisfiable(w) = out else {
        panic!("expected a witness, got {out:?}");
    };
    assert!(
        w.contains(&("p".to_string(), WitnessValue::Int(12))),
        "{w:?}"
    );
    assert!(
        w.contains(&("y".to_string(), WitnessValue::Int(3))),
        "{w:?}"
    );
    assert!(
        w.contains(&("h".to_string(), WitnessValue::Int(3))),
        "{w:?}"
    );
    assert!(
        w.contains(&("l".to_string(), WitnessValue::Int(4))),
        "{w:?}"
    );
}

/// Unit-tagged items convert through the fold like binary `+`:
/// `1 [min] + 30 [s]` sums to 1.5 min = 90 s.
#[test]
fn sum_converts_units_across_scales() {
    let Some(out) = outcome(
        "package P {
            attribute def Integer;
            attribute s; attribute m;
            attribute min {
                attribute unitConversion {
                    attribute referenceUnit = s;
                    attribute conversionFactor = 60;
                }
            }
            attribute x : Integer;
            assert constraint c { x [s] == sum((1 [min], 30 [s])) }
        }",
    ) else {
        return;
    };
    assert_eq!(
        out,
        SolveOutcome::Satisfiable(vec![("x".to_string(), WitnessValue::Int(90))])
    );
}

/// A valueless `[0..*]` collection has no static arity: the fold bails
/// with the sharpened reason, not the blanket invocation one.
#[test]
fn sum_over_valueless_collection_bails_with_arity_reason() {
    let Some(out) = outcome(
        "package P {
            attribute def Integer;
            attribute total : Integer;
            attribute ps : Integer[0..*];
            assert constraint c { total == sum(ps) }
        }",
    ) else {
        return;
    };
    let SolveOutcome::Unknown(reason) = out else {
        panic!("expected an arity-unknown bail, got {out:?}");
    };
    assert!(reason.contains("arity unknown"), "{reason}");
}

// -- finite forAll/exists expansion -------------------------------------------

/// `forAll` over a bound scalar sequence expands to a conjunction: an
/// item pinned outside the predicate makes the whole assert
/// unsatisfiable.
#[test]
fn forall_over_bound_sequence_conjunction() {
    let Some(out) = outcome(
        "package P {
            attribute def Integer;
            attribute a : Integer;
            attribute b : Integer;
            attribute ps : Integer[0..*] = (a, b);
            assert constraint c { ps->forAll {in v; v > 0} & b == 0 - 3 }
        }",
    ) else {
        return;
    };
    assert_eq!(out, SolveOutcome::Unsatisfiable);
}

/// `exists` expands to a disjunction — satisfiable exactly when some
/// item can meet the predicate.
#[test]
fn exists_over_bound_sequence_disjunction() {
    let Some(out) = outcome(
        "package P {
            attribute def Integer;
            attribute a : Integer;
            attribute b : Integer;
            assert constraint c {
                (a, b)->exists {in v; v == 7} & a == 1 & b == 2
            }
        }",
    ) else {
        return;
    };
    assert_eq!(out, SolveOutcome::Unsatisfiable);
}

/// An unbound collection with an exact multiplicity skolemizes: `[4]`
/// instances, each chain through the parameter a per-instance variable.
#[test]
fn forall_skolemizes_bounded_multiplicity() {
    let Some(out) = outcome(
        "package P {
            attribute def Real;
            part def W {
                attribute r : Real;
                attribute d : Real;
            }
            part ws : W[4];
            assert constraint c { ws->forAll {in w; 2 * w.r < w.d} }
        }",
    ) else {
        return;
    };
    let SolveOutcome::Satisfiable(w) = out else {
        panic!("expected a witness over per-instance variables, got {out:?}");
    };
    // Four instances × two leaves, named by their skolem paths.
    assert_eq!(w.len(), 8, "{w:?}");
    assert!(w.iter().any(|(n, _)| n == "ws#1.r"), "{w:?}");
    assert!(w.iter().any(|(n, _)| n == "ws#4.d"), "{w:?}");
}

/// Two quantifiers over the same collection range over the *same*
/// instances — `forAll r == 3` and `exists r == 4` contradict.
#[test]
fn quantifiers_share_skolem_instances() {
    let Some(out) = outcome(
        "package P {
            attribute def Real;
            part def W {
                attribute r : Real;
            }
            part ws : W[2];
            assert constraint c {
                ws->forAll {in w; w.r == 3} & ws->exists {in w; w.r == 4}
            }
        }",
    ) else {
        return;
    };
    assert_eq!(out, SolveOutcome::Unsatisfiable);
}

/// A multiplicity over the expansion cap stays a bail, not a blowup.
#[test]
fn skolemization_respects_the_cap() {
    let Some(out) = outcome(
        "package P {
            attribute def Real;
            part def W {
                attribute r : Real;
            }
            part ws : W[64];
            assert constraint c { ws->forAll {in w; w.r > 0} }
        }",
    ) else {
        return;
    };
    let SolveOutcome::Unknown(reason) = out else {
        panic!("expected a cap bail, got {out:?}");
    };
    assert!(reason.contains("expansion cap"), "{reason}");
}
