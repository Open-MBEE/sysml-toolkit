//! Interval-propagation tests. Unlike the solving tests, these need
//! no `z3` binary — propagation is a self-contained interval backend — so
//! the hand fixtures and the corpus ratchet always run.

use sysmlv2_model::check::ConstraintVerdict;
use sysmlv2_model::model::Model;
use sysmlv2_solve::{
    FeatureRange, PropagateConfig, PropagateOutcome, Propagation, propagate_constraints,
};

fn prop(src: &str) -> Propagation {
    let mut model = Model::new();
    let unit = model.add_source("t.sysml", src);
    assert!(
        unit.diagnostics.is_empty(),
        "fixture must parse clean: {:?}",
        unit.diagnostics
    );
    propagate_constraints(&model, &PropagateConfig::default())
}

fn range_of<'a>(p: &'a Propagation, feature: &str) -> &'a FeatureRange {
    p.ranges
        .iter()
        .find(|r| r.feature == feature)
        .unwrap_or_else(|| panic!("no range for `{feature}` in {:?}", p.ranges))
}

/// The single undecided constraint's propagation outcome.
fn sole_outcome(p: &Propagation) -> PropagateOutcome {
    let undecided: Vec<_> = p
        .constraints
        .iter()
        .filter(|c| matches!(c.verdict, ConstraintVerdict::Undecided(_)))
        .collect();
    assert_eq!(
        undecided.len(),
        1,
        "expected exactly one undecided constraint: {:?}",
        p.constraints
    );
    undecided[0]
        .propagate
        .clone()
        .expect("undecided ⇒ propagated")
}

/// Propagation must not decide a constraint from a value read *through
/// an unbound parameter*: a requirement definition's `subject` stands
/// for an argument bound later (`satisfy R by x`), and the `default`
/// its type declares is exactly what such an argument may override.
/// Inlining it would let the interval backend *prove* a verdict the
/// model never committed to, so the step stays a free variable and the
/// constraint stays undecided.
#[test]
fn a_subjects_defaults_do_not_decide_propagation() {
    let p = prop(
        "package P {
            part def Valve { attribute cycleSeconds default = 8; }
            requirement def CyclesFastEnough {
                subject unit : Valve;
                require constraint c { unit.cycleSeconds <= 2 }
            }
        }",
    );
    assert!(
        !matches!(sole_outcome(&p), PropagateOutcome::Violated),
        "{:?}",
        p.constraints
    );
}

#[test]
fn unknown_receiver_formulas_and_aliases_do_not_decide_propagation() {
    for (declaration, expression) in [
        ("ref part unit : Device;", "unit.enabled"),
        ("subject unit : Device;", "unit.computed"),
        (
            "subject unit : Device; ref part aliasUnit : Device = unit;",
            "aliasUnit.enabled",
        ),
        (
            "subject unit : Device;",
            "(if true ? unit else unit).enabled",
        ),
        ("subject unit : Device;", "unit.child.enabled"),
        ("in unit : Device;", "unit.enabled"),
    ] {
        let p = prop(&format!(
            "package P {{
                attribute def Boolean;
                part def Child {{ attribute enabled : Boolean default = false; }}
                part def Device {{
                    attribute enabled : Boolean default = false;
                    attribute computed : Boolean = enabled;
                    part child : Child;
                }}
                requirement def R {{
                    {declaration}
                    require constraint c {{ {expression} }}
                }}
            }}"
        ));
        assert!(
            matches!(
                sole_outcome(&p),
                PropagateOutcome::Undecided | PropagateOutcome::Unsupported(_)
            ),
            "{declaration} / {expression}: {:?}",
            p.constraints
        );
    }
}

#[test]
fn nested_unknown_receivers_do_not_share_solver_variables() {
    let p = prop(
        "package P {
            attribute def Real;
            part def Child { attribute value : Real default = 0; }
            part def Parent { part child : Child; }
            requirement def R {
                subject leftUnit : Parent;
                actor rightUnit : Parent;
                assert constraint c {
                    leftUnit.child.value >= 1 and rightUnit.child.value <= 0
                }
            }
        }",
    );
    assert!(
        matches!(sole_outcome(&p), PropagateOutcome::Unsupported(_)),
        "{:?}",
        p.constraints
    );
}

// -- narrowing ---------------------------------------------------------------

#[test]
fn lower_bound_narrows_to_half_line() {
    let p = prop(
        "package P {
            attribute def Real;
            attribute wingSpan : Real;
            assert constraint c { wingSpan >= 10 }
        }",
    );
    let r = range_of(&p, "wingSpan");
    assert_eq!(r.range, "[10, +∞]");
    assert!(r.narrowed);
    // Holds for every value in the narrowed domain.
    assert_eq!(sole_outcome(&p), PropagateOutcome::Satisfied);
}

#[test]
fn lower_bound_tightens_twice() {
    // A half-line's finite side keeps moving under a second, stronger
    // bound; a third, weaker bound is then settled by the tightened
    // domain rather than left undecided.
    let p = prop(
        "package P {
            attribute def Real;
            attribute x : Real;
            assert constraint open { x > 0 }
            assert constraint strong { x >= 1000 }
            assert constraint weak { x >= 500 }
        }",
    );
    assert_eq!(range_of(&p, "x").range, "[1000, +∞]");
    assert_eq!(outcome_of(&p, "weak"), PropagateOutcome::Satisfied);
}

#[test]
fn two_constraints_narrow_jointly() {
    // Separate asserted constraints over one shared feature contract the
    // same variable — the joint system's headline behavior.
    let p = prop(
        "package Tank {
            attribute def Real;
            attribute level : Real;
            assert constraint lo { level >= 5 }
            assert constraint hi { level <= 8 }
        }",
    );
    assert_eq!(range_of(&p, "level").range, "[5, 8]");
    assert!(range_of(&p, "level").narrowed);
}

/// Parse a `[lo, hi]` range string into `f64` endpoints (only finite ones).
fn bounds(r: &FeatureRange) -> (f64, f64) {
    let inner = r.range.trim_start_matches('[').trim_end_matches(']');
    let (lo, hi) = inner.split_once(", ").expect("a numeric range");
    (lo.parse().unwrap(), hi.parse().unwrap())
}

#[test]
fn product_backsolves_the_other_factor() {
    let p = prop(
        "package P {
            attribute def Real;
            attribute x : Real;
            attribute y : Real;
            assert constraint fix { x == 2 }
            assert constraint prod { x * y == 6 }
        }",
    );
    // `x` is pinned by a direct literal equality (no arithmetic → sharp);
    // `y` is *computed* through interval division, so it carries the
    // sound one-ulp outward fuzz that a real value picks up — the interval
    // must still tightly enclose the true factor 3.
    assert_eq!(range_of(&p, "x").range, "[2, 2]");
    let (lo, hi) = bounds(range_of(&p, "y"));
    assert!(
        lo <= 3.0 && 3.0 <= hi && hi - lo < 1e-6,
        "y should tightly enclose 3, got {}",
        range_of(&p, "y").range
    );
}

// -- empty-domain proofs -----------------------------------------------------

#[test]
fn contradiction_is_unsatisfiable() {
    let p = prop(
        "package P {
            attribute def Integer;
            attribute x : Integer;
            assert constraint c { x > 5 & x < 4 }
        }",
    );
    assert_eq!(sole_outcome(&p), PropagateOutcome::Unsatisfiable);
    assert_eq!(range_of(&p, "x").range, "∅");
}

#[test]
fn joint_contradiction_across_constraints_is_unsatisfiable() {
    let p = prop(
        "package P {
            attribute def Real;
            attribute t : Real;
            assert constraint lo { t >= 9 }
            assert constraint hi { t <= 3 }
        }",
    );
    // Both asserted members are proved unsatisfiable by the empty domain.
    for c in &p.constraints {
        if matches!(c.verdict, ConstraintVerdict::Undecided(_)) {
            assert_eq!(c.propagate, Some(PropagateOutcome::Unsatisfiable));
        }
    }
}

// -- division through zero ---------------------------------------------------

#[test]
fn division_by_a_zero_straddling_divisor_stays_wide() {
    // The divisor's domain contains 0, so `6 / y` carries no information —
    // `x` must not be (unsoundly) narrowed, and nothing proves unsat.
    let p = prop(
        "package P {
            attribute def Real;
            attribute x : Real;
            attribute y : Real;
            assert constraint yb1 { y >= -1 }
            assert constraint yb2 { y <= 1 }
            assert constraint q { x == 6 / y }
        }",
    );
    assert_eq!(range_of(&p, "x").range, "[−∞, +∞]");
    assert!(!range_of(&p, "x").narrowed);
    // `y` is still bounded by its own constraints, not emptied.
    assert_eq!(range_of(&p, "y").range, "[-1, 1]");
}

/// The propagation outcome of the constraint declared as `name`.
fn outcome_of(p: &Propagation, name: &str) -> PropagateOutcome {
    p.constraints
        .iter()
        .find(|c| c.name.as_deref() == Some(name))
        .unwrap_or_else(|| panic!("no constraint `{name}` in {:?}", p.constraints))
        .propagate
        .clone()
        .unwrap_or_else(|| panic!("`{name}` was not propagated"))
}

#[test]
fn remainder_by_a_possibly_zero_divisor_stays_undecided() {
    // `y ∈ [0, 5]` admits 0, and `x % 0` is an SMT total-function free
    // value — the remainder bounds nothing, so `m` must stay undecided
    // rather than being (unsoundly) proved violated.
    let p = prop(
        "package P {
            attribute def Integer;
            attribute x : Integer;
            attribute y : Integer;
            assert constraint yb1 { y >= 0 }
            assert constraint yb2 { y <= 5 }
            assert constraint m { x % y == 100 }
        }",
    );
    assert_eq!(outcome_of(&p, "m"), PropagateOutcome::Undecided);
    assert_eq!(range_of(&p, "y").range, "[0, 5]");
    assert_eq!(range_of(&p, "x").range, "[−∞, +∞]");
}

#[test]
fn division_by_an_exactly_zero_divisor_constrains_nothing() {
    // With `y` pinned to 0, `6 / y` is a free value: the equality must
    // not contract the (literal) dividend to a contradiction — that
    // would bottom the pass out as a false unsat and stop `xb` from
    // ever narrowing `x`.
    let p = prop(
        "package P {
            attribute def Real;
            attribute x : Real;
            attribute y : Real;
            assert constraint yz { y == 0 }
            assert constraint q { x == 6 / y }
            assert constraint xb { x >= 5 }
        }",
    );
    assert_eq!(outcome_of(&p, "q"), PropagateOutcome::Undecided);
    assert_eq!(range_of(&p, "y").range, "[0, 0]");
    assert_eq!(range_of(&p, "x").range, "[5, +∞]");
}

#[test]
fn backward_division_keeps_zero_in_the_divisor() {
    // `x / y == 2` with x = 4 suggests y = 2, but y = 0 also satisfies
    // it under total division (`4 / 0` is free) — the contraction must
    // keep 0 in `y`'s domain while still bounding it near 2 above.
    let p = prop(
        "package P {
            attribute def Real;
            attribute x : Real;
            attribute y : Real;
            assert constraint xf { x == 4 }
            assert constraint q { x / y == 2 }
        }",
    );
    assert_eq!(range_of(&p, "x").range, "[4, 4]");
    let (lo, hi) = bounds(range_of(&p, "y"));
    assert!(
        lo <= 0.0,
        "0 escaped the divisor: {}",
        range_of(&p, "y").range
    );
    assert!(
        (2.0..2.0001).contains(&hi),
        "upper bound should sit at ~2: {}",
        range_of(&p, "y").range
    );
}

// -- sequence intrinsics ----------------------------------------------------

#[test]
fn ranges_narrow_through_a_sum_fold() {
    // `sum` lowers to a plain `+` chain, so the interval backend rides
    // the same term: x = a + b with a = 2 and b ∈ [3, 4] pins x near
    // [5, 6] (computed endpoints carry the sound one-ulp fuzz).
    let p = prop(
        "package P {
            attribute def Real;
            attribute x : Real;
            attribute a : Real;
            attribute b : Real;
            attribute ps : Real[0..*] = (a, b);
            assert constraint xs { x == sum(ps) }
            assert constraint af { a == 2 }
            assert constraint blo { b >= 3 }
            assert constraint bhi { b <= 4 }
        }",
    );
    let (lo, hi) = bounds(range_of(&p, "x"));
    assert!(
        lo <= 5.0 && 5.0 - lo < 1e-9 && hi >= 6.0 && hi - 6.0 < 1e-9,
        "x should tightly enclose [5, 6]: {}",
        range_of(&p, "x").range
    );
    assert!(range_of(&p, "x").narrowed);
}

#[test]
fn max_fold_pins_the_result() {
    // `max` lowers to a chain of conditionals whose steps are named by
    // hidden auxiliaries: the result narrows like any other feature, and
    // the auxiliaries never surface as ranges or referenced features.
    // The narrowing itself held before the auxiliaries existed — what
    // this pins is that naming the steps did not change the answer, and
    // that nothing internal leaks out. The cost is pinned separately by
    // the forty-item test below.
    let p = prop(
        "package P {
            attribute def Integer;
            attribute hi : Integer;
            attribute a : Integer;
            attribute b : Integer;
            assert constraint m { hi == max((a, b)) }
            assert constraint af { a == 2 }
            assert constraint bf { b == 7 }
        }",
    );
    assert_eq!(range_of(&p, "hi").range, "[7, 7]");
    let declared = ["hi", "a", "b"];
    assert!(
        p.ranges
            .iter()
            .all(|r| declared.contains(&r.feature.as_str())),
        "{:?}",
        p.ranges
    );
    for c in &p.constraints {
        assert!(
            c.features.iter().all(|f| declared.contains(&f.as_str())),
            "{:?}",
            c.features
        );
    }
}

#[test]
fn max_over_forty_items_stays_linear() {
    // Each fold step references the previous step's auxiliary, so a
    // 41-item extremum is a 41-step chain — not a term doubling per item.
    let items: Vec<String> = (1..=40).map(|i| i.to_string()).collect();
    let start = std::time::Instant::now();
    let p = prop(&format!(
        "package P {{
            attribute def Integer;
            attribute x : Integer;
            attribute y : Integer;
            assert constraint m {{ x == max(({}, y)) }}
            assert constraint yf {{ y == 45 }}
        }}",
        items.join(", ")
    ));
    assert_eq!(range_of(&p, "x").range, "[45, 45]");
    assert!(
        start.elapsed() < std::time::Duration::from_secs(5),
        "fold took {:?}",
        start.elapsed()
    );
}

#[test]
fn separate_units_each_see_their_own_enumerations() {
    // The enumeration literal index is derived once for the whole model
    // and shared by every unit's translation: each unit must still reach
    // its own enumeration, and literals of the same position in different
    // enumerations must stay apart. This is a property of the sharing,
    // not of the caching — a stale index would need a model that changed
    // after the index was built, which the resolved model does not allow.
    let mut model = Model::new();
    for (name, src) in [
        (
            "a.sysml",
            "package A {
                enum def Phase { init; run; halt; }
                attribute p : Phase;
                assert constraint ap { p == Phase::halt }
            }",
        ),
        (
            "b.sysml",
            "package B {
                enum def Colour { red; green; blue; }
                attribute c : Colour;
                assert constraint bc { c != Colour::red }
            }",
        ),
    ] {
        let unit = model.add_source(name, src);
        assert!(
            unit.diagnostics.is_empty(),
            "fixture must parse clean: {:?}",
            unit.diagnostics
        );
    }
    let p = propagate_constraints(&model, &PropagateConfig::default());
    assert_eq!(range_of(&p, "p").range, "{halt}");
    assert_eq!(range_of(&p, "c").range, "{green, blue}");
    assert_eq!(outcome_of(&p, "ap"), PropagateOutcome::Satisfied);
    assert_eq!(outcome_of(&p, "bc"), PropagateOutcome::Satisfied);
}

// -- finite quantifier expansion --------------------------------------------

#[test]
fn ranges_narrow_through_a_skolemized_forall() {
    // `ws->forAll {in w; …}` over an exact `[2]` multiplicity expands to
    // a conjunction over per-instance variables — propagation narrows
    // each instance's feature like any other conjunct.
    let p = prop(
        "package P {
            attribute def Real;
            part def W {
                attribute r : Real;
            }
            part ws : W[2];
            assert constraint c { ws->forAll {in w; w.r >= 3 & w.r <= 5} }
        }",
    );
    for feature in ["ws#1.r", "ws#2.r"] {
        assert_eq!(range_of(&p, feature).range, "[3, 5]");
        assert!(range_of(&p, feature).narrowed);
    }
}

// -- enumerations ------------------------------------------------------------

#[test]
fn inequality_removes_one_enum_literal() {
    let p = prop(
        "package P {
            enum def Phase { halt; mid; init; }
            attribute c : Phase;
            assert constraint c1 { c != Phase::mid }
        }",
    );
    let r = range_of(&p, "c");
    assert!(r.range.contains("halt") && r.range.contains("init"));
    assert!(!r.range.contains("mid"), "mid not excluded: {}", r.range);
}

#[test]
fn enum_literals_past_position_128_stay_distinct() {
    // A wide enumeration: pinning the 130th literal must narrow to that
    // literal alone, and excluding the 2nd must not empty the domain
    // (the two positions are distinct members, not aliases).
    let lits: String = (1..=130).map(|i| format!("l{i}; ")).collect();
    let p = prop(&format!(
        "package P {{
            enum def Wide {{ {lits} }}
            attribute c : Wide;
            assert constraint pin {{ c == Wide::l130 }}
            assert constraint apart {{ c != Wide::l2 }}
        }}"
    ));
    assert_eq!(range_of(&p, "c").range, "{l130}");
    assert_eq!(outcome_of(&p, "pin"), PropagateOutcome::Satisfied);
    assert_eq!(outcome_of(&p, "apart"), PropagateOutcome::Satisfied);
}

// -- partial conjunctions ----------------------------------------------------

#[test]
fn conjunction_degrades_per_conjunct() {
    // One conjunct outside the fragment (mixed opaque units) must not
    // silence its siblings: the translatable conjunct still narrows its
    // feature; the constraint itself stays outside the fragment with
    // the bail reason.
    let p = prop(
        "package P {
            attribute def Real;
            attribute u; attribute v;
            attribute margin : Real;
            attribute mix : Real;
            assert constraint c { margin >= 2100 and mix + 1 ['u'] > 1 ['v'] }
        }",
    );
    let r = range_of(&p, "margin");
    assert_eq!(r.range, "[2100, +∞]");
    assert!(r.narrowed);
    match sole_outcome(&p) {
        PropagateOutcome::Unsupported(m) => {
            assert!(m.contains("no unit conversion"), "unexpected reason: {m}")
        }
        o => panic!("expected the bail reason to survive, got {o:?}"),
    }
}

#[test]
fn partial_conjunction_still_refutes() {
    // Translated conjuncts that contradict each other (an empty joint
    // domain) prove the conjunction unsatisfiable even though a
    // sibling stayed outside the fragment.
    let p = prop(
        "package P {
            attribute def Real;
            attribute u; attribute v;
            attribute margin : Real;
            attribute mix : Real;
            assert constraint c {
                margin >= 5 and margin <= 4 and mix + 1 ['u'] > 1 ['v']
            }
        }",
    );
    assert_eq!(sole_outcome(&p), PropagateOutcome::Unsatisfiable);
}

// -- corpus ratchet ----------------------------------------------------------

/// Over the full corpus + standard library, propagation must never prove an
/// asserted constraint `Violated` or `Unsatisfiable` (a conforming corpus is
/// consistent). This is the soundness ratchet — the alarming directions must
/// stay empty — and it needs no solver.
#[test]
fn corpus_no_false_violations() {
    let mut model = Model::new();
    model
        .load_library_dir(&sysmlv2_testkit::library_dir())
        .unwrap();
    for f in sysmlv2_testkit::user_files() {
        let src = std::fs::read_to_string(&f).unwrap();
        model.add_source(f.file_name().unwrap().to_string_lossy().into_owned(), &src);
    }
    let p = propagate_constraints(&model, &PropagateConfig::default());
    for c in &p.constraints {
        if !c.asserted {
            continue;
        }
        if let Some(PropagateOutcome::Violated | PropagateOutcome::Unsatisfiable) = &c.propagate {
            panic!(
                "propagation flagged asserted `{:?}` ({}) as {:?} in {}",
                c.name,
                c.element_type,
                c.propagate,
                model.units()[c.unit].name
            );
        }
    }
}

#[test]
fn decimal_bounds_stay_exact() {
    // Bounds spelled as decimal literals contract the domain to exactly
    // those decimals — not to their nearest doubles.
    let p = prop(
        "package Mass {
            attribute def Real;
            attribute airframeKg : Real;
            attribute batteryKg : Real;
            assert constraint airframeRange { airframeKg >= 0.8 and airframeKg <= 1.1 }
            assert constraint batteryRange { batteryKg >= 0.2 and batteryKg <= 0.3 }
        }",
    );
    let a = range_of(&p, "airframeKg");
    assert_eq!(a.range, "[0.8, 1.1]");
    assert_eq!(a.range_approx, "[0.8, 1.1]");
    let b = range_of(&p, "batteryKg");
    assert_eq!(b.range, "[0.2, 0.3]");
    assert_eq!(b.range_approx, "[0.2, 0.3]");
}

#[test]
fn non_terminating_bounds_print_as_fractions_and_hint_as_decimals() {
    let p = prop(
        "package Ratio {
            attribute def Real;
            attribute share : Real;
            assert constraint c { share >= 1 / 3 and share <= 2 / 3 }
        }",
    );
    let r = range_of(&p, "share");
    assert_eq!(r.range, "[1/3, 2/3]");
    assert_eq!(r.range_approx, "[≈0.3333333333333333, ≈0.6666666666666666]");
}
