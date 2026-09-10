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
