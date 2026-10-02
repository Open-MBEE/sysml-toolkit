//! Corpus ratchet for the solving stage: over the full corpus +
//! standard library, the constraints the evaluator leaves undecided must
//! solve to exactly the recorded outcome counts — `valid` and
//! `unsatisfiable` must stay 0 on a conforming corpus (a nonzero
//! `unsatisfiable` would mean we prove a published model self-
//! contradictory). Changes in satisfiable/unknown counts require an
//! explained translation improvement or soundness correction. Skips when
//! no `z3` is on PATH.

use sysmlv2_model::model::Model;
use sysmlv2_solve::{SolveOutcome, SolverConfig, solve_constraints, z3_version};

#[test]
fn corpus_solve_ratchet() {
    let cfg = SolverConfig::default();
    if z3_version(&cfg).is_err() {
        eprintln!("skipping corpus_solve_ratchet: no z3 on PATH");
        return;
    }
    let mut model = Model::new();
    model
        .load_library_dir(&sysmlv2_testkit::library_dir())
        .unwrap();
    for f in sysmlv2_testkit::user_files() {
        let src = std::fs::read_to_string(&f).unwrap();
        // Distinct source paths can share a basename; keep their identity seeds distinct.
        model.add_source(
            sysmlv2_testkit::relative_source_name(&sysmlv2_testkit::corpus_root(), f.as_path()),
            &src,
        );
    }
    let solved = solve_constraints(&model, &cfg).unwrap();
    let (mut valid, mut sat, mut unsat, mut unknown) = (0, 0, 0, 0);
    for s in &solved {
        match &s.solve {
            None => {}
            Some(SolveOutcome::Valid) => {
                valid += 1;
                eprintln!(
                    "VALID: {} — {:?} ({})",
                    model.units()[s.unit].name,
                    s.name,
                    s.element_type
                );
            }
            Some(SolveOutcome::Satisfiable(_)) => sat += 1,
            Some(SolveOutcome::Unsatisfiable) => {
                unsat += 1;
                eprintln!(
                    "UNSAT: {} — {:?} ({})",
                    model.units()[s.unit].name,
                    s.name,
                    s.element_type
                );
            }
            Some(SolveOutcome::Unknown(_)) => unknown += 1,
            // A conclusion this count does not know would silently skew
            // the ratchet.
            Some(other) => panic!("unhandled solve conclusion: {other:?}"),
        }
    }
    // The 1 valid is genuine and verified by hand: `Turbojet Stage
    // Analysis.sysml` binds `'Static Pressure' = 'Ideal Gas Law'(…)` and
    // then asserts `'Static Pressure' == 'Ideal Gas Law'(…)` with the
    // identical arguments — through calculation inlining both sides are
    // one term, a tautology by construction. Valid (⇒ satisfied) is a
    // benign strengthening on a conforming corpus; UNSAT (⇒ violated)
    // is the alarming direction and must stay 0.
    // 56/23 → 59/30 when asserted constraints with *inherited* bodies
    // entered the undecided pool: the solver produces
    // witnesses for three of the ten, the rest stay unknown.
    // 59/30 → 64/25 with the sequence intrinsics (sum over bound
    // sequence arguments — the Mass-Roll-up family); the ten remaining
    // sum sites are def-level `[0..*]` parameters with no bound value,
    // the honest arity-unknown boundary.
    // 64/25 → 65/24 with the quantifier expansion (7b's variant
    // selection constraint — `rearWheelChoice->forAll` skolemizes over
    // the redefined `[2]` multiplicity into variant-sorted instances);
    // 15_05's DiscBrakeConstraint also expands but lands in the honest
    // approx-Unknown bucket (its `outerDiameter` leaf is a
    // bracket-over-quantity value, outside the fragment).
    // 65/24 → 65/27 when unbound-feature cardinality stopped
    // fabricating: three `(1..size(xs)-1)->forAll` bodies
    // over unbound `[0..*]` collections used to evaluate vacuously true
    // (fabricated size 1 emptied the range) and never reached the
    // solver; they now enter the undecided pool, where the quantified
    // size-dependent bodies are outside the decidable fragment.
    // 65/27 → 63/29 when nested unknown receiver paths stopped sharing
    // declaration-level variables: `device.battery.power` in User Keyword
    // Example and `generator.generateTorque.torque` in 12b-Allocation-1
    // now stay unknown. Supporting them again requires preserving each
    // receiver path in the solver's variable identity.
    // 63/29 → 61/32 with effective cardinality and guarded collection
    // translation: one scenario's inherited unbound samples stop making
    // its size-dependent quantifier vacuously true (enters unknown).
    // An unbound componentMasses redefinition inherits [0..*], so it
    // cannot supply one scalar summand; an autoPort with an unresolved
    // redefinition likewise cannot supply a known singleton. Both lose
    // fabricated scalar witnesses. Exact expanded variant instances
    // still solve, independently of their root collection's multiplicity.
    // 61/32 → 37/58 with normative defaults and inherited subsettings:
    // 24 scalar witnesses depended on explicitly subsetted [*] quantities,
    // generic parameters, non-structural variation usages, or package-owned
    // receivers whose cardinality is not one. Two formerly static verdicts
    // likewise become unknown. Requirement/case subjects retain their actual
    // inherited [1] through complete supported positional redefinitions.
    assert_eq!(
        (valid, sat, unsat, unknown),
        (1, 37, 0, 58),
        "solve ratchet moved — unsatisfiable must stay 0 on the \
         conforming corpus; satisfiable/unknown changes require an \
         explained translation improvement or soundness correction"
    );
}
