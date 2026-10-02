//! The pairing a redefining feature's body inherits members through
//! (`positional_redefinition_targets`, read off one feature's heritage)
//! agrees with the implied `Redefinition` relationships the model
//! materializes, for every declared parameter and end of the library and
//! the corpus: each side's targets are the other's, or redefined through
//! them (the planner drops an edge another path already reaches — an
//! explicit `:>>` of the same feature, a result inherited through a
//! redefined one). An expression's parameters, which pair with the
//! function it invokes rather than with a written general, stay out; so
//! do the library features the planner alone pairs, through bases the
//! heritage does not read: an accept's payload and receiver, some
//! connection usages' binary-link ends, and succession ends. Binary
//! Connection/Interface definitions' owned ends now agree with lookup.
//! The planner also counts a membership a general imports as one of its
//! slots, which the heritage reading does not; no corpus model exercises
//! that, so a user-model disagreement there would be the expected one.
use std::collections::{BTreeSet, HashSet};

use sysmlv2_parser::json::{ElementRef, Reference, ResolvedModel};
use sysmlv2_parser::model::Model;

/// Implied targets only the planner pairs — library features reached
/// through bases the heritage does not read — measured over the library
/// and the corpus.
// 81 accept payloads + 29 accept receivers + 4 connection-usage ends.
// Binary definition ancestry removes 70 former exceptions: 68 implied
// targets now agree directly, and two Causation targets now resolve
// explicitly, making their former implied edges redundant.
const TOLERATED_LIBRARY_ONLY: usize = 114;
// Corrected succession specialization adds these end pairings. Keep them
// separate so their addition cannot hide a change in the older families.
const SUCCESSION_LIBRARY_ONLY: usize = 782;

fn redefinition_targets(
    r: &mut ResolvedModel,
    feature: ElementRef,
    implied: bool,
) -> Vec<ElementRef> {
    let mut out = r.positional_redefinition_targets(feature);
    let relationships: Vec<ElementRef> = if implied {
        r.implied_relationships(feature)
    } else {
        r.owned_relationships(feature)
    };
    for relationship in relationships {
        if r.element_type(relationship) != "Redefinition" {
            continue;
        }
        for target in r.relationship_ends(relationship).1 {
            if let Reference::Element(target) = target {
                out.push(target);
            }
        }
    }
    out
}

/// Everything `start` reaches through written, positional and implied
/// redefinitions.
fn closure(r: &mut ResolvedModel, start: &BTreeSet<ElementRef>) -> HashSet<ElementRef> {
    let mut seen: HashSet<ElementRef> = start.iter().copied().collect();
    let mut stack: Vec<ElementRef> = start.iter().copied().collect();
    while let Some(feature) = stack.pop() {
        for implied in [false, true] {
            for target in redefinition_targets(r, feature, implied) {
                if seen.insert(target) {
                    stack.push(target);
                }
            }
        }
    }
    seen
}

#[test]
fn corpus_positional_targets_agree_with_the_implied_redefinitions() {
    let mut model = Model::new();
    model
        .load_library_dir(&sysmlv2_testkit::library_dir())
        .expect("library");
    for f in sysmlv2_testkit::user_files() {
        let src = std::fs::read_to_string(&f).unwrap();
        model.add_source(
            sysmlv2_testkit::relative_source_name(&sysmlv2_testkit::corpus_root(), f.as_path()),
            &src,
        );
    }
    let mut r = ResolvedModel::build(&model);
    let mut checked = 0;
    let mut tolerated = 0;
    let mut succession_only = 0;
    let mut differ = Vec::new();
    for feature in r.elements().collect::<Vec<_>>() {
        let properties = r.element_properties(feature);
        let is_end = properties.get("isEnd").and_then(|v| v.as_bool()) == Some(true);
        if !(is_end || r.is_parameter(feature)) {
            continue;
        }
        let Some(owner) = r.owner(feature) else {
            continue;
        };
        if r.inheritance_incomplete(owner, true) || r.element_type(owner).ends_with("Expression") {
            continue;
        }
        let heritage: BTreeSet<_> = r
            .positional_redefinition_targets(feature)
            .into_iter()
            .collect();
        let mut implied = BTreeSet::new();
        for relationship in r.implied_relationships(feature) {
            if r.element_type(relationship) != "Redefinition" {
                continue;
            }
            for target in r.relationship_ends(relationship).1 {
                if let Reference::Element(target) = target {
                    implied.insert(target);
                }
            }
        }
        if heritage.is_empty() && implied.is_empty() {
            continue;
        }
        checked += 1;
        let explicit: BTreeSet<_> = redefinition_targets(&mut r, feature, false)
            .into_iter()
            .collect();
        let from_heritage = closure(&mut r, &heritage.union(&explicit).copied().collect());
        let from_implied = closure(&mut r, &implied.union(&explicit).copied().collect());
        let heritage_only: Vec<_> = heritage
            .iter()
            .filter(|t| !from_implied.contains(t))
            .copied()
            .collect();
        let (library_only, implied_only): (Vec<_>, Vec<_>) = implied
            .iter()
            .filter(|t| !from_heritage.contains(t))
            .copied()
            .partition(|&t| r.is_library_element(t));
        tolerated += library_only.len();
        if matches!(r.element_type(owner), "Succession" | "SuccessionAsUsage") {
            succession_only += library_only
                .iter()
                .filter(|&&target| {
                    matches!(
                        r.element_qualified_name(target).as_deref(),
                        Some(
                            "Occurrences::happensBeforeLinks::earlierOccurrence"
                                | "Occurrences::happensBeforeLinks::laterOccurrence"
                        )
                    )
                })
                .count();
        }
        if !heritage_only.is_empty() || !implied_only.is_empty() {
            let name = r.element_qualified_name(feature).unwrap_or_default();
            let spell = |r: &mut ResolvedModel, set: &[ElementRef]| {
                set.iter()
                    .map(|&t| r.element_qualified_name(t).unwrap_or_default())
                    .collect::<Vec<_>>()
            };
            let (h, i) = (spell(&mut r, &heritage_only), spell(&mut r, &implied_only));
            differ.push(format!(
                "{} {name}: heritage only {h:?}, implied only {i:?}",
                r.element_type(feature)
            ));
        }
    }
    eprintln!(
        "checked {checked} positional features, tolerated {tolerated} library-only implied targets"
    );
    assert!(checked > 1500, "only {checked} positional features");
    assert!(
        differ.is_empty(),
        "{} differ:\n{}",
        differ.len(),
        differ.join("\n")
    );
    // The library pairings the planner alone makes, pinned so that a
    // heritage reading that stops making ones it does make is seen, and a
    // planner that stops making one of these is too.
    assert_eq!(
        tolerated - succession_only,
        TOLERATED_LIBRARY_ONLY,
        "library-only implied targets"
    );
    assert_eq!(
        succession_only, SUCCESSION_LIBRARY_ONLY,
        "succession library-only implied targets"
    );
}
