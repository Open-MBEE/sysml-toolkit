//! The outcomes a settled build resolved its references to, for the next
//! build of the same units to start from.
//!
//! A language server builds a session again after every edit, and nearly
//! every reference is as it was. Reference resolution repeats its pass
//! against the lookup graph of the previous pass's outcomes until a pass
//! changes none, starting from a pass over nothing; started instead from
//! the outcomes the previous build settled on, the loop confirms them in
//! one pass where the edit changed none, and otherwise carries the change
//! through as many passes as it takes, which is what the loop does after
//! its first pass anyway.
//!
//! The outcomes are kept per unit, under the unit's root path, and per
//! reference in pending order, each with a fingerprint of the reference —
//! its position within the unit, key, spelling, scope, exclusion, modes
//! and chain — so that a reference lowered where and as it was takes its
//! outcome, and any other — an edited reference, or every reference after
//! an inserted or removed element — starts unresolved. An outcome names
//! its target by the identity the element had before user identities were
//! assigned — the ownership-path identity, which a unit lowered the same
//! way assigns the same — or by its library identity; a target no row of
//! the next build carries starts unresolved. The seed is a guess the first
//! pass verifies: every pass resolves every reference, so a wrong or
//! missing seed costs passes, never answers. Nor can a seed change what an
//! acyclic model settles on, since each pass's outcomes follow from the
//! graph of the previous pass's and the chain of what depends on what ends
//! at references resolved lexically; a cyclic model, which the checks
//! report, could settle on a fixed point the seed chose as it could on one
//! the first pass chose, and a seeded loop that does not settle within its
//! passes starts over cold.

use super::{Builder, PendingRef, id_ref};
use crate::libcache::Fnv;
use serde_json::json;
use std::collections::HashMap;
use std::sync::Arc;
use uuid::Uuid;

/// The outcomes a settled build's references resolved to, per unit, for
/// the next build of the same units to start from (see the module).
#[derive(Clone, Default)]
pub struct SettledOutcomes {
    units: HashMap<String, SettledUnit>,
}

#[derive(Clone)]
struct SettledUnit {
    /// Each reference in pending order: its fingerprint — position within
    /// the unit, key, spelling, scope, exclusion, modes and chain — and its
    /// outcome, the identity of its target before user identities were
    /// assigned, or `None` unresolved.
    refs: Vec<(u64, Option<Uuid>)>,
}

impl SettledOutcomes {
    /// How many units' outcomes are kept.
    pub fn unit_count(&self) -> usize {
        self.units.len()
    }
}

/// The outcomes seeded into a build's pending references, in pending
/// order: `None` for a reference without a kept outcome.
#[derive(Clone)]
pub(super) struct Seed {
    outcomes: Vec<Option<Option<Uuid>>>,
}

#[cfg(test)]
thread_local! {
    static SEEDS_ABANDONED: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}
/// How many seeded loops did not settle and started over cold.
#[cfg(test)]
pub(crate) fn seeds_abandoned() -> usize {
    SEEDS_ABANDONED.with(|c| c.get())
}
#[cfg(test)]
pub(super) fn note_seed_abandoned() {
    SEEDS_ABANDONED.with(|c| c.set(c.get() + 1));
}
#[cfg(not(test))]
pub(super) fn note_seed_abandoned() {}

#[cfg(test)]
thread_local! {
    /// A test's budget of seeded passes, in place of the loop's own.
    static SEEDED_PASSES: std::cell::Cell<Option<usize>> = const { std::cell::Cell::new(None) };
}
/// The passes a seeded loop may take before starting over cold.
pub(super) fn seeded_passes() -> usize {
    #[cfg(test)]
    if let Some(passes) = SEEDED_PASSES.with(|c| c.get()) {
        return passes;
    }
    super::REDO_PASSES + 1
}
#[cfg(test)]
pub(crate) fn set_seeded_passes(passes: Option<usize>) {
    SEEDED_PASSES.with(|c| c.set(passes));
}

impl Builder {
    /// The pending references by unit, in pending order: each unit's root
    /// path, and each of its references' index and fingerprint.
    fn pending_by_unit(&self, pending: &[PendingRef]) -> Vec<(String, Vec<(usize, u64)>)> {
        let mut units: Vec<(String, Vec<(usize, u64)>)> = Vec::new();
        let mut current: Option<(usize, usize, usize)> = None;
        let mut spelled = String::new();
        for (i, p) in pending.iter().enumerate() {
            // the unit the reference's element was lowered in
            let unit = match self.unit_starts.binary_search_by_key(&p.elem, |&(e, _)| e) {
                Ok(u) => u,
                Err(0) => 0,
                Err(u) => u - 1,
            };
            if current.is_none_or(|(u, ..)| u != unit) {
                let start = self.unit_starts[unit].0;
                let scope_start = self.scope_starts.get(unit).map_or(0, |&(s, _)| s);
                current = Some((unit, start, scope_start));
                units.push((self.elements[start].path.clone(), Vec::new()));
            }
            let (_, start, scope_start) = current.unwrap();
            let mut hash = Fnv::new();
            hash.update(&(p.elem.wrapping_sub(start) as u64).to_le_bytes());
            hash.update(p.key.as_bytes());
            hash.update(&[0]);
            spelled.clear();
            p.qn.write_ref_string(&mut spelled);
            hash.update(spelled.as_bytes());
            hash.update(&[0]);
            hash.update(&(p.scope.wrapping_sub(scope_start) as u64).to_le_bytes());
            hash.update(
                &(p.exclude.map_or(u64::MAX, |e| e.wrapping_sub(start) as u64)).to_le_bytes(),
            );
            hash.update(&[u8::from(p.declared_only), u8::from(p.spec_idx.is_some())]);
            for link in p.chain.iter().flatten() {
                spelled.clear();
                link.write_ref_string(&mut spelled);
                hash.update(spelled.as_bytes());
                hash.update(&[0]);
            }
            units.last_mut().unwrap().1.push((i, hash.finish()));
        }
        units
    }

    /// Keep the outcomes this build settled on, for the next build of the
    /// same units to start from, when asked to.
    pub(super) fn record_settled(&mut self, pending: &[PendingRef]) {
        if !self.keep_settled {
            return;
        }
        // An array key's references append in pending order: the n-th
        // reference of an element's key reads the array's n-th entry.
        let mut appended: HashMap<(usize, &str), usize> = HashMap::new();
        let mut units = HashMap::new();
        for (path, refs) in self.pending_by_unit(pending) {
            let refs = refs
                .iter()
                .map(|&(i, fingerprint)| {
                    let p = &pending[i];
                    let props = &self.elements[p.elem].props;
                    let outcome = match p.key.split_once('#') {
                        Some((base, _)) => {
                            let n = appended.entry((p.elem, base)).or_insert(0);
                            let entry = props
                                .get(base)
                                .and_then(|v| v.as_array()?.get(*n)?.as_reference());
                            *n += 1;
                            entry
                        }
                        None => props.get(&p.key).and_then(|v| v.as_reference()),
                    };
                    (fingerprint, outcome)
                })
                .collect();
            units.insert(path, SettledUnit { refs });
        }
        self.settled = Some(Arc::new(SettledOutcomes { units }));
    }

    /// The seed `settled` gives this build's pending references: the kept
    /// outcome of every reference lowered where and as its unit's reference
    /// at the same position was. `None` when no reference takes one.
    pub(super) fn seed_from(
        &self,
        pending: &[PendingRef],
        settled: &SettledOutcomes,
    ) -> Option<Seed> {
        let mut outcomes = vec![None; pending.len()];
        let mut seeded = false;
        for (path, refs) in self.pending_by_unit(pending) {
            let Some(unit) = settled.units.get(&path) else {
                continue;
            };
            for (k, &(i, fingerprint)) in refs.iter().enumerate() {
                if let Some(&(kept, outcome)) = unit.refs.get(k) {
                    if kept == fingerprint {
                        outcomes[i] = Some(outcome);
                        seeded = true;
                    }
                }
            }
        }
        seeded.then_some(Seed { outcomes })
    }

    /// Write the seed as the outcomes a pass would have written: a kept
    /// target some row of this build carries, as a reference to that row;
    /// anything else as unresolved.
    pub(super) fn apply_seed(&mut self, pending: &[PendingRef], seed: &Seed) {
        // this build's rows by id, and the frozen rows through the kept table
        let frozen = self
            .prefix_ids
            .clone()
            .filter(|ids| ids.len() == self.lib_boundary && self.elements.base_untouched());
        let start = if frozen.is_some() {
            self.lib_boundary
        } else {
            0
        };
        let own: crate::layered::IdMap<Uuid, usize> = self
            .elements
            .iter()
            .enumerate()
            .skip(start)
            .map(|(i, e)| (e.id, i))
            .collect();
        for p in pending {
            if let Some((key, _)) = p.key.split_once('#') {
                self.elements[p.elem].props.insert(key, json!([]));
            }
        }
        for (p, outcome) in pending.iter().zip(&seed.outcomes) {
            let target = outcome
                .flatten()
                .and_then(|id| own.get(&id).or_else(|| frozen.as_ref()?.get(&id)).copied());
            if let Some(si) = p.spec_idx {
                self.record_spec_outcome(si, target, &[]);
            }
            let value = match target {
                Some(target) => id_ref(self.elements[target].id),
                None => crate::properties::Atom::from(json!({ "@ref": p.qn.to_ref_string() })),
            };
            self.set_pending_value(p.elem, &p.key, value);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::super::recorded_lookup::settled_passes;
    use super::super::{ResolvedModel, passes};
    use super::*;
    use crate::model::Model;
    use crate::prepared::PreparedLibrary;

    const LIBRARY: &str = "package Lib { part def Base { attribute mass; attribute parts; } part def Other { attribute mass; } }";
    const A: &str = "package A { part def Car :> Lib::Base { attribute :>> mass; } part car : Car { attribute :>> mass = 1; } }";
    const B: &str = "package B { import A::*; part def Truck :> Car { attribute :>> mass = 2; } part truck : Truck { attribute :>> parts; } }";
    const B_CHANGED: &str = "package B { import A::*; part def Truck :> Lib::Other { attribute :>> mass = 2; } part truck : Truck { attribute :>> parts; } }";

    fn library() -> Arc<PreparedLibrary> {
        let mut base = Model::new();
        let parsed = base.add_library_source("lib.sysml", LIBRARY);
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        base.prepare_library().unwrap()
    }

    /// A build of `a` and `b` on the library, starting from `start` when
    /// given, with the outcomes it settled on.
    fn build(
        library: &Arc<PreparedLibrary>,
        a: &str,
        b: &str,
        start: Option<Arc<SettledOutcomes>>,
    ) -> (ResolvedModel, Option<Arc<SettledOutcomes>>) {
        let mut model = Model::new();
        Arc::clone(library).install(&mut model).unwrap();
        for (name, text) in [("a.sysml", a), ("b.sysml", b)] {
            let parsed = model.add_source(name, text);
            assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        }
        match start {
            Some(start) => model.start_from_settled(start),
            None => model.keep_settled_outcomes(),
        }
        let r = ResolvedModel::build(&model);
        assert!(r.b.library_facts.is_some(), "built on the prepared library");
        let settled = model.settled_outcomes();
        (r, settled)
    }

    /// What a build answers: its elements' metaclasses, identities and
    /// properties, the references it could not resolve, and the sites
    /// and imports it recorded.
    fn answers(r: &ResolvedModel) -> String {
        let mut out = serde_json::to_string(&r.source_compact_json()).unwrap();
        out.push_str(&format!(
            "\n{:?}\n{:?}\n{}\n{:?}",
            r.b.unresolved,
            r.b.ambiguous,
            r.b.ref_sites.len(),
            {
                let mut used: Vec<_> = r.b.used_imports.iter().copied().collect();
                used.sort_unstable();
                used
            }
        ));
        out
    }

    #[test]
    fn the_same_units_settle_in_one_pass_from_the_kept_outcomes() {
        let library = library();
        let (cold, settled) = build(&library, A, B, None);
        let settled = settled.expect("kept");
        assert_eq!(settled.unit_count(), 2);
        let passes_before = passes();
        let settles_before = settled_passes();
        let (warm, kept_again) = build(&library, A, B, Some(Arc::clone(&settled)));
        assert_eq!(passes() - passes_before, 1, "one confirming pass");
        assert_eq!(settled_passes() - settles_before, 1);
        assert_eq!(answers(&warm), answers(&cold));
        assert!(
            kept_again.is_some(),
            "the seeded build keeps its outcomes too"
        );
    }

    #[test]
    fn a_changed_reference_starts_unresolved_and_the_rest_from_their_outcomes() {
        let library = library();
        let (_, settled) = build(&library, A, B, None);
        let settled = settled.unwrap();
        let (cold, _) = build(&library, A, B_CHANGED, None);
        let passes_before = passes();
        let (warm, _) = build(&library, A, B_CHANGED, Some(settled));
        let warm_passes = passes() - passes_before;
        assert_eq!(answers(&warm), answers(&cold));
        let passes_before = passes();
        build(&library, A, B_CHANGED, None);
        let cold_passes = passes() - passes_before;
        assert!(
            warm_passes <= cold_passes + 1,
            "{warm_passes} passes, cold {cold_passes}"
        );
    }

    #[test]
    fn a_wrong_seed_costs_a_pass_and_no_answer() {
        let library = library();
        let (cold, settled) = build(&library, A, B, None);
        let mut wrong = (*settled.unwrap()).clone();
        // every kept outcome unresolved, and then every one pointing at
        // the library's `Other::mass`
        let other_mass = (0..cold.b.lib_boundary)
            .rev()
            .map(|i| &cold.b.elements[i])
            .find(|e| {
                e.ty == "AttributeUsage"
                    && e.props.get("declaredName").and_then(|v| v.as_str()) == Some("mass")
            })
            .map(|e| e.id)
            .unwrap();
        for target in [None, Some(other_mass)] {
            for unit in wrong.units.values_mut() {
                for (_, outcome) in &mut unit.refs {
                    *outcome = target;
                }
            }
            let passes_before = passes();
            let (warm, _) = build(&library, A, B, Some(Arc::new(wrong.clone())));
            assert!(
                passes() - passes_before >= 2,
                "the wrong guess is corrected and confirmed"
            );
            assert_eq!(answers(&warm), answers(&cold));
        }
    }

    #[test]
    fn a_seeded_loop_that_does_not_settle_starts_over_cold() {
        let library = library();
        let (cold, settled) = build(&library, A, B, None);
        let settled = settled.unwrap();
        let passes_before = passes();
        build(&library, A, B, None);
        let cold_passes = passes() - passes_before;
        set_seeded_passes(Some(0));
        let abandoned = seeds_abandoned();
        let passes_before = passes();
        let (warm, kept) = build(&library, A, B, Some(settled));
        set_seeded_passes(None);
        assert_eq!(seeds_abandoned(), abandoned + 1);
        assert_eq!(
            passes() - passes_before,
            cold_passes,
            "the cold passes after the abandoned seed"
        );
        assert_eq!(answers(&warm), answers(&cold));
        assert!(kept.is_some());
    }

    #[test]
    fn outcomes_of_other_units_do_not_seed() {
        let library = library();
        let (_, settled) = build(&library, A, B, None);
        let settled = settled.unwrap();
        // the same texts under other unit names: no reference takes a seed
        let renamed = |start: Option<Arc<SettledOutcomes>>| {
            let mut model = Model::new();
            Arc::clone(&library).install(&mut model).unwrap();
            model.add_source("x.sysml", A);
            model.add_source("y.sysml", B);
            match start {
                Some(start) => model.start_from_settled(start),
                None => model.keep_settled_outcomes(),
            }
            ResolvedModel::build(&model)
        };
        let passes_before = passes();
        let cold = renamed(None);
        let cold_passes = passes() - passes_before;
        let abandoned = seeds_abandoned();
        let passes_before = passes();
        let warm = renamed(Some(settled));
        assert_eq!(passes() - passes_before, cold_passes, "a cold build");
        assert_eq!(seeds_abandoned(), abandoned, "no seed to abandon");
        assert_eq!(answers(&warm), answers(&cold));
    }

    /// A unit with an element inserted before its references: the
    /// references after it lie elsewhere in the unit, so they take no
    /// seed; the other unit's do, and the answers are the cold build's.
    #[test]
    fn references_after_an_inserted_element_start_unresolved() {
        let library = library();
        let (_, settled) = build(&library, A, B, None);
        let settled = settled.unwrap();
        let inserted = B.replacen("package B { ", "package B { part def Extra; ", 1);
        assert_ne!(inserted, B);
        let (cold, _) = build(&library, A, &inserted, None);
        let (warm, _) = build(&library, A, &inserted, Some(settled));
        assert_eq!(answers(&warm), answers(&cold));
    }
}
