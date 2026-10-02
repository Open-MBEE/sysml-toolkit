//! Certificate for adding dynamic positional rows behind an immutable prefix.
//! It does not admit callee endpoints, derive bases or publish/cache a plan.
use super::positional::PositionalRedefinitions;
use std::collections::{HashMap, HashSet};

#[derive(Debug, PartialEq, Eq)]
pub(super) enum Refusal {
    WorkLimit,
    LostCompleteness,
    ChangedStaticOrder,
    InvalidSource,
    DuplicateTarget,
}

fn charge(steps: &mut usize, amount: usize) -> Result<(), Refusal> {
    *steps = steps.saturating_add(amount);
    if *steps > crate::eval::MAX_STEPS {
        Err(Refusal::WorkLimit)
    } else {
        Ok(())
    }
}

/// Compare every static positional row against the complete candidate run.
/// Each old target vector must be an exact prefix: a semantic tail cannot
/// insert new targets before/between immutable static rows. New completeness
/// failures anywhere refuse the batch, including scopes reached via imports.
/// Required owners are all dynamic specialization sources, including calls
/// with no arguments/results. They must not be incomplete merely because the
/// candidate happened to emit no positional row for them.
///
/// source_owner must return the checked exact owning Type of a positional
/// Feature, charging any traversal to the supplied shared steps. A scope-only
/// owner lookup is insufficient for scope-less invocation arguments.
/// Both plans must come from the same immutable authored snapshot and shared
/// planner. Only the returned additions may enter a bind-invalidated tail;
/// the candidate plan itself remains unpublished until the entire dynamic
/// batch (endpoints, generated IDs, ownership and caches) can commit atomically.
pub(super) fn certify(
    static_plan: &PositionalRedefinitions,
    candidate: &PositionalRedefinitions,
    required_owners: &[usize],
    mut source_owner: impl FnMut(usize, &mut usize) -> Option<usize>,
    steps: &mut usize,
) -> Result<HashMap<usize, Vec<usize>>, Refusal> {
    charge(steps, required_owners.len())?;
    for owner in required_owners {
        if candidate.incomplete.contains(owner) {
            return Err(Refusal::LostCompleteness);
        }
    }
    charge(steps, candidate.incomplete.len())?;
    if candidate
        .incomplete
        .iter()
        .any(|owner| !static_plan.incomplete.contains(owner))
    {
        return Err(Refusal::LostCompleteness);
    }
    for (&source, old) in &static_plan.targets {
        charge(steps, old.len().saturating_add(1))?;
        let next = candidate
            .targets
            .get(&source)
            .map_or(&[][..], Vec::as_slice);
        if !next.starts_with(old) {
            return Err(Refusal::ChangedStaticOrder);
        }
    }
    let mut delta = HashMap::new();
    for (&source, targets) in &candidate.targets {
        // Charge all target validation and copying before allocating either
        // the uniqueness set or the output slice. No partial delta escapes.
        charge(steps, targets.len().saturating_mul(2).saturating_add(1))?;
        let mut seen = HashSet::new();
        if targets.iter().any(|target| !seen.insert(*target)) {
            return Err(Refusal::DuplicateTarget);
        }
        let before = static_plan.targets.get(&source).map_or(0, Vec::len);
        if targets.len() > before {
            let owner = source_owner(source, steps);
            charge(steps, 0)?;
            let owner = owner.ok_or(Refusal::InvalidSource)?;
            if candidate.incomplete.contains(&owner) {
                return Err(Refusal::LostCompleteness);
            }
            delta.insert(source, targets[before..].to_vec());
        }
    }
    Ok(delta)
}

#[cfg(test)]
mod tests {
    use super::*;
    fn plan(rows: &[(usize, &[usize])], incomplete: &[usize]) -> PositionalRedefinitions {
        PositionalRedefinitions {
            targets: rows.iter().map(|(s, t)| (*s, t.to_vec())).collect(),
            incomplete: incomplete.iter().copied().collect(),
        }
    }
    fn run(
        a: &PositionalRedefinitions,
        b: &PositionalRedefinitions,
        required: &[usize],
    ) -> Result<HashMap<usize, Vec<usize>>, Refusal> {
        certify(a, b, required, |s, _| Some(s / 10), &mut 0)
    }
    #[test]
    fn suffix_additions_preserve_every_static_row() {
        let old = plan(&[(10, &[2, 3]), (20, &[4])], &[]);
        let next = plan(&[(10, &[2, 3, 5]), (20, &[4]), (30, &[6])], &[]);
        assert_eq!(
            run(&old, &next, &[1]),
            Ok(HashMap::from([(10, vec![5]), (30, vec![6])]))
        );
        assert_eq!(run(&old, &old, &[]), Ok(HashMap::new()));
    }
    #[test]
    fn loss_reorder_retarget_and_middle_insert_are_refused() {
        let old = plan(&[(10, &[2, 3])], &[]);
        for next in [
            plan(&[], &[]),
            plan(&[(10, &[3, 2])], &[]),
            plan(&[(10, &[2, 4])], &[]),
            plan(&[(10, &[2, 4, 3])], &[]),
        ] {
            assert_eq!(run(&old, &next, &[]), Err(Refusal::ChangedStaticOrder));
        }
    }
    #[test]
    fn incompleteness_without_output_is_not_empty_success() {
        let old = plan(&[], &[1]);
        assert_eq!(run(&old, &old, &[1]), Err(Refusal::LostCompleteness));
        assert_eq!(
            run(&plan(&[], &[]), &plan(&[], &[9]), &[]),
            Err(Refusal::LostCompleteness)
        );
        assert_eq!(
            run(&old, &plan(&[(10, &[2])], &[1]), &[]),
            Err(Refusal::LostCompleteness)
        );
        assert_eq!(
            run(&old, &plan(&[(10, &[2])], &[]), &[1]),
            Ok(HashMap::from([(10, vec![2])]))
        );
    }
    #[test]
    fn invalid_targets_and_sources_refuse() {
        assert_eq!(
            run(&plan(&[], &[]), &plan(&[(10, &[2, 2])], &[]), &[]),
            Err(Refusal::DuplicateTarget)
        );
        assert_eq!(
            certify(
                &plan(&[], &[]),
                &plan(&[(10, &[2])], &[]),
                &[],
                |_, _| None,
                &mut 0
            ),
            Err(Refusal::InvalidSource)
        );
    }
    #[test]
    fn exhausted_comparison_returns_no_prefix_and_does_not_poison_retry() {
        let old = plan(&[], &[]);
        let next = plan(&[(10, &[2, 3])], &[]);
        let mut steps = crate::eval::MAX_STEPS - 1;
        assert_eq!(
            certify(&old, &next, &[], |_, _| Some(1), &mut steps),
            Err(Refusal::WorkLimit)
        );
        assert!(steps > crate::eval::MAX_STEPS);
        assert!(run(&old, &next, &[]).is_ok());
    }
    #[test]
    fn successful_owner_callback_cannot_hide_exhausted_shared_work() {
        let old = plan(&[], &[]);
        let next = plan(&[(10, &[2])], &[]);
        let mut steps = 0;
        let result = certify(
            &old,
            &next,
            &[],
            |_, work| {
                *work = crate::eval::MAX_STEPS + 1;
                Some(1)
            },
            &mut steps,
        );
        assert_eq!(result, Err(Refusal::WorkLimit));
    }
}
