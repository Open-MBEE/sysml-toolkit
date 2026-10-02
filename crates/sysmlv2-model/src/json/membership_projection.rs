//! Shared ordered Feature/membership reduction used by positional planning.
//! Inputs are provider facts; this algebra does not certify their completeness.
//! Checked effective-input consumers must validate the same provider graph before
//! treating the returned sequence as complete. No lookup, publication, or cache.
use std::collections::{HashMap, HashSet};

#[derive(Clone, Copy, PartialEq, Eq)]
pub(super) struct Membership {
    pub(super) relationship: usize,
    pub(super) member: usize,
}

#[derive(PartialEq, Eq)]
pub(super) struct Node {
    pub(super) owned: Vec<usize>,
    pub(super) owned_memberships: Vec<Membership>,
    pub(super) bases: Vec<usize>,
    pub(super) public_imports: Vec<Membership>,
    pub(super) protected_imports: Vec<Membership>,
    pub(super) memberships_complete: bool,
}

/// Classification facts belong to the caller's provider. These predicates do
/// not imply that the owner's relationship or inheritance domain is complete.
pub(super) trait MembershipFacts {
    fn is_feature(&self, member: usize) -> bool;
    fn is_feature_membership(&self, relationship: usize) -> bool;
    fn is_protected(&self, relationship: usize) -> bool;
}

#[derive(Default)]
pub(super) struct Reduction {
    seen: HashSet<usize>,
    owned_direct: HashSet<usize>,
    counts: HashMap<usize, usize>,
    shadow: HashSet<usize>,
}
impl Reduction {
    /// Ordered union of each direct base's complete nonprivate projection.
    pub(super) fn inheritable(
        &mut self,
        node: &Node,
        exported: &HashMap<usize, Vec<Membership>>,
        steps: &mut Option<&mut usize>,
    ) -> Option<Vec<Membership>> {
        let mut inherited = Vec::new();
        reset_scratch_set(&mut self.seen);
        for &base in &node.bases {
            // Admission belongs to the contributing membership or import,
            // including import-all contributions of private members.
            charge(steps, exported[&base].len().saturating_add(1))?;
            for &membership in &exported[&base] {
                if self.seen.insert(membership.relationship) {
                    inherited.push(membership);
                }
            }
        }
        Some(inherited)
    }
    pub(super) fn reduce(
        &mut self,
        node: &Node,
        exported: &HashMap<usize, Vec<Membership>>,
        redefinitions: &HashMap<usize, Vec<usize>>,
        traversal: &mut Reachability,
        facts: &impl MembershipFacts,
        steps: &mut Option<&mut usize>,
    ) -> Option<(Vec<usize>, Vec<Membership>)> {
        let mut inherited = self.inheritable(node, exported, steps)?;
        reset_scratch_set(&mut self.owned_direct);
        for feature in &node.owned {
            charge(
                steps,
                redefinitions
                    .get(feature)
                    .map_or(0, Vec::len)
                    .saturating_add(1),
            )?;
        }
        self.owned_direct.extend(
            node.owned
                .iter()
                .flat_map(|f| redefinitions.get(f).into_iter().flatten().copied()),
        );
        reset_scratch_map(&mut self.counts);
        charge(steps, inherited.len())?;
        for membership in &inherited {
            if facts.is_feature(membership.member) {
                *self.counts.entry(membership.member).or_insert(0usize) += 1;
            }
        }
        reset_scratch_set(&mut self.shadow);
        // Every membership of one Feature has the same closure and
        // owned-feature comparison, so traverse that Feature only once.
        for (&feature, &count) in &self.counts {
            charge(steps, 1)?;
            if redefinitions.get(&feature).is_none_or(Vec::is_empty) {
                // The closure is exactly this feature; no traversal or
                // intermediate collection is necessary.
                if count > 1 || self.owned_direct.contains(&feature) {
                    self.shadow.insert(feature);
                }
                continue;
            }
            let closure = traversal.reachable_budget(feature, redefinitions, steps)?;
            charge(steps, closure.len().saturating_mul(2))?;
            // Reflexive closure suppresses another Membership of this
            // same Feature, but never suppresses its own Membership.
            self.shadow.extend(
                closure
                    .iter()
                    .copied()
                    .filter(|&target| target != feature || count > 1),
            );
            if closure.iter().any(|t| self.owned_direct.contains(t)) {
                self.shadow.insert(feature);
            }
        }
        charge(
            steps,
            inherited
                .len()
                .saturating_mul(2)
                .saturating_add(node.owned.len()),
        )?;
        inherited
            .retain(|m| !self.counts.contains_key(&m.member) || !self.shadow.contains(&m.member));
        let surviving = inherited;
        let mut features = node.owned.clone();
        features.extend(surviving.iter().filter_map(|membership| {
            facts
                .is_feature_membership(membership.relationship)
                .then_some(membership.member)
        }));
        Some((features, surviving))
    }
    pub(super) fn export(
        &mut self,
        node: &Node,
        surviving: Vec<Membership>,
        facts: &impl MembershipFacts,
        steps: &mut Option<&mut usize>,
    ) -> Option<Vec<Membership>> {
        charge(
            steps,
            node.owned_memberships
                .len()
                .saturating_mul(4)
                .saturating_add(node.public_imports.len().saturating_mul(2))
                .saturating_add(node.protected_imports.len().saturating_mul(2))
                .saturating_add(surviving.len().saturating_mul(2)),
        )?;
        let mut visible = Vec::new();
        for protected in [false, true] {
            visible.extend(
                node.owned_memberships
                    .iter()
                    .copied()
                    .filter(|m| facts.is_protected(m.relationship) == protected),
            );
            visible.extend(if protected {
                &node.protected_imports
            } else {
                &node.public_imports
            });
        }
        visible.extend(surviving);
        reset_scratch_set(&mut self.seen);
        visible.retain(|m| self.seen.insert(m.relationship));
        Some(visible)
    }
}

// A wide node must not make every later tiny node clear a wide hash table.
// Retain ordinary capacities, but discard an oversized table after that first
// wide-to-small transition; its one large clear is charged to the wide node.
pub(super) fn reset_scratch_set<T>(scratch: &mut HashSet<T>) {
    if scratch.capacity() > scratch.len().max(32).saturating_mul(4) {
        *scratch = HashSet::new();
    } else {
        scratch.clear();
    }
}

pub(super) fn reset_scratch_map<K, V>(scratch: &mut HashMap<K, V>) {
    if scratch.capacity() > scratch.len().max(32).saturating_mul(4) {
        *scratch = HashMap::new();
    } else {
        scratch.clear();
    }
}

/// Scratch space for one planning pass. The graph grows while planning, so
/// every traversal gets fresh marks; only storage is reused, never reachability.
pub(super) struct Reachability {
    pub(super) marks: Vec<usize>,
    sparse: Option<HashSet<usize>>,
    pub(super) generation: usize,
    pub(super) todo: Vec<usize>,
    pub(super) reached: Vec<usize>,
}

impl Reachability {
    pub(super) fn new(elements: usize) -> Self {
        Self {
            marks: vec![0; elements],
            sparse: None,
            generation: 0,
            todo: Vec::new(),
            reached: Vec::new(),
        }
    }

    /// Small certified slices need marks only for visited identities. This
    /// reuses the same traversal, without allocating for unrelated graph rows.
    pub(super) fn sparse() -> Self {
        Self {
            marks: Vec::new(),
            sparse: Some(HashSet::new()),
            generation: 0,
            todo: Vec::new(),
            reached: Vec::new(),
        }
    }

    fn begin(&mut self, steps: &mut Option<&mut usize>) -> Option<()> {
        if let Some(marks) = &mut self.sparse {
            charge(steps, marks.capacity())?;
            reset_scratch_set(marks);
        } else {
            if self.generation == usize::MAX {
                charge(steps, self.marks.len())?;
                self.marks.fill(0);
                self.generation = 0;
            }
            self.generation += 1;
        }
        Some(())
    }

    fn visit(&mut self, element: usize) -> bool {
        if let Some(marks) = &mut self.sparse {
            marks.insert(element)
        } else if self.marks[element] == self.generation {
            false
        } else {
            self.marks[element] = self.generation;
            true
        }
    }

    #[cfg(test)]
    pub(super) fn reachable(
        &mut self,
        source: usize,
        graph: &HashMap<usize, Vec<usize>>,
    ) -> &[usize] {
        self.reachable_budget(source, graph, &mut None)
            .expect("unbounded traversal cannot exhaust its budget")
    }

    /// Existential reachability does not need to allocate a complete closure.
    /// Fresh marks observe graph growth between calls; no answer is cached.
    pub(super) fn reaches_budget(
        &mut self,
        source: usize,
        target: usize,
        graph: &HashMap<usize, Vec<usize>>,
        steps: &mut Option<&mut usize>,
    ) -> Option<bool> {
        charge(steps, 1)?;
        self.begin(steps)?;
        self.todo.clear();
        self.todo.push(source);
        while let Some(e) = self.todo.pop() {
            charge(steps, 1)?;
            if e == target {
                return Some(true);
            }
            if !self.visit(e) {
                continue;
            }
            for &next in graph.get(&e).into_iter().flatten() {
                charge(steps, 1)?;
                if next == target {
                    return Some(true);
                }
                self.todo.push(next);
            }
        }
        Some(false)
    }

    pub(super) fn reachable_budget(
        &mut self,
        source: usize,
        graph: &HashMap<usize, Vec<usize>>,
        steps: &mut Option<&mut usize>,
    ) -> Option<&[usize]> {
        charge(steps, 1)?;
        self.begin(steps)?;
        self.todo.clear();
        self.reached.clear();
        self.todo.push(source);
        while let Some(e) = self.todo.pop() {
            charge(steps, 1)?;
            if self.visit(e) {
                self.reached.push(e);
                charge(steps, graph.get(&e).map_or(0, Vec::len))?;
                self.todo
                    .extend(graph.get(&e).into_iter().flatten().copied());
            }
        }
        Some(&self.reached)
    }
}

pub(super) fn charge(steps: &mut Option<&mut usize>, amount: usize) -> Option<()> {
    if let Some(steps) = steps {
        **steps = steps.saturating_add(amount);
        if **steps > crate::eval::MAX_STEPS {
            return None;
        }
    }
    Some(())
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn sparse_wide_to_small_traversal_work_does_not_retain_wide_clear_cost() {
        let graph = HashMap::from([(0, (1..10_000).collect()), (10_000, vec![10_001])]);
        let mut dense = Reachability::new(10_002);
        let mut sparse = Reachability::sparse();
        let mut steps = 0;
        assert_eq!(
            sparse
                .reachable_budget(0, &graph, &mut Some(&mut steps))
                .unwrap(),
            dense.reachable(0, &graph)
        );
        for _ in 0..2 {
            assert_eq!(
                sparse
                    .reachable_budget(10_000, &graph, &mut Some(&mut steps))
                    .unwrap(),
                dense.reachable(10_000, &graph)
            );
        }
        let small_start = steps;
        for _ in 0..1_000 {
            assert_eq!(
                sparse
                    .reachable_budget(10_000, &graph, &mut Some(&mut steps))
                    .unwrap(),
                &[10_000, 10_001]
            );
        }
        assert!(steps - small_start < 10_000);
        let mut exhausted = crate::eval::MAX_STEPS;
        assert!(
            sparse
                .reachable_budget(0, &graph, &mut Some(&mut exhausted))
                .is_none()
        );
        assert_eq!(sparse.reachable(0, &graph), dense.reachable(0, &graph));
    }
    #[test]
    fn existential_reachability_matches_complete_closure_through_graph_growth() {
        let mut graph: HashMap<usize, Vec<usize>> = HashMap::new();
        let mut traversal = Reachability::new(12);
        let mut sparse = Reachability::sparse();
        for round in 0..36 {
            graph
                .entry(round % 12)
                .or_default()
                .push((round * 7 + 3 + round / 12) % 12);
            for source in 0..12 {
                let expected = traversal.reachable(source, &graph).to_vec();
                assert_eq!(sparse.reachable(source, &graph), expected);
                for target in 0..12 {
                    assert_eq!(
                        traversal.reaches_budget(source, target, &graph, &mut Some(&mut 0)),
                        Some(expected.contains(&target))
                    );
                    assert_eq!(
                        sparse.reaches_budget(source, target, &graph, &mut Some(&mut 0)),
                        Some(expected.contains(&target))
                    );
                }
            }
        }
        traversal.generation = usize::MAX;
        let mut exhausted = crate::eval::MAX_STEPS;
        assert!(
            traversal
                .reaches_budget(0, 3, &graph, &mut Some(&mut exhausted))
                .is_none()
        );
        assert_eq!(
            traversal.reaches_budget(0, 3, &graph, &mut Some(&mut 0)),
            Some(true)
        );
    }
}
