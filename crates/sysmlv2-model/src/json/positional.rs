//! Rule-required positional redefinitions, shared by inheritance and the
//! materialized relationship view. This table never changes compact storage.

#[cfg(test)]
use super::membership_projection::{reset_scratch_map, reset_scratch_set};
use super::{
    Builder,
    membership_projection::{
        ExportedOver, Membership as PositionalMembership, MembershipFacts, Node, Reachability,
        Reduction, charge,
    },
};
use crate::metaclass::conforms;
use std::collections::{HashMap, HashSet};

#[derive(Clone, Default)]
pub(super) struct PositionalRedefinitions {
    pub targets: HashMap<usize, Vec<usize>>,
    pub incomplete: HashSet<usize>,
}

/// The direct bases a positional planning reads, by type: a table of them, or
/// a build's own over its prepared library's ([`OverLibrary`]).
pub(super) trait DirectBases {
    fn get(&self, e: &usize) -> Option<&Vec<usize>>;
}
impl DirectBases for HashMap<usize, Vec<usize>> {
    fn get(&self, e: &usize) -> Option<&Vec<usize>> {
        HashMap::get(self, e)
    }
}
/// A build's own types' direct bases over its library's: the two tables name
/// disjoint types.
pub(super) struct OverLibrary<'a> {
    pub own: &'a HashMap<usize, Vec<usize>>,
    pub library: &'a HashMap<usize, Vec<usize>>,
}
impl DirectBases for OverLibrary<'_> {
    fn get(&self, e: &usize) -> Option<&Vec<usize>> {
        self.own.get(e).or_else(|| self.library.get(e))
    }
}

/// Raw stored-row inputs shared only by the static/dynamic planning transaction.
/// Imports and candidate bases are gathered anew on each pass. Reduction reuse
/// requires equality of every consumed input; otherwise it is recomputed. Row
/// mutations refuse reuse instead of relabeling an older snapshot.
#[derive(Default)]
pub(super) struct PositionalWorkspace {
    rows: Option<crate::layered::Revision>,
    explicit: usize,
    one_shot: bool,
    roots: Option<Vec<usize>>,
    ids: Option<HashSet<uuid::Uuid>>,
    owned: HashMap<usize, (Vec<usize>, Option<Vec<PositionalMembership>>)>,
    unresolved: HashMap<usize, bool>,
    reduction: Option<CompleteReduction>,
    /// When set, the types a planning reached are recorded here.
    reached: Option<Vec<usize>>,
    /// The plans of the prepared library a planning extends: the types the
    /// library's planning reached are not planned again, their derivations
    /// read from there.
    library: Option<std::sync::Arc<super::LibraryPlans>>,
    /// When set, a planning leaves what it derived for each type here.
    planned: Option<PlannedTypes>,
}

/// The positional roles of a type's effective features: its ends, its
/// results and its other parameters, each in effective order.
#[derive(Clone)]
pub(super) struct Roles {
    ends: Vec<usize>,
    results: Vec<usize>,
    parameters: Vec<usize>,
}

/// What a planning derived for every type it completed — its effective
/// features, their roles, its exported memberships — and the redefinitions
/// it read and added. A prepared library's planning keeps these, and a build
/// on the library plans only its own types over them
/// (see [`Builder::plan_positional_on_library`]).
#[derive(Default)]
pub(super) struct PlannedTypes {
    effective: HashMap<usize, Vec<usize>>,
    roles: HashMap<usize, Roles>,
    exported: HashMap<usize, Vec<PositionalMembership>>,
    redefinitions: HashMap<usize, Vec<usize>>,
}
#[cfg(test)]
impl PlannedTypes {
    /// Whether the planning kept what it derived for type `e`.
    pub(super) fn has(&self, e: usize) -> bool {
        self.effective.contains_key(&e)
            && self.roles.contains_key(&e)
            && self.exported.contains_key(&e)
    }
}
/// Recorded bootstrap edges indexed only for one planner invocation. These
/// vectors can change without a stored-row revision, so this proof input must
/// never be cached on Builder, StoredStructure, or the cross-pass workspace.
#[derive(Default)]
struct RecordedRedefinitions {
    targets: HashMap<usize, HashSet<usize>>,
    incomplete: HashSet<usize>,
}
impl RecordedRedefinitions {
    fn build(b: &Builder, steps: &mut usize) -> Option<Self> {
        charge(&mut Some(steps), b.spec_targets.len())?;
        let mut index = Self::default();
        for (i, &(source, kind, _, _)) in b.spec_targets.iter().enumerate() {
            if kind != "Redefinition" {
                continue;
            }
            if let Some(target) = b.spec_resolved.get(i).copied().flatten() {
                index.targets.entry(source).or_default().insert(target);
            } else {
                index.incomplete.insert(source);
            }
        }
        Some(index)
    }

    fn sources_match(
        &self,
        actual: &HashMap<usize, Vec<usize>>,
        steps: &mut usize,
    ) -> Option<bool> {
        for (source, targets) in actual {
            charge(
                &mut Some(&mut *steps),
                targets.len().saturating_mul(2).saturating_add(1),
            )?;
            if self.incomplete.contains(source) {
                return Some(false);
            }
            let current: HashSet<_> = targets.iter().copied().collect();
            if self
                .targets
                .get(source)
                .map_or(!current.is_empty(), |expected| &current != expected)
            {
                return Some(false);
            }
        }
        Some(true)
    }
}

#[derive(Default)]
struct ImportProof {
    recorded: Option<RecordedRedefinitions>,
    // Domain evidence only, local to this immutable planning invocation.
    role_domains: HashSet<usize>,
}
struct ImportSourceContext<'a> {
    owner: usize,
    bases: &'a dyn DirectBases,
    incomplete: &'a HashSet<usize>,
    ordinary_only: bool,
    allow_prerequisites: bool,
}

struct CompleteReduction {
    order: Vec<usize>,
    nodes: HashMap<usize, Node>,
    prerequisites: HashMap<usize, Vec<usize>>,
    incomplete: HashSet<usize>,
    redefinitions: HashMap<usize, Vec<usize>>,
    result: PositionalRedefinitions,
}
fn charge_map_vectors(
    map: &HashMap<usize, Vec<usize>>,
    steps: &mut Option<&mut usize>,
) -> Option<()> {
    charge(steps, map.capacity())?;
    for values in map.values() {
        charge(steps, values.len())?;
    }
    Some(())
}
fn charge_plan(plan: &PositionalRedefinitions, steps: &mut Option<&mut usize>) -> Option<()> {
    charge(steps, plan.incomplete.capacity())?;
    charge_map_vectors(&plan.targets, steps)
}
impl CompleteReduction {
    fn charge_inputs(&self, steps: &mut Option<&mut usize>) -> Option<()> {
        charge(
            steps,
            self.order
                .len()
                .saturating_add(self.nodes.capacity())
                .saturating_add(self.incomplete.capacity()),
        )?;
        for node in self.nodes.values() {
            charge(
                steps,
                node.owned
                    .len()
                    .saturating_add(node.owned_memberships.len())
                    .saturating_add(node.bases.len())
                    .saturating_add(node.public_imports.len())
                    .saturating_add(node.protected_imports.len()),
            )?;
        }
        charge_map_vectors(&self.prerequisites, steps)?;
        charge_map_vectors(&self.redefinitions, steps)
    }
}
impl PositionalWorkspace {
    pub(super) fn one_shot() -> Self {
        Self {
            one_shot: true,
            ..Self::default()
        }
    }
    fn align(&mut self, b: &mut Builder) -> Option<()> {
        if let Some(rows) = &self.rows {
            if self.explicit != b.explicit_len()
                || !b
                    .elements
                    .revision()
                    .is_some_and(|current| rows.same_as(current))
            {
                return None;
            }
        } else {
            self.rows = Some(b.elements.observe_revision());
            self.explicit = b.explicit_len();
        }
        Some(())
    }
}

struct CompatibilityMembershipFacts<'a>(&'a Builder);
impl MembershipFacts for CompatibilityMembershipFacts<'_> {
    fn is_feature(&self, member: usize) -> bool {
        conforms(self.0.elements[member].ty, "Feature")
    }
    fn is_feature_membership(&self, relationship: usize) -> bool {
        conforms(self.0.elements[relationship].ty, "FeatureMembership")
    }
    fn is_protected(&self, relationship: usize) -> bool {
        self.0.elements[relationship]
            .props
            .get("visibility")
            .and_then(|value| value.as_str())
            == Some("protected")
    }
}

impl Builder {
    pub(super) fn ensure_positional_redefinitions(&mut self) {
        if !self.positional_planning {
            self.refresh_supported_chain_evidence(None)
                .expect("unbounded chain validation");
        }
        if !self.semantic_ready
            || self.positional_redefinitions.is_some()
            || self.positional_planning
        {
            return;
        }
        // Base resolution can inspect inheritance while resolving semantic
        // metadata. Never recursively start another planner from that lookup.
        self.positional_redefinitions = Some(Default::default());
        self.positional_from_library = false;
        let used = self.used_imports.clone();
        let walks = std::mem::take(&mut self.query_imports);
        let previous_static = std::mem::replace(&mut self.static_planning, true);
        self.positional_planning = true;
        let (plan, from_library) = self.plan_positional_redefinitions();
        self.positional_planning = false;
        self.static_planning = previous_static;
        self.used_imports = used;
        self.query_imports = walks;
        self.inherited_cache.clear();
        self.inherited_by_heritage.clear();
        self.positional_redefinitions = Some(plan);
        self.positional_from_library = from_library;
    }

    /// Prepare a complete positional table within the caller's allowance.
    /// In-progress work is private: refusal never publishes an empty sentinel.
    pub(super) fn ensure_positional_redefinitions_with_budget(
        &mut self,
        steps: &mut usize,
    ) -> bool {
        if charge(&mut Some(&mut *steps), 1).is_none() {
            return false;
        }
        if self.positional_planning {
            return false;
        }
        if self
            .refresh_supported_chain_evidence(Some(&mut *steps))
            .is_none()
        {
            return false;
        }
        if !self.semantic_ready || self.positional_redefinitions.is_some() {
            return true;
        }
        // Precharge invalidation before planning or touching caller state.
        if charge(
            &mut Some(&mut *steps),
            self.inherited_cache
                .capacity()
                .saturating_add(self.inherited_by_heritage.capacity()),
        )
        .is_none()
        {
            return false;
        }
        for key in self.inherited_by_heritage.keys() {
            if charge(&mut Some(&mut *steps), key.0.len()).is_none() {
                return false;
            }
        }
        let previous_static = std::mem::replace(&mut self.static_planning, true);
        self.positional_planning = true;
        let plan = (|| {
            if let Some(plan) = self.plan_positional_extending_library(Some(&mut *steps))? {
                return Some((plan, true));
            }
            let (bases, incomplete) =
                self.positional_direct_bases_with_budget(Some(&mut *steps))?;
            self.plan_positional_redefinitions_with_bases_and_budget(
                &bases,
                &incomplete,
                Some(&mut *steps),
            )
            .map(|plan| (plan, false))
        })();
        self.positional_planning = false;
        self.static_planning = previous_static;
        let Some((plan, from_library)) = plan else {
            return false;
        };
        self.inherited_cache.clear();
        self.inherited_by_heritage.clear();
        self.positional_redefinitions = Some(plan);
        self.positional_from_library = from_library;
        true
    }

    /// The positional plan, and whether it extends the prepared library's.
    fn plan_positional_redefinitions(&mut self) -> (PositionalRedefinitions, bool) {
        if let Some(Some(plan)) = self.plan_positional_extending_library(None) {
            return (plan, true);
        }
        let (direct_bases, incomplete) = self.positional_direct_bases();
        (
            self.plan_positional_redefinitions_with_bases(&direct_bases, &incomplete),
            false,
        )
    }

    /// The positional plan of a build extending its prepared library's plans
    /// (see [`Self::plan_positional_on_library`]), its own types' direct bases
    /// read over the library's: `Some(None)` when the build does not extend
    /// them or must plan every row after all, `None` past the budget.
    fn plan_positional_extending_library(
        &mut self,
        mut steps: Option<&mut usize>,
    ) -> Option<Option<PositionalRedefinitions>> {
        if !self.external_implied_names.is_empty() {
            return Some(None);
        }
        let Some(library) = self.library_plans(steps.as_deref_mut())? else {
            return Some(None);
        };
        let plan = self.plan_extending_library(&library, steps.as_deref_mut())?;
        let (own, own_incomplete) =
            self.own_positional_direct_bases(&library, &plan, steps.as_deref_mut())?;
        let mut incomplete = library.bases_incomplete.clone();
        incomplete.extend(own_incomplete);
        let bases = OverLibrary {
            own: &own,
            library: &library.bases,
        };
        self.plan_positional_on_library(&library, &bases, &incomplete, steps)
    }

    /// Plan every type's positional redefinitions, with the types the planning
    /// reached and what it derived for each: a prepared library's own plan
    /// (see [`super::LibraryPlans`]).
    pub(super) fn plan_positional_reaching(
        &mut self,
        direct_bases: &dyn DirectBases,
        incomplete: &HashSet<usize>,
    ) -> (PositionalRedefinitions, HashSet<usize>, PlannedTypes) {
        let mut workspace = PositionalWorkspace::one_shot();
        workspace.reached = Some(Vec::new());
        workspace.planned = Some(PlannedTypes::default());
        let plan = self
            .plan_positional_redefinitions_with_workspace(
                direct_bases,
                incomplete,
                None,
                &mut workspace,
            )
            .expect("unbounded positional construction cannot exhaust its budget");
        let reached = workspace.reached.unwrap_or_default().into_iter().collect();
        (plan, reached, workspace.planned.unwrap_or_default())
    }

    /// The positional redefinitions of a build that extends its prepared
    /// library's plans: the types its own rows hold that pair a feature by
    /// position (the roots a plan of every row starts from after the
    /// library's), planned with the library types they reach, over the
    /// library's own plan.
    ///
    /// What the planning derives for a type reads its bases' derivations and
    /// its own rows only, except which type of a cycle of bases is left
    /// incomplete, which depends on where the walk entered the cycle: a plan
    /// of every row walks the library's types from the library's roots before
    /// this build's. A library type this planning reaches that the library's
    /// planning reached too must therefore come out as it did there, complete
    /// or not, with the same redefinitions; otherwise (`Some(None)`) the
    /// caller plans every row.
    pub(super) fn plan_positional_on_library(
        &mut self,
        library: &std::sync::Arc<super::LibraryPlans>,
        direct_bases: &dyn DirectBases,
        incomplete: &HashSet<usize>,
        mut steps: Option<&mut usize>,
    ) -> Option<Option<PositionalRedefinitions>> {
        let floor = library.rows;
        let end = self.explicit_len();
        charge(&mut steps, end - floor)?;
        let mut roots = Vec::new();
        for e in floor..end {
            if !conforms(self.elements[e].ty, "Type") {
                continue;
            }
            let mut found = false;
            for &rel in &self.elements[e].owned_relationships {
                charge(&mut steps, 1)?;
                if !super::is_feature_membership(self.elements[rel].ty) {
                    continue;
                }
                for &f in &self.elements[rel].children {
                    charge(&mut steps, 1)?;
                    if self.positional_is_end(f) || self.is_parameter(f) {
                        found = true;
                        break;
                    }
                }
                if found {
                    break;
                }
            }
            if found {
                roots.push(e);
            }
        }
        let mut workspace = PositionalWorkspace::one_shot();
        workspace.reached = Some(Vec::new());
        workspace.library = Some(std::sync::Arc::clone(library));
        let plan = self.plan_positional_with_result_query(
            direct_bases,
            incomplete,
            steps.as_deref_mut(),
            Some(&roots),
            None,
            &mut workspace,
        )?;
        let reached = workspace.reached.unwrap_or_default();
        charge(&mut steps, reached.len().saturating_add(plan.targets.len()))?;
        let planned = &library.positional;
        for e in reached {
            if e < floor
                && library.reached.contains(&e)
                && plan.incomplete.contains(&e) != planned.incomplete.contains(&e)
            {
                return Some(None);
            }
        }
        for (source, targets) in &plan.targets {
            if *source < floor
                && planned
                    .targets
                    .get(source)
                    .is_some_and(|planned| planned != targets)
            {
                return Some(None);
            }
        }
        let mut merged = planned.clone();
        charge(
            &mut steps,
            merged.targets.len().saturating_add(merged.incomplete.len()),
        )?;
        merged.targets.extend(plan.targets);
        merged.incomplete.extend(plan.incomplete);
        Some(Some(merged))
    }

    /// Pure planning over an already admitted direct-base projection. Does not
    /// consult or publish the retained implied or positional plan. Callers must
    /// supply authored plus accepted static/dynamic bases in semantic order,
    /// with unresolved providers represented in incomplete. Endpoint/carrier
    /// admission precedes this internal seam; it is not an interchange reader.
    pub(super) fn plan_positional_redefinitions_with_bases(
        &mut self,
        direct_bases: &dyn DirectBases,
        incomplete: &HashSet<usize>,
    ) -> PositionalRedefinitions {
        self.plan_positional_redefinitions_with_bases_and_budget(direct_bases, incomplete, None)
            .expect("unbounded positional construction cannot exhaust its budget")
    }

    /// Budgeted counterpart used before accepting mutable semantic candidates.
    /// None discards the whole local plan; no partial targets/cache is published.
    pub(super) fn plan_positional_redefinitions_with_bases_and_budget(
        &mut self,
        direct_bases: &dyn DirectBases,
        incomplete: &HashSet<usize>,
        steps: Option<&mut usize>,
    ) -> Option<PositionalRedefinitions> {
        self.plan_positional_redefinitions_with_workspace(
            direct_bases,
            incomplete,
            steps,
            &mut PositionalWorkspace::one_shot(),
        )
    }

    pub(super) fn plan_positional_redefinitions_with_workspace(
        &mut self,
        direct_bases: &dyn DirectBases,
        incomplete: &HashSet<usize>,
        steps: Option<&mut usize>,
        workspace: &mut PositionalWorkspace,
    ) -> Option<PositionalRedefinitions> {
        self.plan_positional_with_result_query(
            direct_bases,
            incomplete,
            steps,
            None,
            None,
            workspace,
        )
    }

    /// Reuse the positional algorithm only when its stored selectors agree with
    /// the caller's complete ordered Membership evidence. No plan is published.
    pub(super) fn plan_checked_positional(
        &mut self,
        nodes: &HashMap<usize, Node>,
        bases: &dyn DirectBases,
        import_owners: &HashSet<usize>,
        steps: &mut usize,
    ) -> Option<PositionalRedefinitions> {
        let mut budget = Some(steps);
        charge(&mut budget, nodes.len())?;
        let roots: Vec<_> = nodes.keys().copied().collect();
        for (&owner, node) in nodes {
            self.positional_charge_members(owner, &mut budget)?;
            charge(&mut budget, node.owned.len() + node.owned_memberships.len())?;
            if self.owned_member_elems(owner, true) != node.owned {
                return None;
            }
            let memberships = self.positional_owned_memberships(owner, &mut budget)?;
            if memberships.len() != node.owned_memberships.len()
                || memberships
                    .iter()
                    .zip(&node.owned_memberships)
                    .any(|(a, b)| a.relationship != b.relationship || a.member != b.member)
            {
                return None;
            }
        }
        // The central planner must consume the exact visibility-specific import
        // selectors proved by the checked provider. CanonicalV3 may use the same
        // bounded Package traversal for selectors outside the legacy leaf domain.
        if !import_owners.is_empty() {
            let mut import_proof = ImportProof::default();
            let mut prerequisites = HashMap::new();
            charge(&mut budget, import_owners.len())?;
            for &owner in import_owners {
                let (mut public, mut protected) = self.positional_imports(
                    owner,
                    bases,
                    &HashSet::new(),
                    &mut budget,
                    &mut import_proof,
                    &mut prerequisites,
                )?;
                if let Some(required) = prerequisites.get(&owner) {
                    charge(&mut budget, required.len())?;
                    if required
                        .iter()
                        .any(|dependency| !nodes.contains_key(dependency))
                    {
                        return None;
                    }
                }
                let node = nodes.get(&owner)?;
                for (actual, expected) in [
                    (&mut public, &node.public_imports),
                    (&mut protected, &node.protected_imports),
                ] {
                    charge(&mut budget, actual.len().saturating_add(expected.len()))?;
                    let mut seen = HashSet::new();
                    actual.retain(|m| seen.insert(m.relationship));
                    if actual != expected {
                        return None;
                    }
                }
            }
        }
        self.plan_positional_with_result_query(
            bases,
            &HashSet::new(),
            budget,
            Some(&roots),
            None,
            &mut PositionalWorkspace::one_shot(),
        )
    }

    /// Bootstrap targets are compatibility inputs, never current-row authority.
    /// A checked consumer must prove equality for its entire closure before
    /// using the positional algorithm's reachability-based edge omissions.
    pub(super) fn positional_redefinition_sources_match(
        &self,
        actual: &HashMap<usize, Vec<usize>>,
        steps: &mut usize,
    ) -> Option<bool> {
        let mut budget = Some(steps);
        charge(&mut budget, self.spec_targets.len())?;
        let mut indexed: HashMap<usize, HashSet<usize>> = HashMap::new();
        for (i, &(owner, kind, _, _)) in self.spec_targets.iter().enumerate() {
            if kind == "Redefinition" && actual.contains_key(&owner) {
                let Some(target) = self.spec_resolved.get(i).copied().flatten() else {
                    return Some(false);
                };
                indexed.entry(owner).or_default().insert(target);
            }
        }
        for (owner, targets) in actual {
            charge(
                &mut budget,
                targets.len().saturating_mul(2).saturating_add(1),
            )?;
            let expected = indexed.remove(owner).unwrap_or_default();
            let current: HashSet<_> = targets.iter().copied().collect();
            if current != expected {
                return Some(false);
            }
        }
        Some(true)
    }

    /// Detached candidate selection over caller-certified roots/bases. This
    /// reuses the positional membership algorithm, not its possibly older cache.
    /// Returned identities still require the caller's checked carrier/alias and
    /// library-role certificate; this is not a whole result-family capability.
    pub(super) fn plan_unique_result_candidates(
        &mut self,
        direct_bases: &dyn DirectBases,
        incomplete: &HashSet<usize>,
        roots: &[usize],
        steps: &mut usize,
    ) -> Option<HashMap<usize, usize>> {
        let mut candidates = HashMap::new();
        let plan = self.plan_positional_with_result_query(
            direct_bases,
            incomplete,
            Some(steps),
            Some(roots),
            Some(&mut candidates),
            &mut PositionalWorkspace::one_shot(),
        )?;
        candidates.retain(|owner, _| !plan.incomplete.contains(owner));
        Some(candidates)
    }

    fn plan_positional_with_result_query(
        &mut self,
        direct_bases: &dyn DirectBases,
        incomplete: &HashSet<usize>,
        mut steps: Option<&mut usize>,
        selected_roots: Option<&[usize]>,
        mut result_candidates: Option<&mut HashMap<usize, usize>>,
        workspace: &mut PositionalWorkspace,
    ) -> Option<PositionalRedefinitions> {
        charge(&mut steps, 1)?;
        workspace.align(self)?;
        // UUID lookup may lazily allocate its complete row index in the stored
        // Membership helper. Account once before any such lookup can occur.
        if self.id_index.is_none() || self.id_index_built_for != self.elements.len() {
            charge(&mut steps, self.elements.len())?;
        }
        let mut roots = Vec::new();
        if let Some(selected) = selected_roots {
            charge(&mut steps, selected.len())?;
            roots.extend_from_slice(selected);
        } else if let Some(cached) = &workspace.roots {
            charge(&mut steps, cached.len())?;
            roots.extend_from_slice(cached);
        } else {
            for e in 0..self.explicit_len() {
                charge(&mut steps, 1)?;
                if !conforms(self.elements[e].ty, "Type") {
                    continue;
                }
                // Root discovery needs existence, not an ordered collection.
                // Defer sorting/allocation until the reachable Node is built.
                let mut found = false;
                for &rel in &self.elements[e].owned_relationships {
                    charge(&mut steps, 1)?;
                    if !super::is_feature_membership(self.elements[rel].ty) {
                        continue;
                    }
                    for &f in &self.elements[rel].children {
                        charge(&mut steps, 1)?;
                        if self.positional_is_end(f) || self.is_parameter(f) {
                            found = true;
                            break;
                        }
                    }
                    if found {
                        break;
                    }
                }
                if found {
                    roots.push(e);
                }
            }
        }
        if !workspace.one_shot && selected_roots.is_none() && workspace.roots.is_none() {
            charge(&mut steps, roots.len())?;
            workspace.roots = Some(roots.clone());
        }

        let mut nodes = HashMap::new();
        let mut import_proof = ImportProof::default();
        let mut prerequisites = HashMap::new();
        charge(&mut steps, roots.len())?;
        let mut todo = roots.clone();
        // A planning extending its prepared library's reads what the
        // library's planning derived for every type that planning reached.
        let library = workspace.library.clone();
        let seeded = |e: &usize| library.as_ref().is_some_and(|l| l.reached.contains(e));
        let empty = PlannedTypes::default();
        let planned = library.as_ref().map_or(&empty, |l| &l.planned);
        while let Some(e) = todo.pop() {
            charge(&mut steps, 1)?;
            if nodes.contains_key(&e) || seeded(&e) {
                continue;
            }
            charge(
                &mut steps,
                direct_bases.get(&e).map_or(0, Vec::len).saturating_mul(2),
            )?;
            let bases = direct_bases.get(&e).cloned().unwrap_or_default();
            todo.extend(bases.iter().copied());
            let imports = self.positional_imports(
                e,
                direct_bases,
                incomplete,
                &mut steps,
                &mut import_proof,
                &mut prerequisites,
            );
            if let Some(required) = prerequisites.get(&e) {
                charge(&mut steps, required.len())?;
                todo.extend(required.iter().copied());
            }
            let (owned, owned_memberships) = if workspace.one_shot {
                let owned_memberships = self.positional_owned_memberships(e, &mut steps);
                charge(&mut steps, 0)?;
                self.positional_charge_members(e, &mut steps)?;
                (self.owned_member_elems(e, true), owned_memberships)
            } else {
                if let std::collections::hash_map::Entry::Vacant(entry) = workspace.owned.entry(e) {
                    let owned_memberships = self.positional_owned_memberships(e, &mut steps);
                    charge(&mut steps, 0)?;
                    self.positional_charge_members(e, &mut steps)?;
                    entry.insert((self.owned_member_elems(e, true), owned_memberships));
                }
                let (owned, memberships) = &workspace.owned[&e];
                charge(
                    &mut steps,
                    owned
                        .len()
                        .saturating_add(memberships.as_ref().map_or(0, Vec::len)),
                )?;
                (owned.clone(), memberships.clone())
            };
            let memberships_complete = imports.is_some() && owned_memberships.is_some();
            let (public_imports, protected_imports) = imports.unwrap_or_default();
            nodes.insert(
                e,
                Node {
                    owned,
                    owned_memberships: owned_memberships.unwrap_or_default(),
                    bases,
                    public_imports,
                    protected_imports,
                    memberships_complete,
                },
            );
        }

        if let Some(reached) = workspace.reached.as_mut() {
            reached.extend(nodes.keys().copied());
        }
        // Iterative postorder avoids a native-stack dependency on model depth.
        // Cyclic bases have no well-founded positional ordering; do not guess.
        let mut state = HashMap::new();
        let mut order = Vec::new();
        charge(&mut steps, incomplete.len())?;
        let mut plan = PositionalRedefinitions {
            targets: HashMap::new(),
            incomplete: incomplete.clone(),
        };
        if let Some(library) = &library {
            charge(&mut steps, library.positional.incomplete.len())?;
            plan.incomplete
                .extend(library.positional.incomplete.iter().copied());
        }
        // Checked callers already hold this exact unique-identity snapshot.
        // Reuse its index rather than re-scanning every row for each small
        // positional closure. The fallback preserves compatibility planning
        // when no such structural certificate exists.
        let indexed_ids = self
            .stored_structure
            .as_ref()
            .filter(|raw| raw.ids_unique && raw.is_current(self))
            .cloned();
        if indexed_ids.is_none() && workspace.ids.is_none() {
            charge(&mut steps, self.explicit_len())?;
            workspace.ids = Some(
                self.elements
                    .iter()
                    .take(self.explicit_len())
                    .map(|e| e.id)
                    .collect(),
            );
        }
        let ids = workspace.ids.as_ref();
        for &e in nodes.keys() {
            charge(&mut steps, 1)?;
            let unresolved = if let Some(cached) = workspace.unresolved.get(&e) {
                *cached
            } else {
                charge(&mut steps, self.elements[e].owned_relationships.len())?;
                let value = self.elements[e].owned_relationships.iter().any(|&r| {
                    let rel = &self.elements[r];
                    conforms(rel.ty, "Specialization")
                        && ![
                            "general",
                            "superclassifier",
                            "type",
                            "subsettedFeature",
                            "redefinedFeature",
                            "referencedFeature",
                            "crossedFeature",
                        ]
                        .iter()
                        .find_map(|key| rel.props.get(key))
                        .and_then(|v| v.as_reference())
                        .is_some_and(|id| {
                            indexed_ids.as_ref().map_or_else(
                                || ids.is_some_and(|ids| ids.contains(&id)),
                                |raw| {
                                    raw.element_for_uuid(self, id)
                                        .is_some_and(|target| target < self.explicit_len())
                                },
                            )
                        })
                });
                if !workspace.one_shot {
                    workspace.unresolved.insert(e, value);
                }
                value
            };
            if unresolved {
                plan.incomplete.insert(e);
            }
        }
        for root in roots {
            let mut stack = vec![(root, false)];
            while let Some((e, exiting)) = stack.pop() {
                charge(&mut steps, 1)?;
                if exiting {
                    state.insert(e, 2);
                    order.push(e);
                } else {
                    // planned by the library: complete or not, it is done
                    if seeded(&e) {
                        continue;
                    }
                    match state.get(&e) {
                        Some(1) => {
                            plan.incomplete.insert(e);
                            continue;
                        }
                        Some(2) => continue,
                        _ => {}
                    }
                    state.insert(e, 1);
                    stack.push((e, true));
                    charge(&mut steps, nodes[&e].bases.len())?;
                    stack.extend(nodes[&e].bases.iter().rev().map(|&b| (b, false)));
                    if let Some(required) = prerequisites.get(&e) {
                        charge(&mut steps, required.len())?;
                        stack.extend(required.iter().rev().map(|&dependency| (dependency, false)));
                    }
                }
            }
        }

        // The library's rows' redefinitions, the positional ones its planning
        // added included, are in its final graph (`planned.redefinitions`).
        let mut redefinitions = HashMap::new();
        let from = library.as_ref().map_or(0, |l| l.spec_rows);
        for i in from..self.spec_targets.len() {
            let (e, kind, _, _) = self.spec_targets[i];
            charge(&mut steps, 1)?;
            if kind == "Redefinition" {
                if let Some(target) = self.spec_resolved.get(i).copied().flatten() {
                    redefinitions.entry(e).or_insert_with(Vec::new).push(target);
                }
            }
        }
        // The reduction reads only these fully gathered inputs and stored
        // rows. Re-gather imports and candidate bases first, then reuse a prior
        // complete result only when the entire consumed input is identical.
        // This is equality memoization, not an incremental dependency guess.
        let memoize =
            !workspace.one_shot && selected_roots.is_none() && result_candidates.is_none();
        if memoize {
            if let Some(cached) = &workspace.reduction {
                cached.charge_inputs(&mut steps)?;
                if cached.order == order
                    && cached.nodes == nodes
                    && cached.prerequisites == prerequisites
                    && cached.incomplete == plan.incomplete
                    && cached.redefinitions == redefinitions
                {
                    charge_plan(&cached.result, &mut steps)?;

                    return Some(cached.result.clone());
                }

                // Replacing an earlier complete result later also disposes its
                // owned vectors; account before doing that work.
                charge_plan(&cached.result, &mut steps)?;
            }
        }
        let initial = if memoize {
            charge(&mut steps, plan.incomplete.capacity())?;
            charge_map_vectors(&redefinitions, &mut steps)?;
            Some((plan.incomplete.clone(), redefinitions.clone()))
        } else {
            None
        };
        let mut effective: HashMap<usize, Vec<usize>> = HashMap::new();
        let mut roles: HashMap<usize, Roles> = HashMap::new();
        let mut exported: HashMap<usize, Vec<PositionalMembership>> = HashMap::new();
        let mut traversal = if selected_roots.is_some() {
            Reachability::sparse()
        } else {
            charge(&mut steps, self.explicit_len())?;
            Reachability::new(self.explicit_len())
        };
        let mut projection = Reduction::default();

        for &e in &order {
            charge(&mut steps, 1)?;
            let node = &nodes[&e];
            charge(&mut steps, node.bases.len())?;
            // A direct import contributes to this type's non-private view,
            // not its effective features. Unsupported visible sequences must
            // not supply a shortened list to a child's positional matching.
            if !node.memberships_complete {
                plan.incomplete.insert(e);
            }
            if node.bases.iter().any(|b| {
                plan.incomplete.contains(b)
                    || !(effective.contains_key(b) || planned.effective.contains_key(b))
            }) {
                plan.incomplete.insert(e);
            }
            if let Some(required) = prerequisites.get(&e) {
                charge(&mut steps, required.len())?;
                if required.iter().any(|dependency| {
                    plan.incomplete.contains(dependency)
                        || !(effective.contains_key(dependency)
                            || planned.effective.contains_key(dependency))
                }) {
                    plan.incomplete.insert(e);
                }
            }
            if plan.incomplete.contains(&e) {
                continue;
            }
            charge(&mut steps, node.owned.len().saturating_mul(4))?;
            let ends: Vec<_> = node
                .owned
                .iter()
                .copied()
                .filter(|&f| self.positional_is_end(f))
                .collect();
            let parameters: Vec<_> = node
                .owned
                .iter()
                .copied()
                .filter(|&f| self.is_parameter(f) && !self.positional_is_result(f))
                .collect();
            let results: Vec<_> = node
                .owned
                .iter()
                .copied()
                .filter(|&f| self.positional_is_result(f))
                .collect();
            let behavior =
                conforms(self.elements[e].ty, "Behavior") || conforms(self.elements[e].ty, "Step");
            let function = conforms(self.elements[e].ty, "Function")
                || conforms(self.elements[e].ty, "Expression");
            let subject_family = |kind| {
                if conforms(kind, "RequirementDefinition") || conforms(kind, "RequirementUsage") {
                    Some(0)
                } else if conforms(kind, "CaseDefinition") || conforms(kind, "CaseUsage") {
                    Some(1)
                } else {
                    None
                }
            };
            let is_subject = |feature: usize| {
                self.elements[feature]
                    .owning_relationship
                    .is_some_and(|r| conforms(self.elements[r].ty, "SubjectMembership"))
            };
            let subjects: Vec<_> = parameters
                .iter()
                .copied()
                .filter(|&f| is_subject(f))
                .collect();
            if subject_family(self.elements[e].ty).is_some() {
                for base in &node.bases {
                    charge(&mut steps, 1)?;
                    charge_sort(&mut steps, effective_of(&effective, planned, base).len())?;
                }
            }
            let subject_bases: Vec<_> = if let Some(family) = subject_family(self.elements[e].ty) {
                node.bases
                    .iter()
                    .filter(|&&base| subject_family(self.elements[base].ty) == Some(family))
                    .map(|&base| {
                        let mut subjects: Vec<_> = effective_of(&effective, planned, &base)
                            .iter()
                            .copied()
                            .filter(|&f| is_subject(f))
                            .collect();
                        subjects.sort_unstable();
                        subjects.dedup();
                        (base, subjects)
                    })
                    .collect()
            } else {
                Vec::new()
            };
            // A requirement/case subject redefines the specialized owner's
            // subject even when that subject is inherited. This is the SysML
            // subject rule, not a change to KerML's positional pairing.
            // Reject ambiguous subject views before emitting any local edges.
            charge(&mut steps, subject_bases.len())?;
            if subjects.len() > 1 || subject_bases.iter().any(|(_, s)| s.len() > 1) {
                plan.incomplete.insert(e);
                continue;
            }
            if let Some(&source) = subjects.first() {
                for (_, targets) in &subject_bases {
                    charge(&mut steps, 1)?;
                    if let Some(&target) = targets.first() {
                        add_edge(
                            source,
                            target,
                            &mut redefinitions,
                            &planned.redefinitions,
                            &mut plan.targets,
                            &mut traversal,
                            &mut steps,
                        )?;
                    }
                }
            }
            for &base in &node.bases {
                charge(&mut steps, 1)?;
                let base_roles = roles
                    .get(&base)
                    .or_else(|| planned.roles.get(&base))
                    .expect("a complete base has roles");
                charge(&mut steps, ends.len().min(base_roles.ends.len()))?;
                let base_ends = base_roles.ends.iter().copied();
                for (&source, target) in ends.iter().zip(base_ends) {
                    add_edge(
                        source,
                        target,
                        &mut redefinitions,
                        &planned.redefinitions,
                        &mut plan.targets,
                        &mut traversal,
                        &mut steps,
                    )?;
                }
                let base_kind = self.elements[base].ty;
                if behavior && (conforms(base_kind, "Behavior") || conforms(base_kind, "Step")) {
                    charge(
                        &mut steps,
                        parameters.len().min(base_roles.parameters.len()),
                    )?;
                    let base_parameters = base_roles.parameters.iter().copied();
                    for (&source, target) in parameters.iter().zip(base_parameters) {
                        charge(
                            &mut steps,
                            subject_bases
                                .len()
                                .saturating_add(self.elements[source].owned_relationships.len())
                                .saturating_add(1),
                        )?;
                        if subjects.contains(&source)
                            && subject_bases
                                .iter()
                                .any(|(owner, subjects)| *owner == base && !subjects.is_empty())
                        {
                            continue;
                        }
                        // KerML `checkFeatureParameterRedefinition` exempts
                        // only an invocation's argument that names what it
                        // redefines. Any other parameter takes over the
                        // general's parameter at its position even when it
                        // also redefines one explicitly: `in :>> b;` in a
                        // specialization of `Diff { in a; in b; }` redefines
                        // `a` as well as `b`, leaving one parameter.
                        let explicit_invocation_argument =
                            conforms(self.elements[e].ty, "InvocationExpression")
                                && self.elements[source].owned_relationships.iter().any(|&r| {
                                    conforms(self.elements[r].ty, "Redefinition")
                                        && self.elements[r]
                                            .props
                                            .get("isImplied")
                                            .and_then(|v| v.as_bool())
                                            != Some(true)
                                });
                        if !explicit_invocation_argument {
                            add_edge(
                                source,
                                target,
                                &mut redefinitions,
                                &planned.redefinitions,
                                &mut plan.targets,
                                &mut traversal,
                                &mut steps,
                            )?;
                        }
                    }
                }
                if function
                    && (conforms(base_kind, "Function") || conforms(base_kind, "Expression"))
                {
                    let base_results = &base_roles.results;
                    if results.len() > 1 || base_results.len() > 1 {
                        plan.incomplete.insert(e);
                    }
                    if results.len() == 1 && base_results.len() == 1 {
                        add_edge(
                            results[0],
                            base_results[0],
                            &mut redefinitions,
                            &planned.redefinitions,
                            &mut plan.targets,
                            &mut traversal,
                            &mut steps,
                        )?;
                    }
                }
            }
            let (features, surviving) = projection.reduce(
                node,
                &ExportedOver {
                    own: &exported,
                    library: &planned.exported,
                },
                &OverLibrary {
                    own: &redefinitions,
                    library: &planned.redefinitions,
                },
                &mut traversal,
                &CompatibilityMembershipFacts(self),
                &mut steps,
            )?;
            if subject_family(self.elements[e].ty).is_some() {
                charge_sort(&mut steps, features.len())?;
                let mut subjects: Vec<_> = features
                    .iter()
                    .copied()
                    .filter(|&f| is_subject(f))
                    .collect();
                subjects.sort_unstable();
                subjects.dedup();
                if subjects.len() > 1 {
                    plan.incomplete.insert(e);
                    continue;
                }
            }
            let visible = projection.export(
                node,
                surviving,
                &CompatibilityMembershipFacts(self),
                &mut steps,
            )?;
            exported.insert(e, visible);
            if function && !plan.incomplete.contains(&e) {
                if let Some(candidates) = result_candidates.as_deref_mut() {
                    charge(&mut steps, features.len())?;
                    let mut results = features
                        .iter()
                        .copied()
                        .filter(|&f| self.positional_is_result(f));
                    if let Some(result) = results.next() {
                        if results.next().is_none() {
                            candidates.insert(e, result);
                        }
                    }
                }
            }
            charge(&mut steps, features.len())?;
            // The slots a specialization pairs by position are the type's
            // effective ones — its own, then the inherited ones ordered
            // after them (KerML 7.4.7.2) — for parameters as for ends.
            let mut role_ends = Vec::new();
            let mut role_results = Vec::new();
            let mut role_parameters = Vec::new();
            for &feature in &features {
                if self.positional_is_end(feature) {
                    role_ends.push(feature);
                }
                if self.positional_is_result(feature) {
                    role_results.push(feature);
                } else if self.is_parameter(feature) {
                    role_parameters.push(feature);
                }
            }
            roles.insert(
                e,
                Roles {
                    ends: role_ends,
                    results: role_results,
                    parameters: role_parameters,
                },
            );
            effective.insert(e, features);
        }
        if let Some((incomplete, redefinitions)) = initial {
            charge_plan(&plan, &mut steps)?;
            workspace.reduction = Some(CompleteReduction {
                order,
                nodes,
                prerequisites,
                incomplete,
                redefinitions,
                result: plan.clone(),
            });
        }
        if let Some(out) = workspace.planned.as_mut() {
            *out = PlannedTypes {
                effective,
                roles,
                exported,
                redefinitions,
            };
        }
        Some(plan)
    }

    /// Charge ownership scans before owned_member_elems allocates its result.
    /// The unbounded legacy path avoids this additional accounting traversal.
    fn positional_charge_members(
        &self,
        owner: usize,
        steps: &mut Option<&mut usize>,
    ) -> Option<()> {
        if steps.is_none() {
            return Some(());
        }
        charge(steps, self.elements[owner].owned_relationships.len())?;
        let mut children = 0usize;
        for &relation in &self.elements[owner].owned_relationships {
            let count = self.elements[relation].children.len();
            charge(steps, count)?;
            children = children.saturating_add(count);
        }
        // owned_member_elems sorts before deduplication. Include all stored
        // children as a conservative upper bound on its collected members.
        charge_sort(steps, children)
    }

    /// Keep the compatibility selector as the fast path. Canonical composition
    /// may additionally consume the checked Namespace import algebra without
    /// recursively asking for a Type certificate during positional planning.
    fn positional_imports(
        &mut self,
        owner: usize,
        bases: &dyn DirectBases,
        incomplete: &HashSet<usize>,
        steps: &mut Option<&mut usize>,
        proof: &mut ImportProof,
        prerequisites: &mut HashMap<usize, Vec<usize>>,
    ) -> Option<(Vec<PositionalMembership>, Vec<PositionalMembership>)> {
        let leaf = self.positional_leaf_imports(owner, bases, incomplete, steps);
        if self.graph_format != crate::model::GraphFormat::CanonicalV3 {
            return leaf;
        }
        // Existing leaf selectors need no extra work unless an imported
        // Feature can bring a foreign positional Redefinition dependency.
        if let Some(imports) = leaf {
            charge(steps, imports.0.len().saturating_add(imports.1.len()))?;
            if !imports
                .0
                .iter()
                .chain(&imports.1)
                .any(|m| conforms(self.elements[m.member].ty, "Feature"))
            {
                return Some(imports);
            }
            let mut local_steps = 0;
            let steps = steps.as_deref_mut().unwrap_or(&mut local_steps);
            let raw = super::structural_index::StoredStructure::for_query(self, steps)?;
            let required = self.positional_import_source_dependencies(
                &raw,
                &imports,
                ImportSourceContext {
                    owner,
                    bases,
                    incomplete,
                    ordinary_only: false,
                    allow_prerequisites: true,
                },
                steps,
                proof,
            )?;
            if !required.is_empty() {
                prerequisites.insert(owner, required);
            }
            return Some(imports);
        }
        // Even an otherwise unbounded publication must not make the checked
        // import traversal unbounded. Bounded callers retain their allowance.
        if self
            .elem_scope
            .get(&owner)
            .is_some_and(|&s| !self.scopes[s].filters.is_empty())
        {
            return None;
        }
        let mut local_steps = 0;
        let steps = steps.as_deref_mut().unwrap_or(&mut local_steps);
        let raw = super::structural_index::StoredStructure::for_query(self, steps)?;
        if !raw.ids_unique || raw.annotations_incomplete || self.metadata_associations_incomplete {
            return None;
        }
        // The checked Type caller establishes these domains before asking for
        // selectors; the publication planner must establish them independently.
        if !raw.import_domains(self, steps)?.owner_complete(owner)
            || !raw.membership_domains(self, steps)?.owner_complete(owner)
            || raw.metadata_annotation_targets.contains(&owner)
            || self.metadata_of.get(&owner).is_some_and(|v| !v.is_empty())
        {
            return None;
        }
        let relationships = super::semantic_ownership::owned_relationships(self, owner)?;
        charge(&mut Some(&mut *steps), relationships.len())?;
        if relationships
            .iter()
            .any(|rel| conforms(self.elements[rel].ty, "ElementFilterMembership"))
        {
            return None;
        }
        let imports =
            super::operations::namespaces::imports::type_imports(self, &raw, owner, &[], steps)
                .ok()?;
        let required = self.positional_import_source_dependencies(
            &raw,
            &imports,
            ImportSourceContext {
                owner,
                bases,
                incomplete,
                ordinary_only: true,
                allow_prerequisites: true,
            },
            steps,
            proof,
        )?;
        if !required.is_empty() {
            prerequisites.insert(owner, required);
        }
        Some(imports)
    }

    /// Prove imported Redefinition sources and their planning dependencies.
    /// Existing ancestry remains sufficient. Foreign positional roles need a
    /// complete ordinary owner domain, never an inheritance contribution.
    /// Authored role sources must target strict actual ancestors; cycles and
    /// arbitrary cross-owner positional dependencies remain qualified.
    fn positional_import_source_dependencies(
        &mut self,
        raw: &super::structural_index::StoredStructure,
        imports: &(Vec<PositionalMembership>, Vec<PositionalMembership>),
        context: ImportSourceContext<'_>,
        steps: &mut usize,
        proof: &mut ImportProof,
    ) -> Option<Vec<usize>> {
        if !raw.ids_unique || raw.annotations_incomplete || self.metadata_associations_incomplete {
            return None;
        }
        let mut budget = Some(steps);
        charge(&mut budget, imports.0.len().saturating_add(imports.1.len()))?;
        let mut todo: Vec<_> = imports
            .0
            .iter()
            .chain(&imports.1)
            .filter_map(|m| conforms(self.elements[m.member].ty, "Feature").then_some(m.member))
            .collect();
        if todo.is_empty() {
            return Some(Vec::new());
        }
        charge(&mut budget, todo.len())?;
        let roots = todo.clone();
        let steps = budget?;
        let inverse = raw.typing(self, steps)?;
        if inverse.sources_incomplete {
            return None;
        }
        let domains = raw.membership_domains(self, steps)?;
        let mut seen = HashSet::new();
        let mut dependency = Reachability::sparse();
        let mut owners = HashMap::new();
        let mut authored = HashMap::new();
        let mut redefinitions = HashMap::new();
        let mut roles = HashSet::new();
        let mut external_roles = HashSet::new();
        let mut required = Vec::new();
        while let Some(feature) = todo.pop() {
            charge(&mut Some(&mut *steps), 1)?;
            if !seen.insert(feature) {
                continue;
            }
            let row = self.elements.get(feature)?;
            if (context.ordinary_only && row.ty != "Feature")
                || row
                    .props
                    .get("isEnd")
                    .is_some_and(|v| v.as_bool().is_none())
                || row.props.get("direction").is_some_and(|v| {
                    !v.is_null() && !matches!(v.as_str(), Some("in" | "out" | "inout"))
                })
                || raw.bad_bases.contains(&feature)
                || raw.metadata_annotation_targets.contains(&feature)
                || self
                    .metadata_of
                    .get(&feature)
                    .is_some_and(|v| !v.is_empty())
            {
                return None;
            }
            // An absent direction does not make a Return/Subject/Parameter
            // membership nonpositional. Admit only these exact ordinary kinds.
            let membership = row.owning_relationship?;
            let kind = self.elements[membership].ty;
            if kind == "EndFeatureMembership" && !self.positional_is_end(feature) {
                return None;
            }
            if if context.ordinary_only {
                !matches!(
                    kind,
                    "FeatureMembership"
                        | "EndFeatureMembership"
                        | "ParameterMembership"
                        | "ReturnParameterMembership"
                        | "OwningMembership"
                )
            } else {
                kind != "OwningMembership" && !conforms(kind, "FeatureMembership")
            } {
                return None;
            }
            let owner = super::semantic_ownership::checked_relationship_carrier(
                self, raw, membership, steps,
            )??;
            if !domains.owner_complete(owner)
                || raw.metadata_annotation_targets.contains(&owner)
                || self.metadata_of.get(&owner).is_some_and(|v| !v.is_empty())
                || super::membership_evidence::member(self, raw, owner, membership, steps)
                    != Some(feature)
            {
                return None;
            }
            owners.insert(feature, owner);
            let positional = self.positional_is_end(feature) || self.is_parameter(feature);
            if positional {
                roles.insert(feature);
                let external = !dependency.reaches_budget(
                    context.owner,
                    owner,
                    context.bases,
                    &mut Some(&mut *steps),
                )?;
                if external || context.ordinary_only || !context.allow_prerequisites {
                    let ordinary_end = row.ty == "Feature"
                        && self.positional_is_end(feature)
                        && !self.is_parameter(feature)
                        && row.props.get("direction").is_none_or(|v| v.is_null())
                        && matches!(kind, "FeatureMembership" | "EndFeatureMembership")
                        && self.elements[owner].ty == "Class";
                    let ordinary_parameter = if row.ty == "Feature"
                        && !self.positional_is_end(feature)
                        && matches!(self.elements[owner].ty, "Behavior" | "Function")
                        && matches!(
                            kind,
                            "FeatureMembership"
                                | "ParameterMembership"
                                | "ReturnParameterMembership"
                        ) {
                        let direction = super::membership_evidence::parameter_direction(
                            self, raw, feature, steps,
                        )??;
                        match kind {
                            "ParameterMembership" => direction == "in",
                            "ReturnParameterMembership" => {
                                self.elements[owner].ty == "Function" && direction == "out"
                            }
                            _ => matches!(direction, "in" | "out" | "inout"),
                        }
                    } else {
                        false
                    };
                    if !ordinary_end && !ordinary_parameter {
                        return None;
                    }
                }
                if external {
                    if !context.allow_prerequisites {
                        return None;
                    }
                    external_roles.insert(feature);
                    required.push(owner);
                }
            } else if context.ordinary_only
                && row.props.get("direction").is_some_and(|v| !v.is_null())
            {
                return None;
            }
            let owned = super::semantic_ownership::owned_relationships(self, feature)?;
            let incoming = inverse
                .relationships
                .get(&feature)
                .map_or(&[][..], Vec::as_slice);
            charge(
                &mut Some(&mut *steps),
                owned.len().saturating_add(incoming.len()),
            )?;
            let relationships: Vec<_> = owned.iter().chain(incoming.iter().copied()).collect();
            let mut seen_relationships = HashSet::new();
            let mut authored_targets = Vec::new();
            let mut targets = Vec::new();
            for relationship in relationships {
                if !conforms(self.elements[relationship].ty, "Redefinition")
                    || !seen_relationships.insert(relationship)
                {
                    continue;
                }
                let carrier = super::semantic_ownership::checked_relationship_carrier(
                    self,
                    raw,
                    relationship,
                    steps,
                )?;
                if carrier != Some(feature) {
                    return None;
                }
                let target = super::type_relations::endpoint_with_carrier(
                    self,
                    feature,
                    carrier,
                    relationship,
                    &["specific", "subsettingFeature", "redefiningFeature"],
                    &["general", "subsettedFeature", "redefinedFeature"],
                    "Feature",
                    steps,
                )?;
                if relationship < self.explicit_len() {
                    authored_targets.push(target);
                }
                targets.push(target);
                todo.push(target);
            }
            authored.insert(feature, authored_targets);
            redefinitions.insert(feature, targets);
        }
        // The central reducer consumes resolved recorded edges. Prove those
        // selectors match the exact current authored closure we just inspected.
        if proof.recorded.is_none() {
            proof.recorded = Some(RecordedRedefinitions::build(self, steps)?);
        }
        if !proof.recorded.as_ref()?.sources_match(&authored, steps)? {
            return None;
        }
        if !external_roles.is_empty() || !context.allow_prerequisites {
            let mut closure = Reachability::sparse();
            let mut acyclic = HashMap::new();
            for root in roots {
                let reached =
                    closure.reachable_budget(root, &redefinitions, &mut Some(&mut *steps))?;
                charge(&mut Some(&mut *steps), reached.len().saturating_mul(2))?;
                let needs_order = reached.iter().any(|source| {
                    if context.allow_prerequisites {
                        external_roles.contains(source)
                    } else {
                        roles.contains(source)
                    }
                });
                if needs_order
                    && reached.iter().any(|source| {
                        authored
                            .get(source)
                            .is_some_and(|targets| !targets.is_empty())
                    })
                {
                    // A role-free relay generates no positional candidate of
                    // its own. Its reachable foreign roles are scheduled before
                    // reduction. A positional authored source is safe only when
                    // every authored target belongs to a strict actual ancestor,
                    // whose generated edges already exist before add_edge runs.
                    charge(&mut Some(&mut *steps), reached.len())?;
                    for &source in reached {
                        let targets = authored.get(&source).map_or(&[][..], Vec::as_slice);
                        charge(&mut Some(&mut *steps), targets.len())?;
                        if roles.contains(&source) {
                            for target in targets {
                                let owner = owners[&source];
                                let target_owner = owners[target];
                                if owner == target_owner
                                    || !dependency.reaches_budget(
                                        owner,
                                        target_owner,
                                        context.bases,
                                        &mut Some(&mut *steps),
                                    )?
                                {
                                    return None;
                                }
                            }
                        }
                    }
                    acyclic_redefinition_closure(root, &redefinitions, &mut acyclic, steps)?;
                }
            }
        }
        charge(&mut Some(&mut *steps), required.len())?;
        let mut unique = HashSet::new();
        required.retain(|owner| unique.insert(*owner));
        for &owner in &required {
            self.positional_role_prerequisite_domain(
                raw,
                owner,
                context.bases,
                context.incomplete,
                steps,
                proof,
            )?;
        }
        Some(required)
    }

    /// Validate the complete foreign owner/base domain before scheduling it.
    /// Shared plain-package imports and ordered authored closures are admitted
    /// only when every reachable positional owner belongs to real ancestry.
    fn positional_role_prerequisite_domain(
        &mut self,
        raw: &super::structural_index::StoredStructure,
        root: usize,
        bases: &dyn DirectBases,
        incomplete: &HashSet<usize>,
        steps: &mut usize,
        proof: &mut ImportProof,
    ) -> Option<()> {
        charge(&mut Some(&mut *steps), 1)?;
        if !matches!(self.elements[root].ty, "Class" | "Behavior" | "Function") {
            return None;
        }
        if proof.role_domains.contains(&root) {
            return Some(());
        }
        let domains = raw.membership_domains(self, steps)?;
        let imports = raw.import_domains(self, steps)?;
        let mut visited = HashSet::new();
        let mut todo = vec![root];
        while let Some(owner) = todo.pop() {
            charge(&mut Some(&mut *steps), 1)?;
            if proof.role_domains.contains(&owner) || !visited.insert(owner) {
                continue;
            }
            if !matches!(
                self.elements[owner].ty,
                "Class" | "Classifier" | "Behavior" | "Function"
            ) || incomplete.contains(&owner)
                || raw.bad_bases.contains(&owner)
                || !domains.owner_complete(owner)
                || !imports.owner_complete(owner)
                || raw.metadata_annotation_targets.contains(&owner)
                || self.metadata_of.get(&owner).is_some_and(|v| !v.is_empty())
                || self
                    .elem_scope
                    .get(&owner)
                    .is_some_and(|&s| !self.scopes[s].filters.is_empty())
            {
                return None;
            }
            let base = bases.get(&owner).map_or(&[][..], Vec::as_slice);
            charge(&mut Some(&mut *steps), base.len())?;
            todo.extend(base.iter().copied());
            let relationships = super::semantic_ownership::owned_relationships(self, owner)?;
            charge(&mut Some(&mut *steps), relationships.len())?;
            let relationships: Vec<_> = relationships.iter().collect();
            let mut features = Vec::new();
            let mut visible_imports = false;
            for relationship in relationships {
                if super::semantic_ownership::checked_relationship_carrier(
                    self,
                    raw,
                    relationship,
                    steps,
                )? != Some(owner)
                {
                    return None;
                }
                let kind = self.elements[relationship].ty;
                if conforms(kind, "Conjugation") || conforms(kind, "ElementFilterMembership") {
                    return None;
                }
                if conforms(kind, "Import") {
                    super::import_memberships::checked_import_target(
                        self,
                        raw,
                        owner,
                        relationship,
                        steps,
                    )?;
                    match self.elements[relationship].props.get("visibility") {
                        None => {}
                        Some(value) => match value.as_str() {
                            Some("private") => {}
                            Some("public" | "protected") => visible_imports = true,
                            _ => return None,
                        },
                    }
                }
                if conforms(kind, "Membership") {
                    let member =
                        super::membership_evidence::member(self, raw, owner, relationship, steps)?;
                    if conforms(self.elements[member].ty, "Feature") {
                        features.push(PositionalMembership {
                            relationship,
                            member,
                        });
                    }
                }
            }
            if visible_imports {
                // Reuse the exact visibility-specific selector without entering
                // Type proofs. Selector completeness does not replace the checked
                // caller's independent lookup-provider certificate.
                let selected = super::operations::namespaces::imports::type_imports(
                    self,
                    raw,
                    owner,
                    &[],
                    steps,
                )
                .ok()?;
                self.positional_import_source_dependencies(
                    raw,
                    &selected,
                    ImportSourceContext {
                        owner,
                        bases,
                        incomplete,
                        ordinary_only: true,
                        allow_prerequisites: false,
                    },
                    steps,
                    proof,
                )?;
            }
            self.positional_import_source_dependencies(
                raw,
                &(features, Vec::new()),
                ImportSourceContext {
                    owner,
                    bases,
                    incomplete,
                    ordinary_only: false,
                    allow_prerequisites: false,
                },
                steps,
                proof,
            )?;
        }
        charge(&mut Some(&mut *steps), visited.len())?;
        proof.role_domains.extend(visited);
        Some(())
    }

    /// Existing dependency-free selector, retained unchanged for LegacyV2 and
    /// as the allocation-free no-import / admitted-leaf fast path in CanonicalV3.
    fn positional_leaf_imports(
        &mut self,
        owner: usize,
        bases: &dyn DirectBases,
        incomplete: &HashSet<usize>,
        steps: &mut Option<&mut usize>,
    ) -> Option<(Vec<PositionalMembership>, Vec<PositionalMembership>)> {
        charge(steps, self.elements[owner].owned_relationships.len())?;
        let imports: Vec<_> = self.elements[owner]
            .owned_relationships
            .iter()
            .copied()
            .filter(|&r| {
                conforms(self.elements[r].ty, "Import")
                    && self.import_admitted(r, super::LookupAccess::Protected)
            })
            .collect();
        if imports.is_empty() {
            return Some(Default::default());
        }
        if self
            .elem_scope
            .get(&owner)
            .is_some_and(|&s| !self.scopes[s].filters.is_empty())
        {
            return None;
        }
        let mut candidates = Vec::new();
        for import in imports {
            charge(steps, 1)?;
            if self.elements[import]
                .props
                .get("isRecursive")
                .and_then(|v| v.as_bool())
                == Some(true)
            {
                return None;
            }
            let protected = self.elements[import]
                .props
                .get("visibility")
                .and_then(|v| v.as_str())
                == Some("protected");
            let memberships = if conforms(self.elements[import].ty, "MembershipImport") {
                let membership = self.positional_reference(import, "importedMembership")?;
                let declaring = self.positional_reference(membership, "owningRelatedElement")?;
                if !self.positional_import_leaf(declaring, bases, incomplete, steps)? {
                    return None;
                }
                vec![membership]
            } else {
                let target = self.positional_reference(import, "importedNamespace")?;
                if !self.positional_import_leaf(target, bases, incomplete, steps)? {
                    return None;
                }
                let access = if self.elements[import]
                    .props
                    .get("isImportAll")
                    .and_then(|v| v.as_bool())
                    == Some(true)
                {
                    super::LookupAccess::All
                } else {
                    super::LookupAccess::Public
                };
                charge(steps, self.elements[target].owned_relationships.len())?;
                self.elements[target]
                    .owned_relationships
                    .iter()
                    .copied()
                    .filter(|&r| {
                        conforms(self.elements[r].ty, "Membership")
                            && self.import_admitted(r, access)
                    })
                    .collect()
            };
            charge(steps, memberships.len())?;
            candidates.extend(memberships.into_iter().map(|m| (m, protected)));
        }
        // Type::nonPrivateMemberships composes visibility-specific imports,
        // not Namespace::importedMemberships' collision-pruned projection.
        // Position follows these membership identities even when names collide.
        let mut result = (Vec::new(), Vec::new());
        for (membership, protected) in candidates {
            charge(steps, 1)?;
            // Aliases participate in inherited redefinition filtering even
            // though only FeatureMemberships can become positional slots.
            let member = self.stored_membership_member(membership)?;
            let membership = PositionalMembership {
                relationship: membership,
                member,
            };
            if protected {
                result.1.push(membership);
            } else {
                result.0.push(membership);
            }
        }
        Some(result)
    }

    fn positional_import_leaf(
        &self,
        owner: usize,
        bases: &dyn DirectBases,
        incomplete: &HashSet<usize>,
        steps: &mut Option<&mut usize>,
    ) -> Option<bool> {
        charge(
            steps,
            self.elements[owner]
                .owned_relationships
                .len()
                .saturating_add(1),
        )?;
        Some(
            !incomplete.contains(&owner)
                && bases.get(&owner).is_none_or(Vec::is_empty)
                && !self.elements[owner].owned_relationships.iter().any(|&r| {
                    conforms(self.elements[r].ty, "Import")
                        || conforms(self.elements[r].ty, "Specialization")
                })
                && self
                    .elem_scope
                    .get(&owner)
                    .is_none_or(|&s| self.scopes[s].filters.is_empty()),
        )
    }

    fn positional_reference(&mut self, e: usize, key: &str) -> Option<usize> {
        let id = self.elements[e].props.get(key)?.as_reference()?;
        self.element_index_of_uuid(id)
    }

    pub(super) fn positional_is_end(&self, e: usize) -> bool {
        self.elements[e]
            .props
            .get("isEnd")
            .and_then(|v| v.as_bool())
            == Some(true)
    }

    pub(super) fn positional_is_result(&self, e: usize) -> bool {
        self.elements[e]
            .owning_relationship
            .is_some_and(|r| conforms(self.elements[r].ty, "ReturnParameterMembership"))
    }

    fn positional_owned_memberships(
        &mut self,
        owner: usize,
        steps: &mut Option<&mut usize>,
    ) -> Option<Vec<PositionalMembership>> {
        charge(
            steps,
            self.elements[owner]
                .owned_relationships
                .len()
                .saturating_mul(2),
        )?;
        let relationships: Vec<_> = self.elements[owner]
            .owned_relationships
            .iter()
            .copied()
            .filter(|&r| {
                conforms(self.elements[r].ty, "Membership")
                    && self.import_admitted(r, super::LookupAccess::Protected)
            })
            .collect();
        relationships
            .into_iter()
            .map(|relationship| {
                Some(PositionalMembership {
                    relationship,
                    member: self.stored_membership_member(relationship)?,
                })
            })
            .collect()
    }

    pub(super) fn semantic_redefinition_targets(
        &mut self,
        e: usize,
        include_implied: bool,
    ) -> Vec<usize> {
        let mut targets = self.indexed_redefinition_targets(e);
        if include_implied
            && self.semantic_ready
            && self.dynamic_evidence_current(e)
            && self.result_redefinition_evidence_current(e)
        {
            if self.effective_positional_redefinitions().is_none() {
                self.ensure_positional_redefinitions();
            }
            for &target in self
                .effective_positional_redefinitions()
                .and_then(|plan| plan.targets.get(&e))
                .into_iter()
                .flatten()
            {
                if !targets.contains(&target) {
                    targets.push(target);
                }
            }
        }
        targets
    }
}

// Structural cycle evidence for newly admitted authored/positional closures.
// This validates the inspected graph; the common planner still derives all edges.
fn acyclic_redefinition_closure(
    root: usize,
    graph: &HashMap<usize, Vec<usize>>,
    state: &mut HashMap<usize, u8>,
    steps: &mut usize,
) -> Option<()> {
    let mut todo = vec![(root, false)];
    while let Some((source, exiting)) = todo.pop() {
        charge(&mut Some(&mut *steps), 1)?;
        if exiting {
            state.insert(source, 2);
            continue;
        }
        match state.get(&source) {
            Some(1) => return None,
            Some(2) => continue,
            _ => {}
        }
        state.insert(source, 1);
        todo.push((source, true));
        if let Some(targets) = graph.get(&source) {
            charge(&mut Some(&mut *steps), targets.len())?;
            todo.extend(targets.iter().rev().map(|&target| (target, false)));
        }
    }
    Some(())
}

/// Add `source → target` to `graph` (read over `library`'s, whose list a
/// source's own starts from) unless it is already implied.
fn add_edge(
    source: usize,
    target: usize,
    graph: &mut HashMap<usize, Vec<usize>>,
    library: &HashMap<usize, Vec<usize>>,
    added: &mut HashMap<usize, Vec<usize>>,
    traversal: &mut Reachability,
    steps: &mut Option<&mut usize>,
) -> Option<()> {
    let over = OverLibrary {
        own: graph,
        library,
    };
    if !traversal.reaches_budget(source, target, &over, steps)? {
        charge(steps, 1)?;
        graph
            .entry(source)
            .or_insert_with(|| library.get(&source).cloned().unwrap_or_default())
            .push(target);
        added.entry(source).or_default().push(target);
    }
    Some(())
}

/// A complete type's effective features: planned here, or by the library.
fn effective_of<'a>(
    effective: &'a HashMap<usize, Vec<usize>>,
    planned: &'a PlannedTypes,
    e: &usize,
) -> &'a Vec<usize> {
    effective
        .get(e)
        .or_else(|| planned.effective.get(e))
        .expect("a complete base has effective features")
}

fn charge_sort(steps: &mut Option<&mut usize>, size: usize) -> Option<()> {
    charge(steps, size.saturating_mul(size.max(1).ilog2() as usize + 2))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn canonical_recursive_and_cyclic_package_selectors_support_positional_publication() {
        for provider in [
            "class Marker; package P {package Q {alias Alias for Marker;}} class A {public import P::**; end feature own;}",
            "package P {class Marker; public import Q::*;} package Q {public import P::*;} class A {public import P::*; end feature own;}",
        ] {
            for format in [
                crate::model::GraphFormat::LegacyV2,
                crate::model::GraphFormat::CanonicalV3,
            ] {
                let mut model = crate::model::Model::with_graph_format(format);
                let source =
                    format!("{provider} class B specializes A {{end feature replacement;}}");
                let unit = model.add_source("package-selector-publication.kerml", &source);
                assert!(unit.diagnostics.is_empty(), "{:?}", unit.diagnostics);
                let mut r = super::super::ResolvedModel::build(&model);
                let owner = r.resolve_qualified("B").unwrap().0;
                let own = r.resolve_qualified("A::own").unwrap().0;
                let replacement = r.resolve_qualified("B::replacement").unwrap().0;
                // This tests the central positional selector independently of
                // the stricter checked Type scope-completeness certificate.
                // The imported memberships contain no positional Features.
                assert!(r.b.ensure_positional_redefinitions_with_budget(&mut 0));
                let plan = r.b.positional_redefinitions.as_ref().unwrap();
                if format == crate::model::GraphFormat::CanonicalV3 {
                    assert!(!plan.incomplete.contains(&owner), "{source}");
                    assert_eq!(plan.targets.get(&replacement), Some(&vec![own]), "{source}");
                } else {
                    assert!(plan.incomplete.contains(&owner), "{source}");
                    assert!(!plan.targets.contains_key(&replacement), "{source}");
                }
            }
        }
    }

    #[test]
    fn expanded_import_publication_refuses_stale_recorded_redefinition_targets() {
        let mut model =
            crate::model::Model::with_graph_format(crate::model::GraphFormat::CanonicalV3);
        let unit = model.add_source("import-recorded-redefinition.kerml", "class Target {feature original;} class Other {feature different;} class External specializes Target {feature selected redefines Target::original;} class Provider {public import External::selected; end feature own;} class Child specializes Provider {end feature replacement;}");
        assert!(unit.diagnostics.is_empty(), "{:?}", unit.diagnostics);
        let mut r = super::super::ResolvedModel::build(&model);
        let selected = r.resolve_qualified("External::selected").unwrap().0;
        let different = r.resolve_qualified("Other::different").unwrap().0;
        let own = r.resolve_qualified("Provider::own").unwrap().0;
        let child = r.resolve_qualified("Child").unwrap().0;
        let replacement = r.resolve_qualified("Child::replacement").unwrap().0;
        let (bases, incomplete) = r.b.positional_direct_bases();
        let healthy = r
            .b
            .plan_positional_redefinitions_with_bases_and_budget(&bases, &incomplete, Some(&mut 0))
            .unwrap();
        assert_eq!(healthy.targets.get(&replacement), Some(&vec![own]));
        let index =
            r.b.spec_targets
                .iter()
                .position(|&(source, kind, _, _)| source == selected && kind == "Redefinition")
                .unwrap();
        let original = r.b.spec_resolved[index];
        r.b.spec_resolved[index] = Some(different);
        let refused = r
            .b
            .plan_positional_redefinitions_with_bases_and_budget(&bases, &incomplete, Some(&mut 0))
            .unwrap();
        assert!(refused.incomplete.contains(&child));
        assert!(!refused.targets.contains_key(&replacement));
        r.b.spec_resolved[index] = original;
        let recovered = r
            .b
            .plan_positional_redefinitions_with_bases_and_budget(&bases, &incomplete, Some(&mut 0))
            .unwrap();
        assert_eq!(recovered.targets.get(&replacement), Some(&vec![own]));
    }

    #[test]
    fn reduction_workspace_does_not_reuse_changed_recorded_redefinitions() {
        let mut model = crate::model::Model::new();
        model.add_source(
            "workspace-redefinition.kerml",
            "function A {in p;} function B specializes A {in q redefines A::p;}",
        );
        assert!(!model.has_errors());
        let mut r = super::super::ResolvedModel::build(&model);
        let (bases, incomplete) = r.b.positional_direct_bases();
        let mut workspace = PositionalWorkspace::default();
        r.b.plan_positional_redefinitions_with_workspace(
            &bases,
            &incomplete,
            Some(&mut 0),
            &mut workspace,
        )
        .unwrap();
        let index =
            r.b.spec_targets
                .iter()
                .position(|(_, kind, _, _)| *kind == "Redefinition")
                .unwrap();
        let source = r.b.spec_targets[index].0;
        let rows = r.b.elements.observe_revision();
        assert!(
            workspace
                .reduction
                .as_ref()
                .unwrap()
                .redefinitions
                .contains_key(&source)
        );
        r.b.spec_resolved[index] = None;
        assert!(r.b.elements.revision().unwrap().same_as(&rows));
        let reused =
            r.b.plan_positional_redefinitions_with_workspace(
                &bases,
                &incomplete,
                Some(&mut 0),
                &mut workspace,
            )
            .unwrap();
        let fresh = r
            .b
            .plan_positional_redefinitions_with_bases_and_budget(&bases, &incomplete, Some(&mut 0))
            .unwrap();
        assert_eq!(reused.targets, fresh.targets);
        assert_eq!(reused.incomplete, fresh.incomplete);
        assert!(
            !workspace
                .reduction
                .as_ref()
                .unwrap()
                .redefinitions
                .contains_key(&source)
        );
    }

    #[test]
    fn transaction_workspace_recomputes_candidate_and_import_dependencies() {
        let mut model = crate::model::Model::new();
        model.add_source("workspace.kerml", "package P {feature x;} function A {public import P::*; in p; return result;} function B {in q; return r;}");
        assert!(!model.has_errors());
        let mut r = super::super::ResolvedModel::build(&model);
        let find = |name: &str| {
            r.b.elements
                .iter()
                .position(|e| e.props.get("declaredName").and_then(|v| v.as_str()) == Some(name))
                .unwrap()
        };
        let (a, b, p) = (find("A"), find("B"), find("P"));
        let (mut bases, mut incomplete) = r.b.positional_direct_bases();
        let mut workspace = PositionalWorkspace::default();
        let mut first_steps = 0;
        let first =
            r.b.plan_positional_redefinitions_with_workspace(
                &bases,
                &incomplete,
                Some(&mut first_steps),
                &mut workspace,
            )
            .unwrap();
        let mut warm_steps = 0;
        let warm =
            r.b.plan_positional_redefinitions_with_workspace(
                &bases,
                &incomplete,
                Some(&mut warm_steps),
                &mut workspace,
            )
            .unwrap();
        assert_eq!(first.targets, warm.targets);
        assert_eq!(first.incomplete, warm.incomplete);
        assert!(warm_steps < first_steps);
        super::super::structural_index::StoredStructure::for_query(&mut r.b, &mut 0).unwrap();
        let indexed = r
            .b
            .plan_positional_redefinitions_with_bases_and_budget(&bases, &incomplete, Some(&mut 0))
            .unwrap();
        assert_eq!(indexed.targets, first.targets);
        assert_eq!(indexed.incomplete, first.incomplete);
        let mut retried_workspace = PositionalWorkspace::default();
        let mut exhausted = crate::eval::MAX_STEPS - 1;
        assert!(
            r.b.plan_positional_redefinitions_with_workspace(
                &bases,
                &incomplete,
                Some(&mut exhausted),
                &mut retried_workspace
            )
            .is_none()
        );
        let retried =
            r.b.plan_positional_redefinitions_with_workspace(
                &bases,
                &incomplete,
                Some(&mut 0),
                &mut retried_workspace,
            )
            .unwrap();
        assert_eq!(retried.targets, first.targets);
        assert_eq!(retried.incomplete, first.incomplete);
        bases.entry(b).or_default().push(a);
        for qualify_provider in [false, true] {
            if qualify_provider {
                incomplete.insert(p);
            }
            let reused =
                r.b.plan_positional_redefinitions_with_workspace(
                    &bases,
                    &incomplete,
                    Some(&mut 0),
                    &mut workspace,
                )
                .unwrap();
            let fresh =
                r.b.plan_positional_redefinitions_with_bases_and_budget(
                    &bases,
                    &incomplete,
                    Some(&mut 0),
                )
                .unwrap();
            assert_eq!(reused.targets, fresh.targets);
            assert_eq!(reused.incomplete, fresh.incomplete);
            if qualify_provider {
                assert!(reused.incomplete.contains(&a));
            }
        }
        r.b.elements[a]
            .props
            .insert("isAbstract", serde_json::json!(true));
        assert!(
            r.b.plan_positional_redefinitions_with_workspace(
                &bases,
                &incomplete,
                Some(&mut 0),
                &mut workspace
            )
            .is_none()
        );
        assert!(
            r.b.plan_positional_redefinitions_with_bases_and_budget(
                &bases,
                &incomplete,
                Some(&mut 0)
            )
            .is_some()
        );
    }

    #[test]
    fn bounded_supplied_planning_matches_unbounded_and_refuses_the_entire_budget_prefix() {
        let mut model = crate::model::Model::new();
        model.add_source("budget.kerml", "function A {in p; return result;} function B specializes A {in q; return r;} function C specializes B {in s; return t;} feature call=C(1);");
        assert!(!model.has_errors());
        let mut r = super::super::ResolvedModel::build(&model);
        r.b.ensure_positional_redefinitions();
        let published = r.b.positional_redefinitions.clone().unwrap();
        let (bases, incomplete) = r.b.positional_direct_bases();
        let mut measured = r.b.clone();
        let mut used = 0;
        let complete = measured
            .plan_positional_redefinitions_with_bases_and_budget(
                &bases,
                &incomplete,
                Some(&mut used),
            )
            .unwrap();
        assert_eq!(complete.targets, published.targets);
        assert_eq!(complete.incomplete, published.incomplete);
        assert!(used > 1 && used < crate::eval::MAX_STEPS);
        let mut interrupted = r.b.clone();
        let mut budget = crate::eval::MAX_STEPS - used + 1;
        assert!(
            interrupted
                .plan_positional_redefinitions_with_bases_and_budget(
                    &bases,
                    &incomplete,
                    Some(&mut budget)
                )
                .is_none()
        );
        assert!(budget > crate::eval::MAX_STEPS);
        assert_eq!(
            interrupted
                .positional_redefinitions
                .as_ref()
                .unwrap()
                .targets,
            published.targets
        );
        assert_eq!(
            interrupted
                .positional_redefinitions
                .as_ref()
                .unwrap()
                .incomplete,
            published.incomplete
        );
        let mut fresh = 0;
        let retried = interrupted
            .plan_positional_redefinitions_with_bases_and_budget(
                &bases,
                &incomplete,
                Some(&mut fresh),
            )
            .unwrap();
        assert_eq!(retried.targets, complete.targets);
        assert_eq!(retried.incomplete, complete.incomplete);
    }

    #[test]
    fn traversal_charges_edges_before_growing_pending_work_and_recovers() {
        let mut traversal = Reachability::new(4);
        let graph = HashMap::from([(0, vec![1, 2]), (1, vec![3]), (2, vec![3]), (3, vec![0])]);
        let mut work = crate::eval::MAX_STEPS - 2;
        assert!(
            traversal
                .reachable_budget(0, &graph, &mut Some(&mut work))
                .is_none()
        );
        assert!(work > crate::eval::MAX_STEPS);
        assert!(
            traversal.todo.is_empty(),
            "edge extension must follow its charge"
        );
        assert_eq!(
            traversal
                .reachable_budget(0, &graph, &mut Some(&mut 0))
                .unwrap()
                .len(),
            4
        );
    }

    #[test]
    fn supplied_static_bases_reproduce_the_legacy_positional_plan() {
        let mut model = crate::model::Model::new();
        model.add_source("positional.kerml", "function Base {in a; return b;} function Child specializes Base {in x; return y;} feature call=Child(1);");
        assert!(!model.has_errors());
        let mut r = super::super::ResolvedModel::build(&model);
        let (expected, _) = r.b.plan_positional_redefinitions();
        let (bases, incomplete) = r.b.positional_direct_bases();
        let retained = r.b.supported_implied.clone().unwrap();
        let actual =
            r.b.plan_positional_redefinitions_with_bases(&bases, &incomplete);
        assert_eq!(actual.targets, expected.targets);
        assert_eq!(actual.incomplete, expected.incomplete);
        assert!(std::sync::Arc::ptr_eq(
            &retained,
            r.b.supported_implied.as_ref().unwrap()
        ));
    }

    #[test]
    fn supplied_local_callee_bases_do_not_publish_candidate_positional_rows() {
        let mut model = crate::model::Model::new();
        model.add_source(
            "positional.kerml",
            "function F {in p; return result;} feature call=F(1);",
        );
        assert!(!model.has_errors());
        let mut r = super::super::ResolvedModel::build(&model);
        let function = r.resolve_qualified("F").unwrap().0;
        let parameter = r.resolve_qualified("F::p").unwrap().0;
        let invocation =
            r.b.elements
                .iter()
                .position(|e| e.ty == "InvocationExpression")
                .unwrap();
        let argument =
            r.b.owned_member_elems(invocation, true)
                .into_iter()
                .find(|&f| r.b.is_parameter(f) && !r.b.positional_is_result(f))
                .unwrap();
        r.b.ensure_positional_redefinitions();
        let published = r.b.positional_redefinitions.clone().unwrap();
        let (mut bases, incomplete) = r.b.positional_direct_bases();
        assert!(
            !bases
                .get(&invocation)
                .is_some_and(|v| v.contains(&function))
        );
        bases.entry(invocation).or_default().push(function);
        let candidate =
            r.b.plan_positional_redefinitions_with_bases(&bases, &incomplete);
        assert!(
            candidate
                .targets
                .get(&argument)
                .is_some_and(|v| v.contains(&parameter))
        );
        assert_eq!(
            r.b.positional_redefinitions.as_ref().unwrap().targets,
            published.targets
        );
        assert_eq!(
            r.b.positional_redefinitions.as_ref().unwrap().incomplete,
            published.incomplete
        );
    }

    #[test]
    fn wide_scratch_tables_do_not_follow_a_run_of_tiny_nodes() {
        let mut members: HashSet<_> = (0..4096).collect();
        let mut counts: HashMap<_, _> = (0..4096).map(|e| (e, 1)).collect();
        reset_scratch_set(&mut members);
        reset_scratch_map(&mut counts);
        assert!(members.is_empty() && counts.is_empty());
        for e in 0..1000 {
            members.insert(e);
            counts.insert(e, 1);
            reset_scratch_set(&mut members);
            reset_scratch_map(&mut counts);
            assert!(members.is_empty() && counts.is_empty());
            assert!(members.capacity() <= 128 && counts.capacity() <= 128);
        }
    }

    #[test]
    fn reusable_traversal_matches_transitive_closure_for_every_three_node_graph() {
        let mut traversal = Reachability::new(3);
        for bits in 0..512 {
            let mut graph = HashMap::new();
            let mut expected = [[false; 3]; 3];
            for (source, row) in expected.iter_mut().enumerate() {
                row[source] = true;
                for (target, reachable) in row.iter_mut().enumerate() {
                    if bits & (1 << (source * 3 + target)) != 0 {
                        graph.entry(source).or_insert_with(Vec::new).push(target);
                        *reachable = true;
                    }
                }
            }
            for intermediate in 0..3 {
                for source in 0..3 {
                    for target in 0..3 {
                        expected[source][target] |=
                            expected[source][intermediate] && expected[intermediate][target];
                    }
                }
            }
            for (source, expected) in expected.iter().enumerate() {
                let reached = traversal.reachable(source, &graph);
                assert_eq!(reached.len(), expected.iter().filter(|&&v| v).count());
                for (target, expected) in expected.iter().enumerate() {
                    assert_eq!(
                        reached.contains(&target),
                        *expected,
                        "graph {bits}, {source}->{target}"
                    );
                }
            }
        }
    }

    #[test]
    fn traversal_observes_graph_growth_and_generation_wrap() {
        let mut traversal = Reachability::new(4);
        let mut graph = HashMap::from([(0, vec![1, 2]), (1, vec![3]), (2, vec![3])]);
        assert_eq!(traversal.reachable(3, &graph), [3]);
        assert_eq!(traversal.reachable(0, &graph).len(), 4);
        graph.insert(3, vec![0]);
        assert_eq!(traversal.reachable(3, &graph).len(), 4);
        traversal.generation = usize::MAX;
        // Stale first-generation marks must not survive the wrap.
        traversal.marks.fill(1);
        graph.clear();
        assert_eq!(traversal.reachable(0, &graph), [0]);
        assert_eq!(traversal.reachable(3, &graph), [3]);
    }
}
