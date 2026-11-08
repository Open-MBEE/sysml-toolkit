//! Rule-required positional redefinitions, shared by inheritance and the
//! materialized relationship view. This table never changes compact storage.

use super::implied;
#[cfg(test)]
use super::membership_projection::{reset_scratch_map, reset_scratch_set};
use super::{
    Builder,
    membership_projection::{
        ExportedOver, Membership as PositionalMembership, MembershipFacts, Node, Reachability,
        Reduction, charge,
    },
};
use crate::flat::ListsByRow;
use crate::layered::{IdMap, IdSet};
use crate::metaclass::conforms;
use crate::metaclass::is_a;
use std::collections::HashMap;
use std::sync::Arc;

#[derive(Clone, Default)]
pub(super) struct PositionalRedefinitions {
    pub targets: IdMap<usize, Vec<usize>>,
    pub incomplete: IdSet<usize>,
}

/// A positional plan as a snapshot carries it: its maps as vectors sorted by
/// key, so that the same plan is written the same way every time.
#[derive(serde::Serialize, serde::Deserialize)]
pub(super) struct PositionalRedefinitionsWire {
    targets: crate::bulk::IndexLists,
    incomplete: crate::bulk::Ints,
}

impl PositionalRedefinitions {
    /// This plan as a snapshot carries it.
    pub(super) fn to_wire(&self) -> PositionalRedefinitionsWire {
        PositionalRedefinitionsWire {
            targets: implied::sorted_by_key(self.targets.iter().map(|(f, t)| (*f, t.clone())))
                .into(),
            incomplete: crate::bulk::Ints(implied::sorted(self.incomplete.iter().copied())),
        }
    }

    /// A plan read back from its wire form, over `rows` rows; `None` when
    /// the wire names a row there is not.
    pub(super) fn from_wire(wire: PositionalRedefinitionsWire, rows: usize) -> Option<Self> {
        let targets = wire.targets.into_lists()?;
        let incomplete = wire.incomplete.0;
        let in_range = |i: usize| i < rows;
        let fits = targets
            .iter()
            .all(|(f, ts)| in_range(*f) && ts.iter().all(|&t| in_range(t)))
            && incomplete.iter().all(|&f| in_range(f));
        fits.then(|| Self {
            targets: targets.into_iter().collect(),
            incomplete: incomplete.into_iter().collect(),
        })
    }
}

/// A budgeted planning attempt that ran out of budget: what it planned over
/// — the revisions of the element, specialization, resolved-target and
/// library-name rows, the library-name configuration and the implied plan
/// it started from — and the budget it had after the entry charge. Planning
/// is a function of those inputs, so an attempt over the same inputs with
/// no more budget fails the same way.
#[derive(Clone)]
pub(super) struct BudgetExhausted {
    rows: crate::layered::Revision,
    specs: crate::layered::Revision,
    resolved: crate::layered::Revision,
    names: crate::layered::Revision,
    library_configuration: bool,
    implied: Option<usize>,
    remaining: usize,
}

/// The identity of a published implied plan, as the memo of exhausted
/// attempts compares it: the same allocation is the same plan. An address
/// reused by a later plan stands for an equally warm one, so a refusal on
/// it is still right.
fn implied_identity(plan: &Arc<implied::SupportedImpliedSpecializations>) -> usize {
    Arc::as_ptr(plan) as usize
}

/// What a planning attempt leaves behind for the next one even when it
/// runs out of budget: the implied plan, the decision whether the library's
/// plans are extended, the identity index and the structural certificate.
/// An attempt that advanced any of these is not remembered as exhausted,
/// because a repeat starts further along. Presence suffices for the index
/// and the certificate: one that went stale was dropped with a revision
/// change the memo keys on anyway.
#[derive(PartialEq, Eq)]
struct PlanningProgress {
    implied: Option<usize>,
    library_plans_decided: bool,
    id_index: bool,
    stored_structure: bool,
}

/// The direct bases a positional planning reads, by type: a table of them, or
/// a build's own over its prepared library's ([`OverLibrary`]).
pub(super) trait DirectBases {
    fn get(&self, e: &usize) -> Option<&[usize]>;
}
impl DirectBases for IdMap<usize, Vec<usize>> {
    fn get(&self, e: &usize) -> Option<&[usize]> {
        HashMap::get(self, e).map(Vec::as_slice)
    }
}
impl DirectBases for ListsByRow<usize> {
    fn get(&self, e: &usize) -> Option<&[usize]> {
        ListsByRow::get(self, *e)
    }
}
impl DirectBases for crate::layered::LayeredMap<usize, Vec<usize>> {
    fn get(&self, e: &usize) -> Option<&[usize]> {
        crate::layered::LayeredMap::get(self, e).map(Vec::as_slice)
    }
}
/// A build's own types' direct bases over its library's: the two tables name
/// disjoint types.
pub(super) struct OverLibrary<'a> {
    pub own: &'a IdMap<usize, Vec<usize>>,
    pub library: &'a ListsByRow<usize>,
}
impl DirectBases for OverLibrary<'_> {
    fn get(&self, e: &usize) -> Option<&[usize]> {
        self.own
            .get(e)
            .map(Vec::as_slice)
            .or_else(|| self.library.get(*e))
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
    ids: Option<IdSet<uuid::Uuid>>,
    owned: IdMap<usize, (Vec<usize>, Option<Vec<PositionalMembership>>)>,
    unresolved: IdMap<usize, bool>,
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
#[derive(Clone, serde::Serialize, serde::Deserialize)]
pub(super) struct Roles {
    ends: Vec<usize>,
    results: Vec<usize>,
    parameters: Vec<usize>,
}

/// A type's roles, borrowed from a table.
#[derive(Clone, Copy)]
pub(super) struct RolesRef<'a> {
    pub(super) ends: &'a [usize],
    pub(super) results: &'a [usize],
    pub(super) parameters: &'a [usize],
}
impl Roles {
    fn as_ref(&self) -> RolesRef<'_> {
        RolesRef {
            ends: &self.ends,
            results: &self.results,
            parameters: &self.parameters,
        }
    }
}

/// What a planning derived for every type it completed — its effective
/// features, their roles, its exported memberships — and the redefinitions
/// it read and added, as the planning makes them. A prepared library's
/// planning keeps these by row ([`PlannedLibraryTypes`]), and a build on
/// the library plans only its own types over them
/// (see [`Builder::plan_positional_on_library`]).
#[derive(Clone, Default)]
pub(super) struct PlannedTypes {
    effective: IdMap<usize, Vec<usize>>,
    roles: IdMap<usize, Roles>,
    exported: IdMap<usize, Vec<PositionalMembership>>,
    redefinitions: IdMap<usize, Vec<usize>>,
}

/// What a prepared library's planning derived, laid out by row (see
/// [`PlannedTypes`]): read back from a snapshot in one pass per table,
/// with no table to hash, and read by index. The roles are three lists by
/// row, present together.
#[derive(Clone, Default)]
pub(super) struct PlannedLibraryTypes {
    pub(super) effective: ListsByRow<usize>,
    ends: ListsByRow<usize>,
    results: ListsByRow<usize>,
    parameters: ListsByRow<usize>,
    pub(super) exported: ListsByRow<PositionalMembership>,
    pub(super) redefinitions: ListsByRow<usize>,
}

impl PlannedLibraryTypes {
    /// The roles of type `e`, when the planning completed it.
    pub(super) fn roles(&self, e: usize) -> Option<RolesRef<'_>> {
        Some(RolesRef {
            ends: self.ends.get(e)?,
            results: self.results.get(e)?,
            parameters: self.parameters.get(e)?,
        })
    }

    /// What `planned` derived, laid out over `rows` rows.
    pub(super) fn from_planned(rows: usize, planned: &PlannedTypes) -> Self {
        let roles = |pick: fn(&Roles) -> &Vec<usize>| {
            let lists: IdMap<usize, Vec<usize>> = planned
                .roles
                .iter()
                .map(|(e, roles)| (*e, pick(roles).clone()))
                .collect();
            ListsByRow::from_map(rows, &lists)
        };
        Self {
            effective: ListsByRow::from_map(rows, &planned.effective),
            ends: roles(|roles| &roles.ends),
            results: roles(|roles| &roles.results),
            parameters: roles(|roles| &roles.parameters),
            exported: ListsByRow::from_map(rows, &planned.exported),
            redefinitions: ListsByRow::from_map(rows, &planned.redefinitions),
        }
        .sharing_ranks()
    }

    /// This planning with its tables sharing their row ranks where they
    /// have lists on the same rows: the planning keeps every table for the
    /// types it completed, so the ranks are one vector for all of them.
    fn sharing_ranks(mut self) -> Self {
        self.ends.share_ranks_with(&self.effective);
        self.results.share_ranks_with(&self.effective);
        self.parameters.share_ranks_with(&self.effective);
        self.exported.share_ranks_with(&self.effective);
        self.redefinitions.share_ranks_with(&self.effective);
        self
    }

    /// What this planning derived, as a snapshot carries it.
    pub(super) fn to_wire(&self) -> PlannedTypesWire {
        PlannedTypesWire {
            effective: (&self.effective).into(),
            roles: RoleLists::from_rows(&self.ends, &self.results, &self.parameters),
            exported: MembershipLists::from_rows(&self.exported),
            redefinitions: (&self.redefinitions).into(),
        }
    }

    /// A planning read back from its wire form, over `rows` rows; `None`
    /// when the wire names a row there is not.
    pub(super) fn from_wire(wire: PlannedTypesWire, rows: usize) -> Option<Self> {
        let effective = wire.effective.into_rows(rows)?;
        let redefinitions = wire.redefinitions.into_rows(rows)?;
        if !effective
            .values()
            .iter()
            .chain(redefinitions.values())
            .all(|&f| f < rows)
        {
            return None;
        }
        let (ends, results, parameters) = wire.roles.into_rows(rows)?;
        let exported = wire.exported.into_rows(rows)?;
        Some(
            Self {
                effective,
                ends,
                results,
                parameters,
                exported,
                redefinitions,
            }
            .sharing_ranks(),
        )
    }

    /// Whether the planning kept what it derived for type `e`.
    #[cfg(test)]
    pub(super) fn has(&self, e: usize) -> bool {
        self.effective.contains(e) && self.roles(e).is_some() && self.exported.contains(e)
    }

    /// The types the planning kept effective features for, in order.
    #[cfg(test)]
    pub(super) fn types(&self) -> Vec<usize> {
        self.effective.iter().map(|(e, _)| e).collect()
    }
}

#[cfg(test)]
impl PlannedLibraryTypes {
    /// Drop this planning a table at a time, naming each to `note` once it
    /// is gone, for the tests that measure what each holds.
    pub(super) fn drop_members(self, note: &mut dyn FnMut(&str)) {
        let Self {
            effective,
            ends,
            results,
            parameters,
            exported,
            redefinitions,
        } = self;
        fn shape<T>(name: &str, lists: &ListsByRow<T>) {
            println!(
                "  {name}: {} rows, {} with a list, {} values",
                lists.rows(),
                lists.iter().count(),
                lists.values().len()
            );
        }
        shape("effective", &effective);
        shape("ends", &ends);
        shape("results", &results);
        shape("parameters", &parameters);
        shape("exported", &exported);
        shape("redefinitions", &redefinitions);
        drop(effective);
        note("effective");
        drop(ends);
        note("ends");
        drop(results);
        note("results");
        drop(parameters);
        note("parameters");
        drop(exported);
        note("exported");
        drop(redefinitions);
        note("redefinitions");
    }
}

/// What a planning derived, as a snapshot carries it: the maps as vectors
/// sorted by key, so that the same planning is written the same way every
/// time.
#[derive(serde::Serialize, serde::Deserialize)]
pub(super) struct PlannedTypesWire {
    effective: crate::bulk::IndexLists,
    roles: RoleLists,
    exported: MembershipLists,
    redefinitions: crate::bulk::IndexLists,
}

/// The roles of each planned type as columns: the types, then each role's
/// list lengths and values.
#[derive(serde::Serialize, serde::Deserialize)]
struct RoleLists {
    types: crate::bulk::Ints,
    ends: crate::bulk::IndexLists,
    results: crate::bulk::IndexLists,
    parameters: crate::bulk::IndexLists,
}
#[cfg(test)]
impl From<Vec<(usize, Roles)>> for RoleLists {
    fn from(roles: Vec<(usize, Roles)>) -> Self {
        Self {
            types: crate::bulk::Ints(roles.iter().map(|r| r.0).collect()),
            ends: roles
                .iter()
                .map(|(e, r)| (*e, r.ends.clone()))
                .collect::<Vec<_>>()
                .into(),
            results: roles
                .iter()
                .map(|(e, r)| (*e, r.results.clone()))
                .collect::<Vec<_>>()
                .into(),
            parameters: roles
                .into_iter()
                .map(|(e, r)| (e, r.parameters))
                .collect::<Vec<_>>()
                .into(),
        }
    }
}
impl RoleLists {
    /// The roles back as three lists by row over `rows` rows; `None` when
    /// the columns disagree on their types or name a row there is not.
    fn into_rows(
        self,
        rows: usize,
    ) -> Option<(ListsByRow<usize>, ListsByRow<usize>, ListsByRow<usize>)> {
        let types = self.types.0.as_slice();
        if self.ends.keys() != types
            || self.results.keys() != types
            || self.parameters.keys() != types
        {
            return None;
        }
        let ends = self.ends.into_rows(rows)?;
        let results = self.results.into_rows(rows)?;
        let parameters = self.parameters.into_rows(rows)?;
        let fits = ends
            .values()
            .iter()
            .chain(results.values())
            .chain(parameters.values())
            .all(|&f| f < rows);
        fits.then_some((ends, results, parameters))
    }

    /// The roles laid out by row as columns: the three tables are present
    /// on the same types.
    fn from_rows(
        ends: &ListsByRow<usize>,
        results: &ListsByRow<usize>,
        parameters: &ListsByRow<usize>,
    ) -> Self {
        Self {
            types: crate::bulk::Ints(ends.iter().map(|(t, _)| t).collect()),
            ends: ends.into(),
            results: results.into(),
            parameters: parameters.into(),
        }
    }

    /// The roles back; `None` when the columns disagree on their types.
    #[cfg(test)]
    fn into_lists(self) -> Option<Vec<(usize, Roles)>> {
        let ends = self.ends.into_lists()?;
        let results = self.results.into_lists()?;
        let parameters = self.parameters.into_lists()?;
        let n = self.types.0.len();
        if ends.len() != n || results.len() != n || parameters.len() != n {
            return None;
        }
        let agree = self
            .types
            .0
            .iter()
            .zip(&ends)
            .zip(&results)
            .zip(&parameters)
            .all(|(((t, e), r), p)| *t == e.0 && *t == r.0 && *t == p.0);
        if !agree {
            return None;
        }
        Some(
            ends.into_iter()
                .zip(results)
                .zip(parameters)
                .map(|(((e, ends), (_, results)), (_, parameters))| {
                    (
                        e,
                        Roles {
                            ends,
                            results,
                            parameters,
                        },
                    )
                })
                .collect(),
        )
    }
}

/// The exported memberships of each planned type as columns.
#[derive(serde::Serialize, serde::Deserialize)]
struct MembershipLists {
    types: crate::bulk::Ints,
    lengths: crate::bulk::Ints,
    relationships: crate::bulk::Ints,
    members: crate::bulk::Ints,
}
#[cfg(test)]
impl From<Vec<(usize, Vec<PositionalMembership>)>> for MembershipLists {
    fn from(lists: Vec<(usize, Vec<PositionalMembership>)>) -> Self {
        Self {
            types: crate::bulk::Ints(lists.iter().map(|l| l.0).collect()),
            lengths: crate::bulk::Ints(lists.iter().map(|l| l.1.len()).collect()),
            relationships: crate::bulk::Ints(
                lists
                    .iter()
                    .flat_map(|l| l.1.iter().map(|m| m.relationship))
                    .collect(),
            ),
            members: crate::bulk::Ints(
                lists
                    .into_iter()
                    .flat_map(|l| l.1.into_iter().map(|m| m.member))
                    .collect(),
            ),
        }
    }
}
impl MembershipLists {
    /// The memberships back as lists by row over `rows` rows; `None` when
    /// the columns do not cover each other or name a row there is not.
    fn into_rows(self, rows: usize) -> Option<ListsByRow<PositionalMembership>> {
        if self.relationships.0.len() != self.members.0.len() {
            return None;
        }
        let values: Vec<PositionalMembership> = self
            .relationships
            .0
            .into_iter()
            .zip(self.members.0)
            .map(|(relationship, member)| PositionalMembership {
                relationship,
                member,
            })
            .collect();
        let lists = ListsByRow::from_sorted(rows, &self.types.0, &self.lengths.0, values)?;
        lists
            .values()
            .iter()
            .all(|m| m.relationship < rows && m.member < rows)
            .then_some(lists)
    }

    /// The memberships laid out by row as columns.
    fn from_rows(lists: &ListsByRow<PositionalMembership>) -> Self {
        Self {
            types: crate::bulk::Ints(lists.iter().map(|(t, _)| t).collect()),
            lengths: crate::bulk::Ints(lists.iter().map(|(_, l)| l.len()).collect()),
            relationships: crate::bulk::Ints(
                lists.values().iter().map(|m| m.relationship).collect(),
            ),
            members: crate::bulk::Ints(lists.values().iter().map(|m| m.member).collect()),
        }
    }

    /// The memberships back; `None` when the columns do not cover each other.
    #[cfg(test)]
    fn into_lists(self) -> Option<Vec<(usize, Vec<PositionalMembership>)>> {
        if self.relationships.0.len() != self.members.0.len()
            || self.types.0.len() != self.lengths.0.len()
            || self
                .lengths
                .0
                .iter()
                .try_fold(0usize, |n, &l| n.checked_add(l))
                != Some(self.members.0.len())
        {
            return None;
        }
        let mut memberships =
            self.relationships
                .0
                .into_iter()
                .zip(self.members.0)
                .map(|(relationship, member)| PositionalMembership {
                    relationship,
                    member,
                });
        Some(
            self.types
                .0
                .into_iter()
                .zip(self.lengths.0)
                .map(|(t, len)| (t, memberships.by_ref().take(len).collect()))
                .collect(),
        )
    }
}

#[cfg(test)]
impl PlannedTypes {
    /// What this planning derived, as a snapshot carries it.
    pub(super) fn to_wire(&self) -> PlannedTypesWire {
        PlannedTypesWire {
            effective: implied::sorted_by_key(self.effective.iter().map(|(e, f)| (*e, f.clone())))
                .into(),
            roles: implied::sorted_by_key(self.roles.iter().map(|(e, r)| (*e, r.clone()))).into(),
            exported: implied::sorted_by_key(self.exported.iter().map(|(e, m)| (*e, m.clone())))
                .into(),
            redefinitions: implied::sorted_by_key(
                self.redefinitions.iter().map(|(e, r)| (*e, r.clone())),
            )
            .into(),
        }
    }

    /// A planning read back from its wire form, over `rows` rows; `None`
    /// when the wire names a row there is not.
    pub(super) fn from_wire(wire: PlannedTypesWire, rows: usize) -> Option<Self> {
        let wire = PlannedTypesLists {
            effective: wire.effective.into_lists()?,
            roles: wire.roles.into_lists()?,
            exported: wire.exported.into_lists()?,
            redefinitions: wire.redefinitions.into_lists()?,
        };
        let in_range = |i: usize| i < rows;
        let all_in_range = |entries: &[(usize, Vec<usize>)]| {
            entries
                .iter()
                .all(|(e, rows)| in_range(*e) && rows.iter().all(|&r| in_range(r)))
        };
        let fits = all_in_range(&wire.effective)
            && all_in_range(&wire.redefinitions)
            && wire.roles.iter().all(|(e, roles)| {
                in_range(*e)
                    && roles
                        .ends
                        .iter()
                        .chain(&roles.results)
                        .chain(&roles.parameters)
                        .all(|&f| in_range(f))
            })
            && wire.exported.iter().all(|(e, memberships)| {
                in_range(*e)
                    && memberships
                        .iter()
                        .all(|m| in_range(m.relationship) && in_range(m.member))
            });
        fits.then(|| Self {
            effective: wire.effective.into_iter().collect(),
            roles: wire.roles.into_iter().collect(),
            exported: wire.exported.into_iter().collect(),
            redefinitions: wire.redefinitions.into_iter().collect(),
        })
    }
}
/// A planning's wire with its columns split back into lists.
#[cfg(test)]
struct PlannedTypesLists {
    effective: Vec<(usize, Vec<usize>)>,
    roles: Vec<(usize, Roles)>,
    exported: Vec<(usize, Vec<PositionalMembership>)>,
    redefinitions: Vec<(usize, Vec<usize>)>,
}

#[cfg(test)]
impl PlannedTypes {
    /// Keep no effective features for type `e`, for the tests of what a
    /// read-back refuses.
    pub(super) fn keep_nothing_for(&mut self, e: usize) {
        self.effective.insert(e, Vec::new());
    }
}
/// Recorded bootstrap edges indexed only for one planner invocation. These
/// vectors can change without a stored-row revision, so this proof input must
/// never be cached on Builder, StoredStructure, or the cross-pass workspace.
#[derive(Default)]
struct RecordedRedefinitions {
    targets: IdMap<usize, IdSet<usize>>,
    incomplete: IdSet<usize>,
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

    fn sources_match(&self, actual: &IdMap<usize, Vec<usize>>, steps: &mut usize) -> Option<bool> {
        for (source, targets) in actual {
            charge(
                &mut Some(&mut *steps),
                targets.len().saturating_mul(2).saturating_add(1),
            )?;
            if self.incomplete.contains(source) {
                return Some(false);
            }
            let current: IdSet<_> = targets.iter().copied().collect();
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
    role_domains: IdSet<usize>,
}
struct ImportSourceContext<'a> {
    owner: usize,
    bases: &'a dyn DirectBases,
    incomplete: &'a IdSet<usize>,
    ordinary_only: bool,
    allow_prerequisites: bool,
}

struct CompleteReduction {
    order: Vec<usize>,
    nodes: IdMap<usize, Node>,
    prerequisites: IdMap<usize, Vec<usize>>,
    incomplete: IdSet<usize>,
    redefinitions: IdMap<usize, Vec<usize>>,
    result: PositionalRedefinitions,
}
fn charge_map_vectors(
    map: &IdMap<usize, Vec<usize>>,
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
        is_a!(self.0.elements[member], "Feature")
    }
    fn is_feature_membership(&self, relationship: usize) -> bool {
        is_a!(self.0.elements[relationship], "FeatureMembership")
    }
    fn is_protected(&self, relationship: usize) -> bool {
        self.0.elements[relationship]
            .props
            .get("visibility")
            .and_then(|value| value.as_str())
            == Some("protected")
    }
}

#[cfg(test)]
thread_local! {
    static BUDGETED_ATTEMPTS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

impl Builder {
    /// Plan the positional redefinitions now, without a budget, when the
    /// model is semantically ready and no plan is published yet: what the
    /// first enumeration of inherited members with implied heritage does.
    pub(crate) fn ensure_positional_redefinitions(&mut self) {
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
        self.drop_inherited_memos();
        self.positional_redefinitions = Some(plan);
        self.positional_from_library = from_library;
        self.positional_budget_exhausted = None;
    }

    /// Whether a positional plan is published.
    #[cfg(test)]
    pub(crate) fn has_positional_plan(&self) -> bool {
        self.positional_redefinitions.is_some()
    }

    /// How many budgeted planning attempts this thread has made: entries
    /// that found no plan published and went on to plan (or to be refused).
    #[cfg(test)]
    pub(crate) fn budgeted_planning_attempts() -> usize {
        BUDGETED_ATTEMPTS.with(|count| count.get())
    }

    fn planning_progress(&self) -> PlanningProgress {
        PlanningProgress {
            implied: self.supported_implied.as_ref().map(implied_identity),
            library_plans_decided: self.library_plans_decided.is_some(),
            id_index: self.id_index.is_some(),
            stored_structure: self.stored_structure.is_some(),
        }
    }

    /// Whether a budgeted attempt with `remaining` steps after its entry
    /// charge would repeat a remembered exhausted one over the same inputs.
    fn refused_as_exhausted(&self, remaining: usize) -> bool {
        let Some(exhausted) = &self.positional_budget_exhausted else {
            return false;
        };
        let same = |revision: Option<&crate::layered::Revision>, at: &crate::layered::Revision| {
            revision.is_some_and(|revision| revision.same_as(at))
        };
        remaining <= exhausted.remaining
            && same(self.elements.revision(), &exhausted.rows)
            && same(self.spec_targets.revision(), &exhausted.specs)
            && same(self.spec_resolved.revision(), &exhausted.resolved)
            && same(self.lib_qnames.revision(), &exhausted.names)
            && self.external_implied_names.is_empty() == exhausted.library_configuration
            && self.supported_implied.as_ref().map(implied_identity) == exhausted.implied
    }

    /// Prepare a complete positional table within the caller's allowance.
    /// In-progress work is private: refusal never publishes an empty sentinel.
    ///
    /// An attempt that runs out of budget without leaving any progress
    /// behind is remembered with its inputs and the budget it had; while
    /// the inputs are the same, a repeat with no more budget is refused
    /// right after the entry charge instead of planning again to the same
    /// end. A repeat with more budget, over changed inputs, or after an
    /// attempt that did make progress plans again.
    pub(crate) fn ensure_positional_redefinitions_with_budget(
        &mut self,
        steps: &mut usize,
    ) -> bool {
        if charge(&mut Some(&mut *steps), 1).is_none() {
            return false;
        }
        if self.positional_planning {
            return false;
        }
        let remaining = crate::eval::MAX_STEPS.saturating_sub(*steps);
        let unplanned = self.semantic_ready && self.positional_redefinitions.is_none();
        if unplanned && self.refused_as_exhausted(remaining) {
            return false;
        }
        #[cfg(test)]
        if unplanned {
            BUDGETED_ATTEMPTS.with(|count| count.set(count.get() + 1));
        }
        let before = self.planning_progress();
        let planned = self.ensure_positional_redefinitions_within(steps);
        if planned || !unplanned || self.positional_redefinitions.is_some() {
            self.positional_budget_exhausted = None;
        } else if self.planning_progress() == before {
            self.positional_budget_exhausted = Some(BudgetExhausted {
                rows: self.elements.observe_revision(),
                specs: self.spec_targets.observe_revision(),
                resolved: self.spec_resolved.observe_revision(),
                names: self.lib_qnames.observe_revision(),
                library_configuration: self.external_implied_names.is_empty(),
                implied: before.implied,
                remaining,
            });
        } else {
            self.positional_budget_exhausted = None;
        }
        planned
    }

    /// [`Self::ensure_positional_redefinitions_with_budget`] without the
    /// memory of exhausted attempts: the planning itself.
    fn ensure_positional_redefinitions_within(&mut self, steps: &mut usize) -> bool {
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
        self.drop_inherited_memos();
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
        incomplete: &IdSet<usize>,
    ) -> (PositionalRedefinitions, IdSet<usize>, PlannedTypes) {
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
    /// The positional roots a row contributes: a type that owns an end, a
    /// parameter or a case objective through a feature membership, and each
    /// objective it owns. An objective redefines the objective of each case
    /// its owner specializes, and a specializing objective pairs its own
    /// subject and parameters against it, planned or seeded, so both are
    /// roots. Root discovery needs existence, not an ordered collection.
    fn positional_roots_of(&self, e: usize, steps: &mut Option<&mut usize>) -> Option<Vec<usize>> {
        let mut roots = Vec::new();
        if !is_a!(self.elements[e], "Type") {
            return Some(roots);
        }
        let mut found = false;
        for &rel in &self.elements[e].owned_relationships {
            charge(steps, 1)?;
            if !is_a!(self.elements[rel], "FeatureMembership") {
                continue;
            }
            if is_a!(self.elements[rel], "ObjectiveMembership") {
                found = true;
                roots.extend(
                    self.elements[rel]
                        .children
                        .iter()
                        .copied()
                        .filter(|&f| is_a!(self.elements[f], "Type")),
                );
                continue;
            }
            if found {
                continue;
            }
            for &f in &self.elements[rel].children {
                charge(steps, 1)?;
                if self.positional_is_end(f) || self.is_parameter(f) {
                    found = true;
                    break;
                }
            }
        }
        if found {
            roots.insert(0, e);
        }
        Some(roots)
    }

    pub(super) fn plan_positional_on_library(
        &mut self,
        library: &std::sync::Arc<super::LibraryPlans>,
        direct_bases: &dyn DirectBases,
        incomplete: &IdSet<usize>,
        mut steps: Option<&mut usize>,
    ) -> Option<Option<PositionalRedefinitions>> {
        let floor = library.rows;
        let end = self.explicit_len();
        charge(&mut steps, end - floor)?;
        let mut roots = Vec::new();
        for e in floor..end {
            roots.extend(self.positional_roots_of(e, &mut steps)?);
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
        incomplete: &IdSet<usize>,
    ) -> PositionalRedefinitions {
        self.plan_positional_redefinitions_with_bases_and_budget(direct_bases, incomplete, None)
            .expect("unbounded positional construction cannot exhaust its budget")
    }

    /// Budgeted counterpart used before accepting mutable semantic candidates.
    /// None discards the whole local plan; no partial targets/cache is published.
    pub(super) fn plan_positional_redefinitions_with_bases_and_budget(
        &mut self,
        direct_bases: &dyn DirectBases,
        incomplete: &IdSet<usize>,
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
        incomplete: &IdSet<usize>,
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
        nodes: &IdMap<usize, Node>,
        bases: &dyn DirectBases,
        import_owners: &IdSet<usize>,
        steps: &mut usize,
    ) -> Option<PositionalRedefinitions> {
        let mut budget = Some(steps);
        charge(&mut budget, nodes.len())?;
        let roots: Vec<_> = nodes.keys().copied().collect();
        for (&owner, node) in nodes {
            self.positional_charge_members(owner, &mut budget)?;
            charge(&mut budget, node.owned.len() + node.owned_memberships.len())?;
            // The checked node lists the generated result feature of an
            // expression too; the positional planner reads the authored
            // rows, and the result's own redefinitions are the result
            // family's.
            let authored_owned: Vec<usize> = node
                .owned
                .iter()
                .copied()
                .filter(|&f| self.is_authored(f))
                .collect();
            if self.owned_member_elems(owner, true) != authored_owned {
                return None;
            }
            let memberships = self.positional_owned_memberships(owner, &mut budget)?;
            // The checked node lists the materialized implied memberships
            // too (a target transition's source); the positional planner
            // reads the authored rows, so the two agree on those.
            let authored: Vec<&PositionalMembership> = node
                .owned_memberships
                .iter()
                .filter(|m| self.is_authored(m.relationship))
                .collect();
            if memberships.len() != authored.len()
                || memberships
                    .iter()
                    .zip(&authored)
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
            let mut prerequisites = IdMap::default();
            charge(&mut budget, import_owners.len())?;
            for &owner in import_owners {
                let (mut public, mut protected) = self.positional_imports(
                    owner,
                    bases,
                    &IdSet::default(),
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
                    let mut seen = IdSet::default();
                    actual.retain(|m| seen.insert(m.relationship));
                    if actual != expected {
                        return None;
                    }
                }
            }
        }
        self.plan_positional_with_result_query(
            bases,
            &IdSet::default(),
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
        actual: &IdMap<usize, Vec<usize>>,
        steps: &mut usize,
    ) -> Option<bool> {
        let mut budget = Some(steps);
        charge(&mut budget, self.spec_targets.len())?;
        let mut indexed: IdMap<usize, IdSet<usize>> = IdMap::default();
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
            let current: IdSet<_> = targets.iter().copied().collect();
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
        incomplete: &IdSet<usize>,
        roots: &[usize],
        steps: &mut usize,
    ) -> Option<IdMap<usize, usize>> {
        let mut candidates = IdMap::default();
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
        incomplete: &IdSet<usize>,
        mut steps: Option<&mut usize>,
        selected_roots: Option<&[usize]>,
        mut result_candidates: Option<&mut IdMap<usize, usize>>,
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
            for e in self.authored_rows() {
                charge(&mut steps, 1)?;
                roots.extend(self.positional_roots_of(e, &mut steps)?);
            }
        }
        if !workspace.one_shot && selected_roots.is_none() && workspace.roots.is_none() {
            charge(&mut steps, roots.len())?;
            workspace.roots = Some(roots.clone());
        }

        let mut nodes = IdMap::default();
        let mut import_proof = ImportProof::default();
        let mut prerequisites = IdMap::default();
        charge(&mut steps, roots.len())?;
        let mut todo = roots.clone();
        // A planning extending its prepared library's reads what the
        // library's planning derived for every type that planning reached.
        let library = workspace.library.clone();
        let seeded = |e: &usize| library.as_ref().is_some_and(|l| l.reached.contains(e));
        let empty = PlannedLibraryTypes::default();
        let planned = library.as_ref().map_or(&empty, |l| &l.planned);
        while let Some(e) = todo.pop() {
            charge(&mut steps, 1)?;
            if nodes.contains_key(&e) || seeded(&e) {
                continue;
            }
            charge(
                &mut steps,
                direct_bases
                    .get(&e)
                    .map_or(0, <[usize]>::len)
                    .saturating_mul(2),
            )?;
            let bases = direct_bases
                .get(&e)
                .map(<[usize]>::to_vec)
                .unwrap_or_default();
            todo.extend(bases.iter().copied());
            let imports = self.positional_imports(
                e,
                direct_bases,
                incomplete,
                &mut steps,
                &mut import_proof,
                &mut prerequisites,
            );
            // A case's objective is planned after its owner, which pairs it
            // with the objectives of the owner's generals, and after those
            // objectives, so that its own subject and parameters pair
            // against them as against its bases.
            if owned_as_objective(self, e) {
                if let Some(owner) = self.owner_elem(e) {
                    let mut required = vec![owner];
                    let mut seen = IdSet::default();
                    let mut stack: Vec<usize> = direct_bases
                        .get(&owner)
                        .map(<[usize]>::to_vec)
                        .unwrap_or_default();
                    while let Some(ancestor) = stack.pop() {
                        charge(&mut steps, 1)?;
                        if required.len() > 256 || !seen.insert(ancestor) {
                            continue;
                        }
                        let members = self.owned_member_elems(ancestor, true);
                        charge(&mut steps, members.len())?;
                        required.extend(
                            members
                                .into_iter()
                                .filter(|&m| m != e && owned_as_objective(self, m)),
                        );
                        stack.extend(
                            direct_bases
                                .get(&ancestor)
                                .map(<[usize]>::to_vec)
                                .unwrap_or_default(),
                        );
                    }
                    prerequisites.entry(e).or_default().extend(required);
                }
            }
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
        let mut state = IdMap::default();
        let mut order = Vec::new();
        charge(&mut steps, incomplete.len())?;
        let mut plan = PositionalRedefinitions {
            targets: IdMap::default(),
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
            workspace.ids = Some(self.authored_rows().map(|i| self.elements[i].id).collect());
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
                    is_a!(rel, "Specialization")
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
                                        .is_some_and(|target| self.is_authored(target))
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
        let mut redefinitions = IdMap::default();
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
        let mut effective: IdMap<usize, Vec<usize>> = IdMap::default();
        let mut roles: IdMap<usize, Roles> = IdMap::default();
        let mut exported: IdMap<usize, Vec<PositionalMembership>> = IdMap::default();
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
                    || !(effective.contains_key(b) || planned.effective.contains(*b))
            }) {
                plan.incomplete.insert(e);
            }
            if let Some(required) = prerequisites.get(&e) {
                charge(&mut steps, required.len())?;
                if required.iter().any(|dependency| {
                    plan.incomplete.contains(dependency)
                        || !(effective.contains_key(dependency)
                            || planned.effective.contains(*dependency))
                }) {
                    plan.incomplete.insert(e);
                }
            }
            // The objectives of its owner's generals an objective was paired
            // with when the owner was planned (SysML
            // `checkRequirementUsageObjectiveRedefinition`): bases for its own
            // subject and parameters.
            let objective_bases: Vec<usize> = plan
                .targets
                .get(&e)
                .map(|targets| {
                    targets
                        .iter()
                        .copied()
                        .filter(|&t| owned_as_objective(self, t))
                        .collect()
                })
                .unwrap_or_default();
            charge(&mut steps, objective_bases.len())?;
            if objective_bases.iter().any(|b| {
                plan.incomplete.contains(b)
                    || !(effective.contains_key(b) || planned.effective.contains(*b))
            }) {
                plan.incomplete.insert(e);
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
            let behavior = is_a!(self.elements[e], "Behavior") || is_a!(self.elements[e], "Step");
            let function =
                is_a!(self.elements[e], "Function") || is_a!(self.elements[e], "Expression");
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
                    .is_some_and(|r| is_a!(self.elements[r], "SubjectMembership"))
            };
            let is_objective = |feature: usize| owned_as_objective(self, feature);
            let case_kind =
                |kind: &str| conforms(kind, "CaseDefinition") || conforms(kind, "CaseUsage");
            let subjects: Vec<_> = parameters
                .iter()
                .copied()
                .filter(|&f| is_subject(f))
                .collect();
            if subject_family(self.elements[e].ty).is_some() {
                for base in node.bases.iter().chain(objective_bases.iter()) {
                    charge(&mut steps, 1)?;
                    charge_sort(&mut steps, effective_of(&effective, planned, base).len())?;
                }
            }
            let subject_bases: Vec<_> = if let Some(family) = subject_family(self.elements[e].ty) {
                node.bases
                    .iter()
                    .chain(objective_bases.iter())
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
            // A case's objective redefines the specialized case's objective,
            // inherited or not (SysML
            // `checkRequirementUsageObjectiveRedefinition`), as its subject
            // does; an ambiguous objective view is left unplanned.
            if case_kind(self.elements[e].ty) {
                charge(&mut steps, node.owned.len())?;
                let objectives: Vec<_> = node
                    .owned
                    .iter()
                    .copied()
                    .filter(|&f| is_objective(f))
                    .collect();
                if objectives.len() > 1 {
                    plan.incomplete.insert(e);
                    continue;
                }
                let mut ambiguous = false;
                let mut objective_targets = Vec::new();
                for &base in &node.bases {
                    if !case_kind(self.elements[base].ty) {
                        continue;
                    }
                    charge(&mut steps, 1)?;
                    let view = effective_of(&effective, planned, &base);
                    charge_sort(&mut steps, view.len())?;
                    let mut found: Vec<_> =
                        view.iter().copied().filter(|&f| is_objective(f)).collect();
                    found.sort_unstable();
                    found.dedup();
                    match found[..] {
                        [] => {}
                        [target] => objective_targets.push(target),
                        _ => ambiguous = true,
                    }
                }
                if ambiguous {
                    plan.incomplete.insert(e);
                    continue;
                }
                if let Some(&source) = objectives.first() {
                    for target in objective_targets {
                        charge(&mut steps, 1)?;
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
            for &base in node.bases.iter().chain(objective_bases.iter()) {
                charge(&mut steps, 1)?;
                let base_roles = roles
                    .get(&base)
                    .map(Roles::as_ref)
                    .or_else(|| planned.roles(base))
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
                    // An invocation's parameters are its arguments, and each
                    // redefines an input parameter of the callee (KerML
                    // `validateInvocationExpressionParameterRedefinition`):
                    // they pair with the base's inputs in order, an output
                    // among the base's parameters taking no position.
                    let invocation = self.elements[e].conforms("InvocationExpression");
                    if invocation {
                        charge(&mut steps, base_roles.parameters.len())?;
                    }
                    let base_parameters = base_roles
                        .parameters
                        .iter()
                        .copied()
                        .filter(|&f| !invocation || self.positional_is_input(f));
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
                        let explicit_invocation_argument = self.elements[e]
                            .conforms("InvocationExpression")
                            && self.elements[source].owned_relationships.iter().any(|&r| {
                                is_a!(self.elements[r], "Redefinition")
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
        incomplete: &IdSet<usize>,
        steps: &mut Option<&mut usize>,
        proof: &mut ImportProof,
        prerequisites: &mut IdMap<usize, Vec<usize>>,
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
                .any(|m| is_a!(self.elements[m.member], "Feature"))
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
        // Semantic metadata adds a base the planner does not write (KerML
        // 9.2); plain metadata adds none.
        let semantic = self.semantically_annotated();
        // The checked Type caller establishes these domains before asking for
        // selectors; the publication planner must establish them independently.
        if !raw.import_domains(self, steps)?.owner_complete(owner)
            || !raw.membership_domains(self, steps)?.owner_complete(owner)
            || semantic.contains(&owner)
        {
            return None;
        }
        let relationships = super::semantic_ownership::owned_relationships(self, owner)?;
        charge(&mut Some(&mut *steps), relationships.len())?;
        if relationships
            .iter()
            .any(|rel| is_a!(self.elements[rel], "ElementFilterMembership"))
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
        // Semantic metadata adds a base the planner does not write (KerML
        // 9.2); plain metadata adds none.
        let semantic = self.semantically_annotated();
        let mut budget = Some(steps);
        charge(&mut budget, imports.0.len().saturating_add(imports.1.len()))?;
        let mut todo: Vec<_> = imports
            .0
            .iter()
            .chain(&imports.1)
            .filter_map(|m| {
                self.elements[m.member]
                    .conforms("Feature")
                    .then_some(m.member)
            })
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
        let mut seen = IdSet::default();
        let mut dependency = Reachability::sparse();
        let mut owners = IdMap::default();
        let mut authored = IdMap::default();
        let mut redefinitions = IdMap::default();
        let mut roles = IdSet::default();
        let mut external_roles = IdSet::default();
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
                || semantic.contains(&feature)
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
                || semantic.contains(&owner)
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
            let mut seen_relationships = IdSet::default();
            let mut authored_targets = Vec::new();
            let mut targets = Vec::new();
            for relationship in relationships {
                if !is_a!(self.elements[relationship], "Redefinition")
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
                if self.is_authored(relationship) {
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
            let mut acyclic = IdMap::default();
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
        let mut unique = IdSet::default();
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
        incomplete: &IdSet<usize>,
        steps: &mut usize,
        proof: &mut ImportProof,
    ) -> Option<()> {
        // Semantic metadata adds a base the planner does not write (KerML
        // 9.2); plain metadata adds none.
        let semantic = self.semantically_annotated();
        charge(&mut Some(&mut *steps), 1)?;
        if !matches!(self.elements[root].ty, "Class" | "Behavior" | "Function") {
            return None;
        }
        if proof.role_domains.contains(&root) {
            return Some(());
        }
        let domains = raw.membership_domains(self, steps)?;
        let imports = raw.import_domains(self, steps)?;
        let mut visited = IdSet::default();
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
                || semantic.contains(&owner)
                || self
                    .elem_scope
                    .get(&owner)
                    .is_some_and(|&s| !self.scopes[s].filters.is_empty())
            {
                return None;
            }
            let base = bases.get(&owner).unwrap_or(&[][..]);
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
                    if is_a!(self.elements[member], "Feature") {
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
        incomplete: &IdSet<usize>,
        steps: &mut Option<&mut usize>,
    ) -> Option<(Vec<PositionalMembership>, Vec<PositionalMembership>)> {
        charge(steps, self.elements[owner].owned_relationships.len())?;
        let imports: Vec<_> = self.elements[owner]
            .owned_relationships
            .iter()
            .copied()
            .filter(|&r| {
                is_a!(self.elements[r], "Import")
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
            let memberships = if is_a!(self.elements[import], "MembershipImport") {
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
                        is_a!(self.elements[r], "Membership") && self.import_admitted(r, access)
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
        incomplete: &IdSet<usize>,
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
                && bases.get(&owner).is_none_or(<[usize]>::is_empty)
                && !self.elements[owner].owned_relationships.iter().any(|&r| {
                    is_a!(self.elements[r], "Import") || is_a!(self.elements[r], "Specialization")
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
            .is_some_and(|r| is_a!(self.elements[r], "ReturnParameterMembership"))
    }

    /// Whether a parameter is an input: its written direction `in` or
    /// `inout`, or none written under a parameter membership, whose default
    /// is `in` (a return parameter membership's is `out`).
    pub(super) fn positional_is_input(&self, e: usize) -> bool {
        match self.elements[e].props.get("direction") {
            Some(value) => matches!(value.as_str(), Some("in" | "inout")),
            None => self.elements[e].owning_relationship.is_some_and(|r| {
                super::behavior::parameter_direction_default(self.elements[r].ty) == Some("in")
            }),
        }
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
                is_a!(self.elements[r], "Membership")
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

    /// The features `e` redefines as the semantic passes read them, as a
    /// list (see [`Self::semantic_redefinition_targets_into`]).
    #[cfg(test)]
    pub(super) fn semantic_redefinition_targets(
        &mut self,
        e: usize,
        include_implied: bool,
    ) -> Vec<usize> {
        let mut targets = Vec::new();
        self.semantic_redefinition_targets_into(e, include_implied, &mut targets);
        targets
    }

    /// The features `e` redefines as the semantic passes read them, pushed
    /// onto `out`: the recorded targets first, then the positional ones not
    /// among them — so a walk's stack takes them without an allocation per
    /// element.
    pub(super) fn semantic_redefinition_targets_into(
        &mut self,
        e: usize,
        include_implied: bool,
        out: &mut Vec<usize>,
    ) {
        let recorded = self.indexed_redefinition_targets_shared(e);
        let start = out.len();
        out.extend(recorded.iter().copied());
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
                if !out[start..].contains(&target) {
                    out.push(target);
                }
            }
        }
    }
}

// Structural cycle evidence for newly admitted authored/positional closures.
// This validates the inspected graph; the common planner still derives all edges.
fn acyclic_redefinition_closure(
    root: usize,
    graph: &IdMap<usize, Vec<usize>>,
    state: &mut IdMap<usize, u8>,
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
    graph: &mut IdMap<usize, Vec<usize>>,
    library: &ListsByRow<usize>,
    added: &mut IdMap<usize, Vec<usize>>,
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
            .or_insert_with(|| {
                library
                    .get(source)
                    .map(<[usize]>::to_vec)
                    .unwrap_or_default()
            })
            .push(target);
        added.entry(source).or_default().push(target);
    }
    Some(())
}

/// Whether `f` is a case's objective (owned through an `ObjectiveMembership`).
fn owned_as_objective(b: &Builder, f: usize) -> bool {
    b.elements[f]
        .owning_relationship
        .is_some_and(|r| is_a!(b.elements[r], "ObjectiveMembership"))
}

/// A complete type's effective features: planned here, or by the library.
fn effective_of<'a>(
    effective: &'a IdMap<usize, Vec<usize>>,
    planned: &'a PlannedLibraryTypes,
    e: &usize,
) -> &'a [usize] {
    effective
        .get(e)
        .map(Vec::as_slice)
        .or_else(|| planned.effective.get(*e))
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
        let graph = IdMap::from_iter([(0, vec![1, 2]), (1, vec![3]), (2, vec![3]), (3, vec![0])]);
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
        // Without a library the operator's function is nothing to the
        // static plan; a caller supplying a callee base plans the pairing
        // for itself without publishing it.
        let mut model = crate::model::Model::new();
        model.add_source(
            "positional.kerml",
            "function F {in p; return result;} feature sum=1+2;",
        );
        assert!(!model.has_errors());
        let mut r = super::super::ResolvedModel::build(&model);
        let function = r.resolve_qualified("F").unwrap().0;
        let parameter = r.resolve_qualified("F::p").unwrap().0;
        let invocation =
            r.b.elements
                .iter()
                .position(|e| e.ty == "OperatorExpression")
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
        let mut members: IdSet<_> = (0..4096).collect();
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
            let mut graph = IdMap::default();
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
        let mut graph = IdMap::from_iter([(0, vec![1, 2]), (1, vec![3]), (2, vec![3])]);
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

    #[test]
    fn an_exhausted_budgeted_attempt_is_not_repeated_with_no_more_budget() {
        let mut model = crate::model::Model::new();
        model.add_source(
            "exhausted.kerml",
            "function A {in p; return result;} function B specializes A {in q; return r;} feature call=B(1);",
        );
        assert!(!model.has_errors());
        let mut r = super::super::ResolvedModel::build(&model);
        r.b.positional_redefinitions = None;
        assert!(r.b.positional_budget_exhausted.is_none());
        // Two steps of budget: the entry charge takes one, the chain-evidence
        // refresh the other, and the planning does not fit in what is left.
        let mut steps = crate::eval::MAX_STEPS - 2;
        assert!(!r.b.ensure_positional_redefinitions_with_budget(&mut steps));
        assert!(r.b.positional_redefinitions.is_none());
        assert!(
            steps >= crate::eval::MAX_STEPS,
            "the attempt charged its work"
        );
        let exhausted = r.b.positional_budget_exhausted.clone().expect("remembered");
        assert_eq!(exhausted.remaining, 1);
        // The same budget over the same inputs is refused after the entry charge alone.
        let mut again = crate::eval::MAX_STEPS - 2;
        assert!(!r.b.ensure_positional_redefinitions_with_budget(&mut again));
        assert_eq!(again, crate::eval::MAX_STEPS - 1);
        // Less budget likewise.
        let mut less = crate::eval::MAX_STEPS - 1;
        assert!(!r.b.ensure_positional_redefinitions_with_budget(&mut less));
        assert_eq!(less, crate::eval::MAX_STEPS);
        // More budget plans again: the attempt charges past the entry.
        let mut more = crate::eval::MAX_STEPS - 3;
        let planned = r.b.ensure_positional_redefinitions_with_budget(&mut more);
        assert!(planned || more >= crate::eval::MAX_STEPS - 1);
        r.b.positional_redefinitions = None;
        assert!(r.b.positional_budget_exhausted.is_some() || planned);
        // A change to the resolved specialization targets is a new input:
        // the same budget plans again, although no element row changed.
        let mut steps = crate::eval::MAX_STEPS - 2;
        assert!(!r.b.ensure_positional_redefinitions_with_budget(&mut steps));
        let rows = r.b.elements.observe_revision();
        let target = r.b.spec_resolved[0];
        r.b.spec_resolved[0] = None;
        r.b.spec_resolved[0] = target;
        assert!(rows.same_as(&r.b.elements.observe_revision()));
        let mut retried = crate::eval::MAX_STEPS - 2;
        assert!(!r.b.ensure_positional_redefinitions_with_budget(&mut retried));
        assert!(
            retried >= crate::eval::MAX_STEPS,
            "a changed input is planned again"
        );
        // Dropping the plan for another library-name configuration forgets
        // the exhausted attempt as well.
        assert!(r.b.positional_budget_exhausted.is_some());
        r.set_library_names(&HashMap::new());
        assert!(r.b.positional_budget_exhausted.is_none());
        // The whole budget publishes, and a published plan is answered before
        // any memory is consulted.
        assert!(r.b.ensure_positional_redefinitions_with_budget(&mut 0));
        assert!(r.b.positional_redefinitions.is_some());
        assert!(r.b.positional_budget_exhausted.is_none());
        let mut none = crate::eval::MAX_STEPS - 2;
        assert!(r.b.ensure_positional_redefinitions_with_budget(&mut none));
    }

    #[test]
    fn a_published_plan_makes_the_budgeted_path_free_of_planning() {
        let mut model = crate::model::Model::new();
        model.add_source(
            "published.kerml",
            "function A {in p; return result;} feature call=A(1);",
        );
        assert!(!model.has_errors());
        let mut r = super::super::ResolvedModel::build(&model);
        r.b.ensure_positional_redefinitions();
        assert!(r.b.has_positional_plan());
        assert!(r.b.positional_budget_exhausted.is_none());
        let mut steps = crate::eval::MAX_STEPS - 2;
        assert!(r.b.ensure_positional_redefinitions_with_budget(&mut steps));
        assert_eq!(
            steps,
            crate::eval::MAX_STEPS,
            "entry charge and refresh only"
        );
        assert!(r.b.positional_budget_exhausted.is_none());
    }
}

#[cfg(test)]
mod wire_rows_tests {
    use super::*;
    use crate::bulk::Ints;

    fn roles(types: &[usize], lists: &[(usize, Vec<usize>)]) -> RoleLists {
        RoleLists {
            types: Ints(types.to_vec()),
            ends: lists.to_vec().into(),
            results: lists.to_vec().into(),
            parameters: lists.to_vec().into(),
        }
    }

    /// The roles' columns must name the same types, within the rows, with
    /// every feature within the rows.
    #[test]
    fn roles_columns_that_disagree_or_leave_the_rows_are_refused() {
        let lists = vec![(1, vec![2]), (3, vec![])];
        let (ends, results, parameters) = roles(&[1, 3], &lists).into_rows(4).unwrap();
        assert_eq!(ends.get(1), Some(&[2][..]));
        assert_eq!(results.get(3), Some(&[][..]));
        assert_eq!(parameters.get(0), None);
        assert!(
            roles(&[1, 2], &lists).into_rows(4).is_none(),
            "the types disagree"
        );
        assert!(
            roles(&[1, 3], &lists).into_rows(3).is_none(),
            "a type past the rows"
        );
        assert!(
            roles(&[1], &[(1, vec![5])]).into_rows(3).is_none(),
            "a feature past the rows"
        );
    }

    /// The memberships' columns must cover each other, within the rows.
    #[test]
    fn membership_columns_that_do_not_cover_each_other_are_refused() {
        let lists = |types: Vec<usize>, lengths: Vec<usize>, rel: Vec<usize>, mem: Vec<usize>| {
            MembershipLists {
                types: Ints(types),
                lengths: Ints(lengths),
                relationships: Ints(rel),
                members: Ints(mem),
            }
        };
        let laid = lists(vec![1], vec![1], vec![2], vec![3])
            .into_rows(4)
            .unwrap();
        assert_eq!(
            laid.get(1).map(|m| (m[0].relationship, m[0].member)),
            Some((2, 3))
        );
        assert!(
            lists(vec![1], vec![1], vec![2], vec![])
                .into_rows(4)
                .is_none(),
            "relationships and members differ"
        );
        assert!(
            lists(vec![1], vec![2], vec![2], vec![3])
                .into_rows(4)
                .is_none(),
            "a length past the values"
        );
        assert!(
            lists(vec![1], vec![1], vec![4], vec![3])
                .into_rows(4)
                .is_none(),
            "a relationship past the rows"
        );
        assert!(
            lists(vec![1], vec![1], vec![2], vec![4])
                .into_rows(4)
                .is_none(),
            "a member past the rows"
        );
    }
}
