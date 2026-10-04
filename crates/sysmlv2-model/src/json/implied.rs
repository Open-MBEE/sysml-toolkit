//! Implied relationships, materialized lazily in the resolved model.
//!
//! SysML 8.4.2 Tables 31/32 give every definition and usage kind a library
//! base it implicitly specializes (`part def` → `Parts::Part`, `part` →
//! `Parts::parts`, …), and a variant usage implicitly specializes the
//! variation it is a variant of (SysML `checkUsageVariationDefinition-
//! Specialization` / `-UsageSpecialization`: a FeatureTyping to the
//! owning variation definition — an enumeration literal's typing — or a
//! Subsetting to the owning variation usage). These relationships are
//! part of the abstract syntax (`isImplied = true`, listed under the
//! specific element's `ownedRelationship` when `isImpliedIncluded`), but
//! the builder never creates them: the lowering keeps the element graph
//! at what the text says, and name resolution reads the same tables as
//! implied heritage instead ([`super::implicit_def_bases`]).
//!
//! The derivation layer materializes them on first demand for the whole
//! model. Library/variation bases are planned when library names are known,
//! from a loaded library or a name table ([`ResolvedModel::set_library_names`]).
//! Supported positional redefinitions between local elements are also
//! materialized, including for models without a library. Library declarations
//! participate because their own kind-required bases and positional
//! redefinitions need not be written explicitly. One relationship element per
//! implied specialization is appended
//! to the element list past every explicit element (`Builder::implied_from`
//! marks the boundary, so the checks, lints and iteration over the model
//! keep to the explicit elements), owned by its specific side through a
//! side table rather than the owner's `ownedRelationship` row — the
//! resolver, the expression evaluator and the language server keep the
//! explicit graph they were built on. The relationship families read the
//! side table ([`ResolvedModel::implied_relationships`]); the full-form
//! emitter takes its implied relationships from here.
//!
//! Ids are the emitter's: `uuid5(OID, "{owner id}/implied{n}")` with `n`
//! the relationship's former position among its owner's implied ones. New
//! edges use `uuid5(OID, "{owner id}/implied/{metaclass}/{target id}")`.
//! An edge is omitted only when another specialization path reaches its
//! required target; cycle-safe elimination keeps each requirement reachable.
//! The unconditional inherited Feature requirement independently contributes
//! Base::things when its loaded canonical Feature identity is established;
//! variable, end and portion constraints add separate obligations.

use super::{Builder, Elem, ElementRef, ResolvedModel, implicit_def_bases, implicit_usage_bases};
use crate::lift::{def_kind_of, usage_kind_of};
use crate::metaclass::conforms;
use serde_json::json;
use std::collections::{HashMap, HashSet};
use std::sync::{Arc, OnceLock};
use sysmlv2_syntax::ast::Dialect;
use uuid::Uuid;

/// One kind's implied specializations: the library bases (qualified
/// names), the relationship metaclass, its source and target keys, and
/// the explicit metaclasses that cover them.
type ImpliedBases = (
    &'static [&'static str],
    &'static str,
    &'static str,
    &'static str,
    &'static [&'static str],
);

type SpecializationGraph = HashMap<Uuid, Vec<Uuid>>;
type StaticPlannerBases = (HashMap<usize, Vec<usize>>, HashSet<usize>);

type PlannedEdge = (&'static str, &'static str, &'static str, Uuid);

pub(super) type RetainedTypings = HashMap<usize, Vec<(&'static str, Uuid)>>;

/// The immutable supported library/variation plan. The positional graph and
/// materialized relationship graph share this calculation, but own any later
/// positional edges independently.
pub(super) struct SupportedImpliedSpecializations {
    candidates: Candidates,
    /// The final specialization graph and the retained targets by owner. A
    /// prepared library's plan keeps both frozen, and a plan extending it adds
    /// a build's own entries over them (see [`super::LibraryPlans`]).
    graph: crate::layered::LayeredMap<Uuid, Vec<Uuid>>,
    by_owner: crate::layered::LayeredMap<usize, Vec<Uuid>>,
    typing_by_owner: OnceLock<Arc<RetainedTypings>>,
    library_configuration: bool,
    expression_targets: HashMap<&'static str, Uuid>,
    chain_bases: Arc<super::type_relations::FeatureChainBases>,
    // Validation memo only: the graph stays immutable and the token is the
    // existing row revision, never a separate semantic generation.
    source_rows: std::sync::Mutex<crate::layered::Revision>,
    source_names: crate::layered::Revision,
}

/// A plan's candidate edges with whether each was retained, in the order a
/// plan of every row lists them: the kinds' and variants' requirements, then
/// the succession endpoints'. A plan extending a prepared library's lists the
/// library plan's before its own in each part, without copying them.
pub(super) struct Candidates {
    library: Option<Arc<SupportedImpliedSpecializations>>,
    own: Vec<(usize, PlannedEdge)>,
    /// The own candidates before this index are the kinds' and variants'
    /// requirements, the rest the succession endpoints'.
    kinds: usize,
    retained: Vec<bool>,
}

type Candidate<'a> = (&'a (usize, PlannedEdge), bool);

fn zip_part<'a>(
    candidates: &'a [(usize, PlannedEdge)],
    retained: &'a [bool],
) -> impl Iterator<Item = Candidate<'a>> + 'a {
    candidates.iter().zip(retained.iter().copied())
}

impl Candidates {
    /// Every candidate, with whether it was retained, in the plan's order.
    pub(super) fn iter(&self) -> impl Iterator<Item = Candidate<'_>> + '_ {
        let (library, retained, kinds): (&[(usize, PlannedEdge)], &[bool], usize) =
            match &self.library {
                Some(plan) => (
                    &plan.candidates.own,
                    &plan.candidates.retained,
                    plan.candidates.kinds,
                ),
                None => (&[], &[], 0),
            };
        zip_part(&library[..kinds], &retained[..kinds])
            .chain(self.own_kinds())
            .chain(zip_part(&library[kinds..], &retained[kinds..]))
            .chain(zip_part(
                &self.own[self.kinds..],
                &self.retained[self.kinds..],
            ))
    }
    fn own_kinds(&self) -> impl Iterator<Item = Candidate<'_>> + '_ {
        zip_part(&self.own[..self.kinds], &self.retained[..self.kinds])
    }
    /// The plan's own candidates (a library plan's are not), in order.
    pub(super) fn own(&self) -> impl Iterator<Item = Candidate<'_>> + '_ {
        zip_part(&self.own, &self.retained)
    }
    pub(super) fn len(&self) -> usize {
        self.own.len()
            + self
                .library
                .as_ref()
                .map_or(0, |plan| plan.candidates.own.len())
    }
    #[cfg(test)]
    pub(super) fn is_empty(&self) -> bool {
        self.len() == 0
    }
    #[cfg(test)]
    fn kind_count(&self) -> usize {
        self.kinds
            + self
                .library
                .as_ref()
                .map_or(0, |plan| plan.candidates.kinds)
    }
}

/// The materialized implied relationships: their owners, and each
/// owner's list in order.
#[derive(Clone)]
pub(super) struct ImpliedTable {
    /// Index of the first implied relationship in the element list.
    pub from: usize,
    /// New owned-result nodes start after the stable old implied families.
    pub(super) owned_results_from: usize,
    pub(super) owned_results_state: OwnedResultState,
    /// Known explicit and retained implied specialization targets.
    specializations: SpecializationGraph,
    static_authority: Arc<SupportedImpliedSpecializations>,
    static_rows: crate::layered::Revision,
    static_owners: HashSet<usize>,
}

pub(super) fn specialization_target(relation: &Elem) -> Option<Uuid> {
    [
        "general",
        "superclassifier",
        "type",
        "subsettedFeature",
        "redefinedFeature",
        "referencedFeature",
        "crossedFeature",
    ]
    .iter()
    .find_map(|key| relation.props.get(key))
    .and_then(|value| value.as_reference())
}

/// Required most-specific Kernel Semantic Library base of supported leaf expressions.
/// The base supplies evaluation heritage and an inherited return parameter;
/// no result is synthesized as an owned member of these expressions.
pub(super) fn literal_implied_base(ty: &str) -> Option<&'static str> {
    Some(match ty {
        "LiteralBoolean" => "Performances::literalBooleanEvaluations",
        "LiteralInteger" | "LiteralInfinity" => "Performances::literalIntegerEvaluations",
        "LiteralRational" => "Performances::literalRationalEvaluations",
        "LiteralString" => "Performances::literalStringEvaluations",
        "NullExpression" => "Performances::nullEvaluations",
        "MetadataAccessExpression" => "Performances::metadataAccessEvaluations",
        _ => return None,
    })
}

/// Most-specific supported expression base in the shared static plan.
/// Every Expression specializes evaluations (checkExpressionSpecialization).
/// Keep this primary role first for stable planning order. The generic
/// Expression obligation and inherited Boolean/Literal obligations are also
/// accumulated independently below; a missing narrower role must not erase
/// an available broader requirement.
/// Dynamic callee/result requirements remain separate.
fn expression_implied_base(ty: &str) -> Option<&'static str> {
    literal_implied_base(ty).or_else(|| {
        if ty == "ConstructorExpression" {
            Some("Performances::constructorEvaluations")
        } else {
            conforms(ty, "Expression").then_some("Performances::evaluations")
        }
    })
}

/// Inherited obligations apply to leaf expressions as well as their abstract
/// bases. The exact-leaf result-provider policy remains separate: broader
/// LiteralExpression ancestry cannot certify a missing leaf role or value.
fn additional_expression_base(ty: &str) -> Option<&'static str> {
    if conforms(ty, "BooleanExpression") {
        Some("Performances::booleanEvaluations")
    } else if conforms(ty, "LiteralExpression") {
        Some("Performances::literalEvaluations")
    } else {
        None
    }
}

fn invariant_implied_base(negated: bool) -> &'static str {
    if negated {
        "Performances::falseEvaluations"
    } else {
        "Performances::trueEvaluations"
    }
}

/// isNegated is a required Boolean with default false. Only absence uses
/// that default; an explicitly malformed value cannot select either branch.
fn invariant_negation(element: &Elem) -> Option<bool> {
    match element.props.get("isNegated") {
        None => Some(false),
        Some(value) => value.as_bool(),
    }
}

/// SysML assert/satisfy obligations accumulate independently of inherited
/// Invariant requirements. A missing narrower role never removes another one.
fn assertion_implied_base(negated: bool) -> &'static str {
    if negated {
        "Constraints::negatedConstraintChecks"
    } else {
        "Constraints::assertedConstraintChecks"
    }
}

fn satisfaction_implied_base(negated: bool) -> &'static str {
    if negated {
        "Requirements::notSatisfiedRequirementChecks"
    } else {
        "Requirements::satisfiedRequirementChecks"
    }
}

/// FeatureChainExpression fixes its operator to the canonical dot Function.
/// This typing is independent of its still-incomplete owned expression graph.
const CHAIN_FUNCTION: &str = "ControlFunctions::.";

/// checkFeatureSpecialization is unconditional for every Feature descendant,
/// including variable, end and portion features. Other families remain separate.
const FEATURE_BASE: &str = "Base::things";
const STEP_BASE: &str = "Performances::performances";
const TYPED_FEATURE_BASES: [(&str, &str); 3] = [
    ("Structure", "Objects::objects"),
    ("Class", "Occurrences::occurrences"),
    ("DataType", "Base::dataValues"),
];

const BINARY_ROLES: [(&str, &str); 4] = [
    ("Connections::BinaryConnection", "ConnectionDefinition"),
    ("Interfaces::BinaryInterface", "InterfaceDefinition"),
    ("Connections::binaryConnections", "ConnectionUsage"),
    ("Interfaces::binaryInterfaces", "InterfaceUsage"),
];

pub(super) fn binary_role_name(package: &str, member: &str) -> Option<&'static str> {
    match (package, member) {
        ("Connections", "BinaryConnection") => Some(BINARY_ROLES[0].0),
        ("Interfaces", "BinaryInterface") => Some(BINARY_ROLES[1].0),
        ("Connections", "binaryConnections") => Some(BINARY_ROLES[2].0),
        ("Interfaces", "binaryInterfaces") => Some(BINARY_ROLES[3].0),
        _ => None,
    }
}

fn expression_role_kind(name: &str) -> &'static str {
    if let Some((_, kind)) = BINARY_ROLES.iter().find(|(role, _)| *role == name) {
        return kind;
    }
    match name {
        CHAIN_FUNCTION => "Function",
        STEP_BASE => "Step",
        "Items::Item::subitems" => "ItemUsage",
        "Items::Item::subparts" => "PartUsage",
        "Objects::Object::subobjects"
        | "Occurrences::Occurrence::suboccurrences"
        | FEATURE_BASE
        | "Objects::objects"
        | "Occurrences::occurrences"
        | "Base::dataValues" => "Feature",
        "Constraints::assertedConstraintChecks" | "Constraints::negatedConstraintChecks" => {
            "ConstraintUsage"
        }
        "Requirements::satisfiedRequirementChecks"
        | "Requirements::notSatisfiedRequirementChecks" => "RequirementUsage",
        // Every supported Performances evaluation role is declared as an expr
        // in the pinned Kernel Semantic Library. Feature/Step siblings do not
        // establish that role, even with its canonical name and loaded UUID.
        _ => "Expression",
    }
}

fn planning_charge(steps: &mut Option<&mut usize>, amount: usize) -> Option<()> {
    if let Some(steps) = steps {
        **steps = steps.saturating_add(amount);
        if **steps > crate::eval::MAX_STEPS {
            return None;
        }
    }
    Some(())
}

/// Stable descending order of dense DFS ranks. Candidate order within a rank
/// must survive: it decides which cycle anchor is retained by reduction.
fn reverse_rank_order(
    indices: std::ops::Range<usize>,
    rank_count: usize,
    rank_at: impl Fn(usize) -> usize,
    steps: &mut Option<&mut usize>,
) -> Option<Vec<usize>> {
    planning_charge(steps, rank_count)?;
    let mut buckets = vec![Vec::new(); rank_count];
    let count = indices.len();
    for index in indices {
        planning_charge(steps, 1)?;
        buckets[rank_at(index)].push(index);
    }
    planning_charge(steps, rank_count.saturating_add(count))?;
    Some(buckets.into_iter().rev().flatten().collect())
}

impl SupportedImpliedSpecializations {
    /// This plan with its final graph and retained targets frozen: a prepared
    /// library's own, which the plans extending it share.
    fn into_frozen(mut self) -> Self {
        self.graph.freeze();
        self.by_owner.freeze();
        self
    }
}

#[cfg(test)]
fn same_map<K: Eq + std::hash::Hash, V: PartialEq>(
    a: &crate::layered::LayeredMap<K, V>,
    b: &crate::layered::LayeredMap<K, V>,
) -> bool {
    a.iter().count() == b.iter().count() && a.iter().all(|(k, v)| b.get(k) == Some(v))
}

#[cfg(test)]
impl SupportedImpliedSpecializations {
    /// The first field in which two plans differ, the memo and the row
    /// revisions aside.
    pub(super) fn difference(&self, other: &Self) -> Option<String> {
        let first =
            |what: &str, a: String, b: String| (a != b).then(|| format!("{what}: {a} != {b}"));
        let listed = |plan: &Self| -> Vec<(usize, PlannedEdge)> {
            plan.candidates.iter().map(|(c, _)| *c).collect()
        };
        let (mine, theirs) = (listed(self), listed(other));
        if mine != theirs {
            let at = mine
                .iter()
                .zip(&theirs)
                .position(|(a, b)| a != b)
                .unwrap_or(mine.len().min(theirs.len()));
            return Some(format!(
                "candidates differ at {at} of {}/{}: {:?} != {:?}",
                mine.len(),
                theirs.len(),
                mine.get(at),
                theirs.get(at)
            ));
        }
        let kept = |plan: &Self| -> Vec<bool> { plan.candidates.iter().map(|(_, r)| r).collect() };
        first(
            "kind candidates",
            self.candidates.kind_count().to_string(),
            other.candidates.kind_count().to_string(),
        )
        .or_else(|| {
            let (mine_kept, theirs_kept) = (kept(self), kept(other));
            (mine_kept != theirs_kept).then(|| {
                let at = mine_kept.iter().zip(&theirs_kept).position(|(a, b)| a != b);
                format!("retained differs at {at:?}: {:?}", at.map(|at| mine[at]))
            })
        })
        .or_else(|| (!same_map(&self.graph, &other.graph)).then(|| "final graph".to_string()))
        .or_else(|| (!same_map(&self.by_owner, &other.by_owner)).then(|| "by owner".to_string()))
        .or_else(|| {
            (self.chain_bases.targets != other.chain_bases.targets
                || self.chain_bases.incomplete != other.chain_bases.incomplete)
                .then(|| "chain bases".to_string())
        })
        .or_else(|| {
            (self.expression_targets != other.expression_targets)
                .then(|| "expression targets".to_string())
        })
        .or_else(|| {
            (self.library_configuration != other.library_configuration)
                .then(|| "configuration".to_string())
        })
    }
}

impl Builder {
    /// Every retained-plan consumer refreshes these common source facts before
    /// reusing the graph. Refusal never advances the memo or poisons a retry.
    pub(super) fn refresh_supported_chain_evidence(
        &mut self,
        mut steps: Option<&mut usize>,
    ) -> Option<()> {
        planning_charge(&mut steps, 1)?;
        let Some(plan) = self.supported_implied.clone() else {
            // A positional cache cannot outlive its required-base authority.
            planning_charge(
                &mut steps,
                self.positional_redefinitions.as_ref().map_or(0, |p| {
                    p.targets.capacity().saturating_add(p.incomplete.capacity())
                }),
            )?;
            self.positional_redefinitions = None;
            return Some(());
        };
        if self.supported_chain_evidence_current() {
            return Some(());
        }
        // Arbitrary row edits can also change positional ownership/order or
        // the authored graph used to minimize requirements. Chain-only equality
        // cannot certify those dependencies. Known append transactions advance
        // source_rows themselves; every other edit requires a new common plan.
        // Hash maps containing Vec values scan buckets on final drop. Their
        // flat Copy payloads do not require element-by-element destruction.
        let retirement = plan
            .graph
            .local_capacity()
            .saturating_add(plan.by_owner.local_capacity())
            .saturating_add(plan.typing_by_owner.get().map_or(0, |m| m.capacity()))
            .saturating_add(self.positional_redefinitions.as_ref().map_or(0, |p| {
                p.targets.capacity().saturating_add(p.incomplete.capacity())
            }));
        planning_charge(&mut steps, retirement)?;
        self.supported_implied = None;
        self.positional_redefinitions = None;
        Some(())
    }

    fn static_source_facts_current(&self, plan: &SupportedImpliedSpecializations) -> bool {
        self.elements
            .revision()
            .is_some_and(|now| plan.source_rows.lock().unwrap().same_as(now))
            && self
                .lib_qnames
                .revision()
                .is_some_and(|now| plan.source_names.same_as(now))
            && plan.library_configuration == self.external_implied_names.is_empty()
    }
    pub(super) fn supported_chain_evidence_current(&self) -> bool {
        self.supported_implied
            .as_ref()
            .is_some_and(|plan| self.static_source_facts_current(plan))
    }
    pub(super) fn physical_static_authority_current(&self) -> bool {
        self.implied.as_ref().is_none_or(|table| {
            // Clearing optional lookup caches is not semantic invalidation. The
            // table still retains the exact recipe authority and its source facts.
            self.static_source_facts_current(&table.static_authority)
                && self
                    .supported_implied
                    .as_ref()
                    .is_none_or(|plan| Arc::ptr_eq(plan, &table.static_authority))
                && self
                    .elements
                    .revision()
                    .is_some_and(|rows| table.static_rows.same_as(rows))
        })
    }
    /// Revalidate the complete existing prefix after arbitrary edits/remaps.
    /// Failed physical recipes stay addressable but cannot prove semantics.
    pub(super) fn certify_materialized_static_prefix(&mut self, steps: &mut usize) -> Option<bool> {
        planning_charge(&mut Some(&mut *steps), 1)?;
        if self.physical_static_authority_current() {
            return Some(true);
        }
        if self.positional_planning {
            return Some(false);
        }
        let boundary = self.implied.as_ref()?.owned_results_from;
        planning_charge(
            &mut Some(&mut *steps),
            self.lib_qnames
                .len()
                .saturating_add(self.external_implied_names.len()),
        )?;
        for (_, parts) in &self.lib_qnames {
            planning_charge(&mut Some(&mut *steps), parts.len())?;
            for part in parts {
                planning_charge(&mut Some(&mut *steps), part.len())?;
            }
        }
        for name in self.external_implied_names.keys() {
            planning_charge(&mut Some(&mut *steps), name.len())?;
        }
        let names = self
            .lib_qnames
            .iter()
            .map(|(id, parts)| (parts.join("::"), *id))
            .chain(
                self.external_implied_names
                    .iter()
                    .map(|(name, id)| (name.clone(), *id)),
            )
            .collect();
        let prefix = self.static_specialization_prefix(
            &names,
            self.external_implied_names.is_empty(),
            Some(&mut *steps),
        )?;
        let captured =
            super::dynamic_invocations::capture_static_prefix(self, prefix, Some(boundary), steps);
        planning_charge(&mut Some(&mut *steps), 0)?;
        Some(captured.is_ok())
    }
    pub(super) fn static_chain_row_current(&self, relationship: usize) -> bool {
        self.implied.as_ref().is_none_or(|table| {
            !(table.from..table.owned_results_from).contains(&relationship)
                || self.physical_static_authority_current()
        })
    }
    fn static_chain_owner_current(&self, owner: usize) -> bool {
        self.implied.as_ref().is_none_or(|table| {
            !table.static_owners.contains(&owner) || self.physical_static_authority_current()
        })
    }
    // Called only after capture_static_prefix validates every physical recipe.
    // A new current plan alone is never sufficient to bless old physical rows.
    pub(super) fn recertify_physical_static_authority(&mut self, steps: &mut usize) -> Option<()> {
        if self.physical_static_authority_current() {
            return Some(());
        }
        let plan = self.supported_implied.clone()?;
        planning_charge(&mut Some(&mut *steps), self.elements.len())?;
        for element in &self.elements {
            planning_charge(&mut Some(&mut *steps), element.owned_relationships.len())?;
        }
        let owners = self.semantic_relationship_owners();
        let (_, graph) = self.required_specialization_edges_with_chain_bases(
            &[],
            0,
            self.elements.len(),
            &owners,
            &plan.chain_bases,
            Some(&mut *steps),
        )?;
        // Retire the old compatibility graph only after charged reconstruction.
        planning_charge(
            &mut Some(&mut *steps),
            self.implied.as_ref()?.specializations.capacity(),
        )?;
        let rows = self.elements.observe_revision();
        if let Some(table) = &mut self.implied {
            table.static_authority = plan;
            table.static_rows = rows;
            table.specializations = graph;
        }
        Some(())
    }

    /// Structural owners, including memberships without a name or body scope.
    fn specialization_relation_owners(&self) -> Vec<Option<usize>> {
        let mut owners = vec![None; self.elements.len()];
        for (owner, element) in self.elements.iter().enumerate() {
            for &relationship in &element.owned_relationships {
                owners[relationship] = Some(owner);
            }
        }
        owners
    }

    /// The library bases each of `requirement_candidates` (types and variant
    /// members) requires by its kind, and a composite feature by its owned
    /// typing, as candidates for the minimizer.
    fn kind_requirements(
        &mut self,
        requirement_candidates: Vec<usize>,
        names: &HashMap<String, Uuid>,
        expression_targets: &HashMap<&'static str, Uuid>,
        owners: &[Option<usize>],
        mut steps: Option<&mut usize>,
    ) -> Option<Vec<(usize, PlannedEdge)>> {
        let mut candidates = Vec::new();
        planning_charge(&mut steps, super::type_relations::COMPOSITE_ROLES.len())?;
        let typing_structure = if self.graph_format == crate::model::GraphFormat::CanonicalV3
            || super::type_relations::COMPOSITE_ROLES
                .iter()
                .any(|role| expression_targets.contains_key(role))
        {
            let mut local = 0;
            let evidence = (|| {
                let steps = steps.as_deref_mut().unwrap_or(&mut local);
                let raw = super::structural_index::StoredStructure::for_query(self, steps)?;
                let typing = raw.typing(self, steps)?;
                Some((raw, typing))
            })();
            if evidence.is_none() && steps.is_some() {
                return None;
            }
            evidence
        } else {
            None
        };
        if !names.is_empty() {
            for i in requirement_candidates {
                planning_charge(&mut steps, 1 + self.elements[i].owned_relationships.len())?;
                let mut required = self.required_implied_plan(i, names, expression_targets, owners);
                if let Some((raw, typing)) = &typing_structure {
                    if conforms(self.elements[i].ty, "Feature")
                        && (self.graph_format == crate::model::GraphFormat::CanonicalV3
                            || self.elements[i]
                                .props
                                .get("isComposite")
                                .and_then(|v| v.as_bool())
                                == Some(true))
                    {
                        let typed = self.owned_typing_requirements(
                            i,
                            expression_targets,
                            raw,
                            typing,
                            &mut steps,
                        )?;
                        // The sequential minimizer always removes an earlier
                        // exact duplicate while its later copy remains live.
                        // Keep that last copy to preserve DFS visitation and
                        // the order of surviving recipes, including cycles.
                        if !typed.is_empty() {
                            planning_charge(
                                &mut steps,
                                required.len().saturating_mul(typed.len()),
                            )?;
                            required.retain(|edge| !typed.contains(edge));
                            required.extend(typed);
                        }
                    }
                }
                candidates.extend(required.into_iter().map(|edge| (i, edge)));
            }
        }
        Some(candidates)
    }

    /// The supported direct implied requirements, shared by positional rules
    /// and lazy relationship materialization. Library-owned requirements matter:
    /// library declarations can themselves omit a kind-required generalization.
    fn supported_implied_specializations(
        &mut self,
        names: &HashMap<String, Uuid>,
        use_library_cache: bool,
    ) -> Arc<SupportedImpliedSpecializations> {
        self.supported_implied_specializations_with_budget(names, use_library_cache, None)
            .expect("unbounded implied planning cannot exhaust its budget")
    }

    fn supported_implied_specializations_with_budget(
        &mut self,
        names: &HashMap<String, Uuid>,
        use_library_cache: bool,
        mut steps: Option<&mut usize>,
    ) -> Option<Arc<SupportedImpliedSpecializations>> {
        self.refresh_supported_chain_evidence(steps.as_deref_mut())?;
        if use_library_cache {
            if let Some(plan) = &self.supported_implied {
                if plan.library_configuration {
                    return Some(Arc::clone(plan));
                }
            }
            // A build on a prepared library plans its own rows on top of the
            // plan of the library's.
            if let Some(library) = self.library_plans(steps.as_deref_mut())? {
                if let Some(plan) =
                    self.supported_implied_on_library(&library, names, steps.as_deref_mut())?
                {
                    self.supported_implied = Some(Arc::clone(&plan));
                    return Some(plan);
                }
            }
        }
        planning_charge(&mut steps, self.elements.len())?;
        let mut requirement_candidates = Vec::new();
        for (i, element) in self.elements.iter().enumerate() {
            planning_charge(&mut steps, element.owned_relationships.len())?;
            // All kind-based requirements belong to Types. Variant ownership
            // is an independent recipe, so retain even a non-Type variant row.
            // Collect during the already charged complete ownership scan.
            if i < self.explicit_len()
                && (conforms(element.ty, "Type")
                    || element.owning_relationship.is_some_and(|membership| {
                        self.elements
                            .get(membership)
                            .is_some_and(|row| row.ty == "VariantMembership")
                    }))
            {
                requirement_candidates.push(i);
            }
        }
        let owners = self.specialization_relation_owners();
        let expression_targets = self.expression_target_names(names, &mut steps)?;
        let mut candidates = self.kind_requirements(
            requirement_candidates,
            names,
            &expression_targets,
            &owners,
            steps.as_deref_mut(),
        )?;
        let kind_candidates = candidates.len();
        // This optional family uses a bounded certificate even on a legacy
        // unbounded call. Failure publishes no partial endpoints.
        let endpoints = if let Some(steps) = steps.as_deref_mut() {
            super::succession_endpoints::endpoints(self, steps)?
        } else {
            super::succession_endpoints::endpoints(self, &mut 0).unwrap_or_default()
        };
        for (source, target) in endpoints {
            candidates.push((
                source,
                (
                    "ReferenceSubsetting",
                    "subsettingFeature",
                    "referencedFeature",
                    self.elements[target].id,
                ),
            ));
        }
        let chain_bases = self.checked_chain_bases(self.explicit_len(), steps.as_deref_mut())?;
        let (retained, graph) = self.required_specialization_edges_with_chain_bases(
            &candidates,
            0,
            self.explicit_len(),
            &owners,
            &chain_bases,
            steps.as_deref_mut(),
        )?;
        let mut by_owner = crate::layered::LayeredMap::<usize, Vec<Uuid>>::default();
        for (i, &(owner, edge)) in candidates.iter().enumerate() {
            planning_charge(&mut steps, 1)?;
            if retained[i] {
                by_owner.entry(owner).or_default().push(edge.3);
            }
        }
        let plan = Arc::new(SupportedImpliedSpecializations {
            candidates: Candidates {
                library: None,
                own: candidates,
                kinds: kind_candidates,
                retained,
            },
            graph: graph.into_iter().collect(),
            by_owner,
            typing_by_owner: OnceLock::new(),
            library_configuration: use_library_cache,
            expression_targets,
            chain_bases,
            source_rows: std::sync::Mutex::new(self.elements.observe_revision()),
            source_names: self.lib_qnames.observe_revision(),
        });
        // Name setters, ID changes, binding replay and model append invalidate
        // this cache. External plans may be reused by read-only value proofs;
        // other callers retain their explicit external-plan rebuild policy.
        self.supported_implied = Some(Arc::clone(&plan));
        Some(plan)
    }

    /// [`Self::supported_implied_specializations_with_budget`] for a build
    /// that extends its prepared library's plans (see [`super::LibraryPlans`]):
    /// the requirements of this build's own rows, its own successions'
    /// endpoints and its own features' chain bases, minimized over the
    /// library plan's final graph, put together with the library plan in the
    /// order a plan of every row lists its candidates — the library's kinds'
    /// requirements, this build's, the library's endpoints, this build's.
    /// `Some(None)` when the plan cannot be extended this way.
    fn supported_implied_on_library(
        &mut self,
        library: &super::LibraryPlans,
        names: &HashMap<String, Uuid>,
        mut steps: Option<&mut usize>,
    ) -> Option<Option<Arc<SupportedImpliedSpecializations>>> {
        let plan = &library.implied;
        let floor = library.rows;
        let end = self.explicit_len();
        planning_charge(&mut steps, end - floor)?;
        let mut requirement_candidates = Vec::new();
        for i in floor..end {
            let element = &self.elements[i];
            planning_charge(&mut steps, element.owned_relationships.len())?;
            if conforms(element.ty, "Type")
                || element.owning_relationship.is_some_and(|membership| {
                    self.elements
                        .get(membership)
                        .is_some_and(|row| row.ty == "VariantMembership")
                })
            {
                requirement_candidates.push(i);
            }
        }
        let owners = self.specialization_relation_owners_from(floor);
        let expression_targets = plan.expression_targets.clone();
        let mut candidates = self.kind_requirements(
            requirement_candidates,
            names,
            &expression_targets,
            &owners,
            steps.as_deref_mut(),
        )?;
        let kind_candidates = candidates.len();
        let endpoints = if let Some(steps) = steps.as_deref_mut() {
            super::succession_endpoints::endpoints_from(self, floor, steps)?
        } else {
            super::succession_endpoints::endpoints_from(self, floor, &mut 0).unwrap_or_default()
        };
        for (source, target) in endpoints {
            candidates.push((
                source,
                (
                    "ReferenceSubsetting",
                    "subsettingFeature",
                    "referencedFeature",
                    self.elements[target].id,
                ),
            ));
        }
        let chains =
            self.checked_chain_bases_from(floor, end, library.chained, steps.as_deref_mut())?;
        let (retained, graph) = self.required_edges_on_library(
            &candidates,
            floor,
            end,
            &owners,
            &chains,
            &plan.graph,
            steps.as_deref_mut(),
        )?;
        // The library's tables are shared; this build's entries overlay them.
        let mut final_graph = plan.graph.clone();
        for (source, targets) in graph {
            final_graph.insert(source, targets);
        }
        let mut by_owner = plan.by_owner.clone();
        for (i, &(owner, edge)) in candidates.iter().enumerate() {
            planning_charge(&mut steps, 1)?;
            if retained[i] {
                by_owner.entry(owner).or_default().push(edge.3);
            }
        }
        let mut chain_bases = super::type_relations::FeatureChainBases {
            targets: plan.chain_bases.targets.clone(),
            incomplete: plan.chain_bases.incomplete.clone(),
        };
        chain_bases.targets.extend(&chains.targets);
        chain_bases.incomplete.extend(&chains.incomplete);
        Some(Some(Arc::new(SupportedImpliedSpecializations {
            candidates: Candidates {
                library: Some(Arc::clone(plan)),
                own: candidates,
                kinds: kind_candidates,
                retained,
            },
            graph: final_graph,
            by_owner,
            typing_by_owner: OnceLock::new(),
            library_configuration: true,
            expression_targets,
            chain_bases: Arc::new(chain_bases),
            source_rows: std::sync::Mutex::new(self.elements.observe_revision()),
            source_names: self.lib_qnames.observe_revision(),
        })))
    }

    /// [`Self::specialization_relation_owners`] of the rows from `start` on;
    /// the earlier rows' relationships have no owner here.
    fn specialization_relation_owners_from(&self, start: usize) -> Vec<Option<usize>> {
        let mut owners = vec![None; self.elements.len()];
        for owner in start..self.elements.len() {
            for &relationship in &self.elements[owner].owned_relationships {
                owners[relationship] = Some(owner);
            }
        }
        owners
    }

    /// [`Self::required_specialization_edges_with_chain_bases`] for a build's
    /// own rows `floor..explicit_len`, its own candidates and its own
    /// features' chain bases, over the final graph of its library's plan.
    ///
    /// A plan of every row decides the library's candidates after this
    /// build's (their sources are ranked first by the walk), and a library
    /// node's edges lead to library nodes only, so this build's candidates are
    /// decided in the same order, each by whether its target stays reachable
    /// from its source. Minimizing keeps every node a source reaches, so the
    /// library's final graph reaches what the library's whole graph does, and
    /// a library node is a leaf of the ranking walk here: none leads back to a
    /// node of this build, so the order of this build's nodes is the one a
    /// walk of every row gives.
    #[allow(clippy::too_many_arguments)]
    fn required_edges_on_library(
        &self,
        candidates: &[(usize, PlannedEdge)],
        floor: usize,
        explicit_len: usize,
        rel_owner: &[Option<usize>],
        chains: &super::type_relations::FeatureChainBases,
        library: &crate::layered::LayeredMap<Uuid, Vec<Uuid>>,
        mut steps: Option<&mut usize>,
    ) -> Option<(Vec<bool>, SpecializationGraph)> {
        planning_charge(&mut steps, 1)?;
        let mut graph: HashMap<Uuid, Vec<(Uuid, Option<usize>)>> = HashMap::new();
        for (r, relation) in self
            .elements
            .iter()
            .enumerate()
            .take(explicit_len)
            .skip(floor)
        {
            planning_charge(&mut steps, 1)?;
            if !conforms(relation.ty, "Specialization") {
                continue;
            }
            let source = [
                "specific",
                "subclassifier",
                "typedFeature",
                "subsettingFeature",
                "redefiningFeature",
                "referencingFeature",
                "crossingFeature",
            ]
            .iter()
            .find_map(|key| relation.props.get(key));
            let source = match source {
                Some(value) => value.as_reference(),
                None => rel_owner[r].map(|owner| self.elements[owner].id),
            };
            let target = specialization_target(relation);
            if let (Some(source), Some(target)) = (source, target) {
                graph.entry(source).or_default().push((target, None));
            }
        }
        for (index, &(owner, edge)) in candidates.iter().enumerate() {
            planning_charge(&mut steps, 1)?;
            graph
                .entry(self.elements[owner].id)
                .or_default()
                .push((edge.3, Some(index)));
        }
        for (&source, &target) in &chains.targets {
            planning_charge(&mut steps, 1)?;
            graph
                .entry(self.elements[source].id)
                .or_default()
                .push((self.elements[target].id, None));
        }
        let mut visited = HashSet::new();
        let mut postorder = Vec::new();
        let mut todo = Vec::new();
        for &(owner, _) in candidates {
            planning_charge(&mut steps, 1)?;
            let source = self.elements[owner].id;
            if visited.contains(&source) {
                continue;
            }
            todo.push((source, false));
            while let Some((at, exiting)) = todo.pop() {
                planning_charge(&mut steps, 1)?;
                if exiting {
                    postorder.push(at);
                } else if visited.insert(at) {
                    todo.push((at, true));
                    planning_charge(&mut steps, graph.get(&at).map_or(0, Vec::len))?;
                    todo.extend(
                        graph
                            .get(&at)
                            .into_iter()
                            .flatten()
                            .map(|&(next, _)| (next, false)),
                    );
                }
            }
        }
        planning_charge(&mut steps, postorder.len())?;
        let rank: HashMap<_, _> = postorder
            .into_iter()
            .enumerate()
            .map(|(rank, id)| (id, rank))
            .collect();
        let order = reverse_rank_order(
            0..candidates.len(),
            rank.len(),
            |index| rank[&self.elements[candidates[index].0].id],
            &mut steps,
        )?;
        planning_charge(&mut steps, candidates.len())?;
        let mut retained = vec![true; candidates.len()];
        let mut seen = HashSet::new();
        let mut stack = Vec::new();
        for index in order {
            planning_charge(&mut steps, 1)?;
            let (owner, edge) = candidates[index];
            if edge.0 == "ReferenceSubsetting" {
                continue;
            }
            retained[index] = false;
            seen.clear();
            stack.clear();
            stack.push(self.elements[owner].id);
            let mut reaches = false;
            while let Some(at) = stack.pop() {
                planning_charge(&mut steps, 1)?;
                if at == edge.3 {
                    reaches = true;
                    break;
                }
                if !seen.insert(at) {
                    continue;
                }
                if let Some(edges) = graph.get(&at) {
                    for &(next, candidate) in edges {
                        planning_charge(&mut steps, 1)?;
                        if candidate.is_none_or(|candidate| retained[candidate]) {
                            if next == edge.3 {
                                reaches = true;
                                break;
                            }
                            stack.push(next);
                        }
                    }
                } else {
                    for &next in library.get(&at).into_iter().flatten() {
                        planning_charge(&mut steps, 1)?;
                        if next == edge.3 {
                            reaches = true;
                            break;
                        }
                        stack.push(next);
                    }
                }
                if reaches {
                    break;
                }
            }
            retained[index] = !reaches;
        }
        let mut final_graph = HashMap::new();
        for (source, edges) in graph {
            planning_charge(&mut steps, 1)?;
            let mut targets = Vec::new();
            for (target, candidate) in edges {
                planning_charge(&mut steps, 1 + targets.len())?;
                if candidate.is_none_or(|candidate| retained[candidate])
                    && !targets.contains(&target)
                {
                    targets.push(target);
                }
            }
            final_graph.insert(source, targets);
        }
        Some((retained, final_graph))
    }

    /// [`Self::positional_direct_bases_from_static_plan`] for a build that
    /// extends its prepared library's plans: the library's own direct bases
    /// and those of this build's own rows, read off `plan` (the library plan
    /// extended with this build's rows).
    fn positional_direct_bases_on_library(
        &mut self,
        library: &super::LibraryPlans,
        plan: &SupportedImpliedSpecializations,
        steps: Option<&mut usize>,
    ) -> Option<StaticPlannerBases> {
        let (own, own_incomplete) = self.own_positional_direct_bases(library, plan, steps)?;
        let mut bases = library.bases.clone();
        bases.extend(own);
        let mut incomplete = library.bases_incomplete.clone();
        incomplete.extend(own_incomplete);
        Some((bases, incomplete))
    }

    /// The direct bases of this build's own types, and those of its own types
    /// whose bases are incomplete, read off `plan` (its library's plan
    /// extended with its own rows): what a build extending its library's
    /// plans adds to the library's (see [`Self::positional_direct_bases_on_library`]).
    pub(super) fn own_positional_direct_bases(
        &mut self,
        library: &super::LibraryPlans,
        plan: &SupportedImpliedSpecializations,
        mut steps: Option<&mut usize>,
    ) -> Option<StaticPlannerBases> {
        let floor = library.rows;
        let end = self.explicit_len();
        planning_charge(&mut steps, end - floor)?;
        let mut bases = HashMap::new();
        let mut incomplete = HashSet::new();
        let push = |bases: &mut HashMap<usize, Vec<usize>>,
                    steps: &mut Option<&mut usize>,
                    owner: usize,
                    target: usize| {
            let targets = bases.entry(owner).or_default();
            planning_charge(steps, targets.len().saturating_add(1))?;
            if !targets.contains(&target) {
                targets.push(target);
            }
            Some(())
        };
        for owner in floor..end {
            planning_charge(&mut steps, self.elements[owner].owned_relationships.len())?;
            for k in 0..self.elements[owner].owned_relationships.len() {
                let relationship = self.elements[owner].owned_relationships[k];
                if !conforms(self.elements[relationship].ty, "Specialization") {
                    continue;
                }
                let target = specialization_target(&self.elements[relationship])
                    .and_then(|id| self.element_index_of_uuid(id))
                    .filter(|&target| target < end);
                if let Some(target) = target {
                    push(&mut bases, &mut steps, owner, target)?;
                }
            }
        }
        // A library plan's candidates are its own rows': the build's own
        // plan lists the build's rows'.
        for (&(owner, edge), retained) in plan.candidates.own() {
            if owner < floor {
                continue;
            }
            planning_charge(&mut steps, 1)?;
            if retained {
                match self
                    .element_index_of_uuid(edge.3)
                    .filter(|&target| target < end)
                {
                    Some(target) => push(&mut bases, &mut steps, owner, target)?,
                    // The required base exists only by external identity.
                    // Its unknown member order cannot justify local pairing.
                    None => {
                        incomplete.insert(owner);
                    }
                }
            }
        }
        planning_charge(&mut steps, plan.chain_bases.incomplete.len())?;
        incomplete.extend(
            plan.chain_bases
                .incomplete
                .iter()
                .copied()
                .filter(|&feature| feature >= floor),
        );
        for (&source, &target) in &plan.chain_bases.targets {
            if source >= floor {
                planning_charge(&mut steps, 1)?;
                push(&mut bases, &mut steps, source, target)?;
            }
        }
        Some((bases, incomplete))
    }

    /// Typed metadata from the SAME retained plan used by inheritance and
    /// materialization. This accessor neither adds nor independently eliminates
    /// edges. Per-query adapters resolve and validate each relevant identity.
    pub(super) fn retained_typing_edges(
        &mut self,
        steps: &mut usize,
    ) -> Option<Arc<RetainedTypings>> {
        if self.effective_dynamic_plan().is_some() {
            return self.dynamic_typing_edges(steps);
        }
        // The existing cache-hit charge below covers these constant predicates.
        // Only stale authority needs the charged shared revalidation path.
        if !self.supported_chain_evidence_current() || !self.physical_static_authority_current() {
            self.refresh_supported_chain_evidence(Some(&mut *steps))?;
            self.certify_materialized_static_prefix(steps)?;
        }
        let library_configuration = self.external_implied_names.is_empty();
        let plan = match self
            .supported_implied
            .as_ref()
            .filter(|plan| plan.library_configuration == library_configuration)
        {
            Some(plan) => Arc::clone(plan),
            None => {
                planning_charge(
                    &mut Some(&mut *steps),
                    self.lib_qnames.len() + self.external_implied_names.len(),
                )?;
                let names = self
                    .lib_qnames
                    .iter()
                    .map(|(id, segments)| (segments.join("::"), *id))
                    .chain(
                        self.external_implied_names
                            .iter()
                            .map(|(name, id)| (name.clone(), *id)),
                    )
                    .collect();
                self.supported_implied_specializations_with_budget(
                    &names,
                    library_configuration,
                    Some(&mut *steps),
                )?
            }
        };
        planning_charge(&mut Some(&mut *steps), 1)?;
        if let Some(typing) = plan.typing_by_owner.get() {
            return Some(Arc::clone(typing));
        }
        planning_charge(&mut Some(&mut *steps), plan.candidates.len())?;
        let mut typing = RetainedTypings::new();
        for (&(owner, edge), retained) in plan.candidates.iter() {
            if retained && (conforms(edge.0, "FeatureTyping") || conforms(edge.0, "Subsetting")) {
                typing.entry(owner).or_default().push((edge.0, edge.3));
            }
        }
        let _ = plan.typing_by_owner.set(Arc::new(typing));
        Some(Arc::clone(plan.typing_by_owner.get().unwrap()))
    }

    /// Complete direct bases in the implemented semantic graph, independent
    /// of lookup spelling and source scope. Conjugation replaces specialization
    /// inheritance (KerML Type::supertypes); otherwise include exact owned
    /// specializations, retained library/variation requirements and supported
    /// positional redefinitions. Resolver-only bases are excluded.
    /// Positional planning must already be stabilized by the caller's provider
    /// proof; this reader never starts an unbudgeted global positional walk.
    pub(super) fn value_context_bases(
        &mut self,
        element: usize,
        steps: &mut usize,
    ) -> Option<Vec<usize>> {
        self.semantic_inheritance_bases(element, true, steps)
    }

    /// Stored Type identities, including Types without a textual body scope.
    pub(super) fn semantic_inheritance_bases(
        &mut self,
        element: usize,
        include_implied: bool,
        steps: &mut usize,
    ) -> Option<Vec<usize>> {
        if include_implied
            && (!self.dynamic_evidence_current(element)
                || !self.result_redefinition_evidence_current(element))
        {
            return None;
        }
        let mut budget = Some(steps);
        planning_charge(&mut budget, 1)?;
        if include_implied {
            self.refresh_supported_chain_evidence(budget.as_deref_mut())?;
            self.certify_materialized_static_prefix(budget.as_deref_mut().unwrap())?;
            if !self.static_chain_owner_current(element) {
                return None;
            }
        }
        let owner = self.elements.get(element)?;
        if !conforms(owner.ty, "Type") {
            return None;
        }
        planning_charge(&mut budget, owner.owned_relationships.len())?;
        let relationships = owner.owned_relationships.clone();
        let conjugations: Vec<_> = relationships
            .iter()
            .copied()
            .filter(|&r| {
                self.elements
                    .get(r)
                    .is_some_and(|e| conforms(e.ty, "Conjugation"))
            })
            .collect();
        if self.id_index.is_none() || self.id_index_built_for != self.elements.len() {
            planning_charge(&mut budget, self.elements.len())?;
        }
        if !conjugations.is_empty() {
            if conjugations.len() != 1 {
                return None;
            }
            let relation = self.elements.get(conjugations[0])?;
            if let Some(source) = relation.props.get("conjugatedType") {
                if source.as_reference()? != self.elements[element].id {
                    return None;
                }
            }
            let target = relation.props.get("originalType")?.as_reference()?;
            let target = self.element_index_of_uuid(target)?;
            return conforms(self.elements.get(target)?.ty, "Type").then_some(vec![target]);
        }
        let mut targets = Vec::new();
        for relationship in relationships {
            let relation = self.elements.get(relationship)?;
            if !conforms(relation.ty, "Specialization")
                || (!include_implied
                    && relation.props.get("isImplied").and_then(|v| v.as_bool()) == Some(true))
            {
                continue;
            }
            for key in [
                "specific",
                "subclassifier",
                "typedFeature",
                "subsettingFeature",
                "redefiningFeature",
                "referencingFeature",
                "crossingFeature",
            ] {
                if let Some(source) = relation.props.get(key) {
                    if source.as_reference()? != self.elements[element].id {
                        return None;
                    }
                }
            }
            let target = specialization_target(relation)?;
            let target = self.element_index_of_uuid(target)?;
            if !conforms(self.elements.get(target)?.ty, "Type") {
                return None;
            }
            planning_charge(&mut budget, 1 + targets.len())?;
            if !targets.contains(&target) {
                targets.push(target);
            }
        }
        if !include_implied {
            return Some(targets);
        }
        if let Some(plan) = self.effective_dynamic_plan() {
            if plan.incomplete_bases.contains(&element) {
                return None;
            }
            for &target in plan.direct_bases.get(&element).into_iter().flatten() {
                planning_charge(&mut budget, 1 + targets.len())?;
                if !conforms(self.elements.get(target)?.ty, "Type") {
                    return None;
                }
                if !targets.contains(&target) {
                    targets.push(target);
                }
            }
            // Retain the existing parameter/end owner-completeness guard;
            // an accepted unrelated Invocation does not certify every sequence.
            self.completed_positional_targets(element)?;
            return Some(targets);
        }
        self.refresh_supported_chain_evidence(budget.as_deref_mut())?;
        let library_configuration = self.external_implied_names.is_empty();
        let plan = match self
            .supported_implied
            .as_ref()
            .filter(|plan| plan.library_configuration == library_configuration)
        {
            Some(plan) => Arc::clone(plan),
            None => {
                planning_charge(
                    &mut budget,
                    self.lib_qnames.len() + self.external_implied_names.len(),
                )?;
                let names = self
                    .lib_qnames
                    .iter()
                    .map(|(id, segments)| (segments.join("::"), *id))
                    .chain(
                        self.external_implied_names
                            .iter()
                            .map(|(name, id)| (name.clone(), *id)),
                    )
                    .collect();
                self.supported_implied_specializations_with_budget(
                    &names,
                    library_configuration,
                    budget.as_deref_mut(),
                )?
            }
        };
        for &id in plan.by_owner.get(&element).into_iter().flatten() {
            planning_charge(&mut budget, 1 + targets.len())?;
            let target = self.element_index_of_uuid(id)?;
            if !conforms(self.elements.get(target)?.ty, "Type") {
                return None;
            }
            if !targets.contains(&target) {
                targets.push(target);
            }
        }
        if plan.chain_bases.incomplete.contains(&element) {
            return None;
        }
        if let Some(&target) = plan.chain_bases.targets.get(&element) {
            planning_charge(&mut budget, 1 + targets.len())?;
            if !targets.contains(&target) {
                targets.push(target);
            }
        }
        let positional = self.is_parameter(element)
            || self.elements[element]
                .props
                .get("isEnd")
                .and_then(|v| v.as_bool())
                == Some(true);
        if positional && self.positional_redefinitions.is_none() {
            return None;
        }
        for &target in self.completed_positional_targets(element)? {
            planning_charge(&mut budget, 1 + targets.len())?;
            if !conforms(self.elements.get(target)?.ty, "Type") {
                return None;
            }
            if !targets.contains(&target) {
                targets.push(target);
            }
        }
        Some(targets)
    }

    fn expression_target_names(
        &mut self,
        names: &HashMap<String, Uuid>,
        budget: &mut Option<&mut usize>,
    ) -> Option<HashMap<&'static str, Uuid>> {
        // A canonical name does not disambiguate two loaded rows sharing one
        // UUID. Refuse these roles rather than selecting a last-wins endpoint.
        if !self.literal_identities_unique(budget.as_deref_mut())? {
            return Some(HashMap::new());
        }
        // The general names map is an inversion. Preserve ambiguity before that
        // inversion loses distinct declared identities for a required name.
        planning_charge(budget, self.lib_qnames.len())?;
        let mut loaded: HashMap<&'static str, Option<Uuid>> = HashMap::new();
        for (id, segments) in &self.lib_qnames {
            let composite = match segments.as_slice() {
                [p, t, n] if p == "Occurrences" && t == "Occurrence" && n == "suboccurrences" => {
                    Some("Occurrences::Occurrence::suboccurrences")
                }
                [p, t, n] if p == "Objects" && t == "Object" && n == "subobjects" => {
                    Some("Objects::Object::subobjects")
                }
                [p, t, n] if p == "Items" && t == "Item" && n == "subitems" => {
                    Some("Items::Item::subitems")
                }
                [p, t, n] if p == "Items" && t == "Item" && n == "subparts" => {
                    Some("Items::Item::subparts")
                }
                _ => None,
            };
            let name = if let Some(name) = composite {
                Some(name)
            } else if let [package, member] = segments.as_slice() {
                match (package.as_str(), member.as_str()) {
                    ("Base", "things") => Some(FEATURE_BASE),
                    ("Performances", "performances") => Some(STEP_BASE),
                    (package, member) if binary_role_name(package, member).is_some() => {
                        binary_role_name(package, member)
                    }
                    ("Base", "dataValues") => Some("Base::dataValues"),
                    ("Objects", "objects") => Some("Objects::objects"),
                    ("Occurrences", "occurrences") => Some("Occurrences::occurrences"),
                    ("ControlFunctions", ".") => Some(CHAIN_FUNCTION),
                    ("Constraints", "assertedConstraintChecks") => {
                        Some(assertion_implied_base(false))
                    }
                    ("Constraints", "negatedConstraintChecks") => {
                        Some(assertion_implied_base(true))
                    }
                    ("Requirements", "satisfiedRequirementChecks") => {
                        Some(satisfaction_implied_base(false))
                    }
                    ("Requirements", "notSatisfiedRequirementChecks") => {
                        Some(satisfaction_implied_base(true))
                    }
                    ("Performances", "literalBooleanEvaluations") => {
                        literal_implied_base("LiteralBoolean")
                    }
                    ("Performances", "literalIntegerEvaluations") => {
                        literal_implied_base("LiteralInteger")
                    }
                    ("Performances", "literalRationalEvaluations") => {
                        literal_implied_base("LiteralRational")
                    }
                    ("Performances", "literalStringEvaluations") => {
                        literal_implied_base("LiteralString")
                    }
                    ("Performances", "nullEvaluations") => literal_implied_base("NullExpression"),
                    ("Performances", "metadataAccessEvaluations") => {
                        literal_implied_base("MetadataAccessExpression")
                    }
                    ("Performances", "evaluations") => {
                        expression_implied_base("InvocationExpression")
                    }
                    ("Performances", "constructorEvaluations") => {
                        expression_implied_base("ConstructorExpression")
                    }
                    ("Performances", "booleanEvaluations") => {
                        additional_expression_base("BooleanExpression")
                    }
                    ("Performances", "literalEvaluations") => {
                        additional_expression_base("LiteralExpression")
                    }
                    ("Performances", "trueEvaluations") => Some(invariant_implied_base(false)),
                    ("Performances", "falseEvaluations") => Some(invariant_implied_base(true)),
                    _ => None,
                }
            } else {
                None
            };
            if let Some(name) = name {
                loaded
                    .entry(name)
                    .and_modify(|prior| {
                        if *prior != Some(*id) {
                            *prior = None;
                        }
                    })
                    .or_insert(Some(*id));
            }
        }
        if self.id_index.is_none() || self.id_index_built_for != self.elements.len() {
            planning_charge(budget, self.elements.len())?;
        }
        let mut out = HashMap::new();
        let fixed_names = [
            "LiteralBoolean",
            "LiteralInteger",
            "LiteralRational",
            "LiteralString",
            "NullExpression",
            "MetadataAccessExpression",
            "InvocationExpression",
            "ConstructorExpression",
        ]
        .into_iter()
        .map(|ty| expression_implied_base(ty).expect("supported fixed-base expression kind"));
        for name in fixed_names
            .chain([
                CHAIN_FUNCTION,
                FEATURE_BASE,
                STEP_BASE,
                additional_expression_base("BooleanExpression").unwrap(),
                additional_expression_base("LiteralExpression").unwrap(),
                invariant_implied_base(false),
                invariant_implied_base(true),
                assertion_implied_base(false),
                assertion_implied_base(true),
                satisfaction_implied_base(false),
                satisfaction_implied_base(true),
                "Base::dataValues",
                "Objects::objects",
                "Occurrences::occurrences",
            ])
            .chain(super::type_relations::COMPOSITE_ROLES)
            .chain(BINARY_ROLES.map(|(role, _)| role))
        {
            if loaded.get(name) == Some(&None) {
                continue;
            }
            let Some(&id) = names.get(name) else {
                continue;
            };
            let element = self.element_index_of_uuid(id);
            // Operator, Feature and Step roles need a unique loaded kind witness;
            // external names alone cannot certify their required heritage.
            if (matches!(name, CHAIN_FUNCTION | FEATURE_BASE | STEP_BASE)
                || BINARY_ROLES.iter().any(|(role, _)| *role == name)
                || TYPED_FEATURE_BASES.iter().any(|(_, role)| *role == name)
                || super::type_relations::COMPOSITE_ROLES.contains(&name))
                && element.is_none()
            {
                continue;
            }
            if let Some(element) = element {
                // Supplied external names cannot promote an arbitrary loaded
                // user/library element into a canonical semantic library role.
                if element >= self.lib_boundary
                    || loaded.get(name) != Some(&Some(id))
                    || !conforms(self.elements[element].ty, expression_role_kind(name))
                {
                    continue;
                }
            }
            out.insert(name, id);
        }
        Some(out)
    }

    /// Check the existing UUID projection, including any materialized suffix.
    /// Public identity changes clear that index; appended rows invalidate its
    /// length. No semantic proof is retained here or in a separate cache.
    pub(super) fn literal_identities_unique(
        &mut self,
        mut steps: Option<&mut usize>,
    ) -> Option<bool> {
        planning_charge(&mut steps, 1)?;
        let Some(first) = self.elements.get(0).map(|element| element.id) else {
            return Some(true);
        };
        if self.id_index.is_none() || self.id_index_built_for != self.elements.len() {
            planning_charge(&mut steps, self.elements.len())?;
        }
        self.element_index_of_uuid(first);
        Some(self.id_index.as_ref()?.len() == self.elements.len())
    }

    /// Required target identity from the same retained-plan configuration used
    /// by semantic inheritance. Call after semantic_inheritance_bases has
    /// ensured that plan; no name resolution or model-wide scan occurs here.
    pub(super) fn planned_literal_target(&self, ty: &str) -> Option<Uuid> {
        let name = literal_implied_base(ty)?;
        self.supported_implied
            .as_ref()?
            .expression_targets
            .get(name)
            .copied()
    }

    /// Direct owned specialization targets for positional obligations. This
    /// deliberately excludes name-lookup convenience heritage and standalone
    /// specializations owned elsewhere. Retained implied requirements come from
    /// exactly the same plan used by the materialized relationship view.
    pub(super) fn positional_direct_bases(
        &mut self,
    ) -> (HashMap<usize, Vec<usize>>, HashSet<usize>) {
        self.positional_direct_bases_with_budget(None)
            .expect("unbounded base planning cannot exhaust")
    }

    pub(super) fn positional_direct_bases_with_budget(
        &mut self,
        mut steps: Option<&mut usize>,
    ) -> Option<StaticPlannerBases> {
        // Bounded proof preparation reuses the same retained authority already
        // admitted by the report. Name setters invalidate it before reuse.
        self.refresh_supported_chain_evidence(steps.as_deref_mut())?;
        if self.external_implied_names.is_empty() {
            if let Some(library) = self.library_plans(steps.as_deref_mut())? {
                let plan = self.plan_extending_library(&library, steps.as_deref_mut())?;
                return self.positional_direct_bases_on_library(&library, &plan, steps);
            }
        }
        if steps.is_some() {
            planning_charge(&mut steps, 1)?;
            if let Some(plan) = self
                .supported_implied
                .as_ref()
                .filter(|plan| plan.library_configuration == self.external_implied_names.is_empty())
                .cloned()
            {
                return self.positional_direct_bases_from_plan(&plan, steps);
            }
        }
        planning_charge(
            &mut steps,
            self.lib_qnames
                .len()
                .saturating_add(self.external_implied_names.capacity()),
        )?;
        for (_, segments) in &self.lib_qnames {
            planning_charge(&mut steps, segments.len())?;
            for segment in segments {
                planning_charge(&mut steps, segment.len())?;
            }
        }
        for name in self.external_implied_names.keys() {
            planning_charge(&mut steps, name.len())?;
        }
        let names = self
            .lib_qnames
            .iter()
            .map(|(id, segments)| (segments.join("::"), *id))
            .chain(
                self.external_implied_names
                    .iter()
                    .map(|(name, id)| (name.clone(), *id)),
            )
            .collect();
        let plan = self.supported_implied_specializations_with_budget(
            &names,
            self.external_implied_names.is_empty(),
            steps.as_deref_mut(),
        )?;
        self.positional_direct_bases_from_plan(&plan, steps)
    }

    /// The direct bases `plan` gives: a build that extends its prepared
    /// library's plans extends the library's own with its own rows'.
    fn positional_direct_bases_from_plan(
        &mut self,
        plan: &SupportedImpliedSpecializations,
        mut steps: Option<&mut usize>,
    ) -> Option<StaticPlannerBases> {
        if plan.library_configuration {
            if let Some(library) = self.library_plans(steps.as_deref_mut())? {
                return self.positional_direct_bases_on_library(&library, plan, steps);
            }
        }
        self.positional_direct_bases_from_static_plan(plan, steps)
    }

    /// The implied plan of a build extending `library`'s plans: the current
    /// one, else its own rows' planned over the library's, with the library's
    /// names (the build's own rows add none).
    pub(super) fn plan_extending_library(
        &mut self,
        library: &super::LibraryPlans,
        mut steps: Option<&mut usize>,
    ) -> Option<Arc<SupportedImpliedSpecializations>> {
        self.refresh_supported_chain_evidence(steps.as_deref_mut())?;
        planning_charge(&mut steps, 1)?;
        if let Some(plan) = self
            .supported_implied
            .as_ref()
            .filter(|plan| plan.library_configuration)
        {
            return Some(Arc::clone(plan));
        }
        self.supported_implied_specializations_with_budget(&library.names, true, steps)
    }

    /// The library configuration's names and implied plan of every row,
    /// planned whole, with its shared tables frozen: a prepared library's own
    /// (see [`super::LibraryPlans`]). The plan is taken from this builder.
    pub(super) fn library_rows_implied(
        &mut self,
    ) -> (HashMap<String, Uuid>, Arc<SupportedImpliedSpecializations>) {
        let names = self
            .lib_qnames
            .iter()
            .map(|(id, segments)| (segments.join("::"), *id))
            .collect();
        let plan = self.supported_implied_specializations(&names, true);
        self.supported_implied = None;
        // Held once here; a plan held elsewhere too is shared unfrozen.
        let plan =
            Arc::try_unwrap(plan).map_or_else(|plan| plan, |plan| Arc::new(plan.into_frozen()));
        (names, plan)
    }

    pub(super) fn positional_direct_bases_from_static_plan(
        &self,
        plan: &SupportedImpliedSpecializations,
        mut steps: Option<&mut usize>,
    ) -> Option<StaticPlannerBases> {
        planning_charge(&mut steps, self.explicit_len())?;
        let by_id: HashMap<_, _> = self
            .elements
            .iter()
            .take(self.explicit_len())
            .enumerate()
            .map(|(i, element)| (element.id, i))
            .collect();
        let mut incomplete = HashSet::new();
        let mut bases: HashMap<usize, Vec<usize>> = HashMap::new();
        for (owner, element) in self.elements.iter().take(self.explicit_len()).enumerate() {
            planning_charge(&mut steps, element.owned_relationships.len())?;
            for &relationship in &element.owned_relationships {
                let relation = &self.elements[relationship];
                if conforms(relation.ty, "Specialization") {
                    if let Some(target) =
                        specialization_target(relation).and_then(|id| by_id.get(&id).copied())
                    {
                        let targets = bases.entry(owner).or_default();
                        planning_charge(&mut steps, targets.len().saturating_add(1))?;
                        if !targets.contains(&target) {
                            targets.push(target);
                        }
                    }
                }
            }
        }
        for (&(owner, edge), retained) in plan.candidates.iter() {
            planning_charge(&mut steps, 1)?;
            if retained {
                if let Some(&target) = by_id.get(&edge.3) {
                    let targets = bases.entry(owner).or_default();
                    planning_charge(&mut steps, targets.len().saturating_add(1))?;
                    if !targets.contains(&target) {
                        targets.push(target);
                    }
                } else {
                    // The required base exists only by external identity.
                    // Its unknown member order cannot justify local pairing.
                    incomplete.insert(owner);
                }
            }
        }
        planning_charge(&mut steps, plan.chain_bases.incomplete.len())?;
        incomplete.extend(plan.chain_bases.incomplete.iter().copied());
        for (&source, &target) in &plan.chain_bases.targets {
            planning_charge(&mut steps, 1)?;
            let targets = bases.entry(source).or_default();
            planning_charge(&mut steps, targets.len().saturating_add(1))?;
            if !targets.contains(&target) {
                targets.push(target);
            }
        }
        Some((bases, incomplete))
    }

    /// Owned typing has three independent KerML specialization obligations.
    /// The existential witnesses are exact owned FeatureTyping endpoints, not
    /// inferred type projections. The same candidate minimizer and publisher
    /// retain the required paths. Conditional composition requirements use the
    /// same checked ownership in both graph formats; the unconditional owned
    /// typing requirements remain specific to canonical graphs.
    fn owned_typing_requirements(
        &mut self,
        feature: usize,
        targets: &HashMap<&'static str, Uuid>,
        raw: &super::structural_index::StoredStructure,
        typing: &super::structural_index::StoredTyping,
        budget: &mut Option<&mut usize>,
    ) -> Option<Vec<PlannedEdge>> {
        let Some(required) = self.owned_typing_kinds(feature, raw, typing, budget) else {
            planning_charge(budget, 0)?;
            return Some(Vec::new());
        };
        planning_charge(budget, 1)?;
        let mut requirements = Vec::new();
        if self.elements[feature]
            .props
            .get("isComposite")
            .and_then(|v| v.as_bool())
            == Some(true)
        {
            let mut local = 0;
            let steps = budget.as_deref_mut().unwrap_or(&mut local);
            // Reciprocal ordinary FeatureMemberships supply the owner. Feature
            // owner conditions require positive owned typing witnesses here;
            // checked reads separately certify the complete owner projection.
            if let Some(membership) = self.elements[feature].owning_relationship {
                if self.elements[membership].ty == "FeatureMembership" {
                    if let Some(Some(owner)) =
                        super::semantic_ownership::checked_relationship_carrier(
                            self, raw, membership, steps,
                        )
                    {
                        if super::membership_evidence::member(self, raw, owner, membership, steps)
                            == Some(feature)
                            && matches!(
                                self.elements[owner].ty,
                                "Type"
                                    | "Classifier"
                                    | "Class"
                                    | "Structure"
                                    | "DataType"
                                    | "Definition"
                                    | "AttributeDefinition"
                                    | "OccurrenceDefinition"
                                    | "ItemDefinition"
                                    | "PartDefinition"
                                    | "Feature"
                                    | "OccurrenceUsage"
                                    | "ItemUsage"
                                    | "PartUsage"
                            )
                        {
                            let owner_types = if conforms(self.elements[owner].ty, "Feature") {
                                // A missing witness contributes no guessed owner
                                // type. Metaclass-specific conditions remain
                                // independent of these existential witnesses.
                                let kinds = self
                                    .owned_typing_kinds(owner, raw, typing, budget)
                                    .unwrap_or([false; 3]);
                                planning_charge(budget, 0)?;
                                super::type_relations::CompositionOwner {
                                    object: kinds[0],
                                    occurrence: kinds[1],
                                }
                            } else {
                                super::type_relations::CompositionOwner::default()
                            };
                            for role in super::type_relations::composite_roles(
                                self.elements[feature].ty,
                                self.elements[owner].ty,
                                required[0],
                                required[1],
                                owner_types,
                            ) {
                                if let Some(&target) = targets.get(role) {
                                    requirements.push((
                                        "Subsetting",
                                        "subsettingFeature",
                                        "subsettedFeature",
                                        target,
                                    ));
                                }
                            }
                        }
                    }
                }
            }
            planning_charge(budget, 0)?;
        }
        if self.graph_format != crate::model::GraphFormat::CanonicalV3 {
            return Some(requirements);
        }
        planning_charge(budget, TYPED_FEATURE_BASES.len())?;
        for (needed, (_, role)) in required.into_iter().zip(TYPED_FEATURE_BASES) {
            if needed {
                if let Some(&target) = targets.get(role) {
                    requirements.push((
                        "Subsetting",
                        "subsettingFeature",
                        "subsettedFeature",
                        target,
                    ));
                }
            }
        }
        Some(requirements)
    }

    /// Positive owned-typing witnesses only. Inherited typing requires the
    /// checked reader's complete projection and cannot invent a static edge.
    fn owned_typing_kinds(
        &mut self,
        feature: usize,
        raw: &super::structural_index::StoredStructure,
        typing: &super::structural_index::StoredTyping,
        budget: &mut Option<&mut usize>,
    ) -> Option<[bool; 3]> {
        planning_charge(budget, 1)?;
        if raw.incomplete() || typing.sources_incomplete || raw.bad_bases.contains(&feature) {
            return None;
        }
        let relationships = typing
            .relationships
            .get(&feature)
            .map_or(&[][..], Vec::as_slice);
        let mut required = [false; 3];
        let mut local = 0;
        for &relationship in relationships {
            planning_charge(budget, 1)?;
            // A dynamic suffix cannot become a new input to its immutable
            // static prefix. Generated typings need their own producer proof.
            if relationship >= self.explicit_len()
                || !conforms(self.elements.get(relationship)?.ty, "FeatureTyping")
            {
                continue;
            }
            let steps = budget.as_deref_mut().unwrap_or(&mut local);
            let carrier = super::semantic_ownership::checked_relationship_carrier(
                self,
                raw,
                relationship,
                steps,
            );
            let Some(carrier) = carrier else {
                planning_charge(budget, 0)?;
                return None;
            };
            if carrier != Some(feature) {
                continue;
            }
            let target = super::type_relations::endpoint(
                self,
                feature,
                relationship,
                &["typedFeature", "specific"],
                &["type", "general"],
                "Type",
                steps,
            );
            planning_charge(budget, 0)?;
            let target = target?;
            planning_charge(budget, TYPED_FEATURE_BASES.len())?;
            for (needed, (kind, _)) in required.iter_mut().zip(TYPED_FEATURE_BASES) {
                *needed |= conforms(self.elements[target].ty, kind);
            }
        }
        Some(required)
    }

    pub(super) fn binary_owned_base(&self, owner: usize) -> Option<(&'static str, bool)> {
        let ty = self.elements[owner].ty;
        let role = if conforms(ty, "InterfaceDefinition") {
            ("Interfaces::BinaryInterface", true)
        } else if conforms(ty, "ConnectionDefinition") {
            ("Connections::BinaryConnection", true)
        } else if conforms(ty, "InterfaceUsage") {
            ("Interfaces::binaryInterfaces", false)
        } else if conforms(ty, "ConnectionUsage") {
            ("Connections::binaryConnections", false)
        } else {
            return None;
        };
        (self
            .owned_member_elems(owner, true)
            .into_iter()
            .filter(|&feature| {
                self.elements[feature]
                    .props
                    .get("isEnd")
                    .and_then(|v| v.as_bool())
                    == Some(true)
            })
            .count()
            == 2)
            .then_some(role)
    }

    /// Lookup must use the same canonical loaded binary role as the
    /// specialization planner, never a user declaration or an inverted alias.
    pub(super) fn binary_lookup_target(&mut self, target: usize, role: &str) -> bool {
        if target >= self.lib_boundary
            || !conforms(self.elements[target].ty, expression_role_kind(role))
            || self.literal_identities_unique(None) != Some(true)
        {
            return false;
        }
        let id = self.elements[target].id;
        let mut found = false;
        for (candidate, parts) in &self.lib_qnames {
            if let [package, member] = parts.as_slice() {
                if binary_role_name(package, member) == Some(role) {
                    if *candidate != id {
                        return false;
                    }
                    found = true;
                }
            }
        }
        found
    }

    /// Plan the semantic requirements before minimizing edges. Considering
    /// all requirements together lets an explicit path through another user
    /// element reach that element's required base, independent of source order.
    fn required_implied_plan(
        &self,
        i: usize,
        names: &HashMap<String, Uuid>,
        expression_targets: &HashMap<&'static str, Uuid>,
        rel_owner: &[Option<usize>],
    ) -> Vec<PlannedEdge> {
        let ty = self.elements[i].ty;
        let mut out = Vec::new();
        if let Some(kind) = def_kind_of(ty) {
            for name in implicit_def_bases(kind) {
                if let Some(&id) = names.get(*name) {
                    out.push(("Subclassification", "subclassifier", "superclassifier", id));
                }
            }
        } else if let Some(kind) =
            usage_kind_of(ty, Dialect::Sysml).filter(|_| !matches!(ty, "Flow" | "SuccessionFlow"))
        {
            for name in implicit_usage_bases(kind) {
                if let Some(&id) = names.get(*name) {
                    out.push(("Subsetting", "subsettingFeature", "subsettedFeature", id));
                }
            }
        }
        // Kernel Flow and Succession are not SysML usages. Their syntax
        // kinds overlap in the lifting API, but their semantic bases do not.
        // Flow's more specific base is conditional on owning ends; assigning
        // it to every flow also makes the library's own hierarchy cyclic.
        let owns_end = conforms(ty, "Flow")
            && self.owned_member_elems(i, true).into_iter().any(|feature| {
                self.elements[feature]
                    .props
                    .get("isEnd")
                    .and_then(|v| v.as_bool())
                    == Some(true)
            });
        let mut feature_bases = Vec::new();
        if conforms(ty, "Step") {
            if let Some(&id) = expression_targets.get(STEP_BASE) {
                out.push(("Subsetting", "subsettingFeature", "subsettedFeature", id));
            }
        }
        if conforms(ty, "Flow") {
            feature_bases.push("Transfers::transfers");
            if owns_end {
                feature_bases.push("Transfers::flowTransfers");
            }
        }
        if conforms(ty, "FlowUsage") && owns_end {
            feature_bases.push("Flows::flows");
        }
        if conforms(ty, "SuccessionFlow") {
            feature_bases.push("Transfers::flowTransfersBefore");
        }
        if conforms(ty, "Succession") {
            feature_bases.push("Occurrences::happensBeforeLinks");
        }
        for base in feature_bases {
            if let Some(&id) = names.get(base) {
                out.push(("Subsetting", "subsettingFeature", "subsettedFeature", id));
            }
        }
        if ty == "FeatureChainExpression"
            && self.elements[i]
                .props
                .get("operator")
                .is_none_or(|v| v.as_str() == Some("."))
        {
            if let Some(&id) = expression_targets.get(CHAIN_FUNCTION) {
                out.push(("FeatureTyping", "typedFeature", "type", id));
            }
        }
        if let Some(name) = expression_implied_base(ty) {
            if let Some(&id) = expression_targets.get(name) {
                out.push(("Subsetting", "subsettingFeature", "subsettedFeature", id));
            }
        }
        if let Some(name) = additional_expression_base(ty) {
            if let Some(&id) = expression_targets.get(name) {
                out.push(("Subsetting", "subsettingFeature", "subsettedFeature", id));
            }
        }
        // A narrower canonical role may be unavailable in a partial library.
        // Accumulate the independent Expression requirement before minimizing;
        // an available leaf/Constructor role is not evidence of its ancestry.
        if conforms(ty, "Expression")
            && expression_implied_base(ty) != Some("Performances::evaluations")
        {
            if let Some(&id) = expression_targets.get("Performances::evaluations") {
                out.push(("Subsetting", "subsettingFeature", "subsettedFeature", id));
            }
        }
        if conforms(ty, "Invariant") {
            if let Some(negated) = invariant_negation(&self.elements[i]) {
                if let Some(&id) = expression_targets.get(invariant_implied_base(negated)) {
                    out.push(("Subsetting", "subsettingFeature", "subsettedFeature", id));
                }
                for (kind, name) in [
                    ("AssertConstraintUsage", assertion_implied_base(negated)),
                    (
                        "SatisfyRequirementUsage",
                        satisfaction_implied_base(negated),
                    ),
                ] {
                    if conforms(ty, kind) {
                        if let Some(&id) = expression_targets.get(name) {
                            out.push(("Subsetting", "subsettingFeature", "subsettedFeature", id));
                        }
                    }
                }
            }
        }
        // These SysML rules explicitly count owned ends. The corresponding
        // KerML binary rules count effective ends and need a separate analysis;
        // an owned-end count must not stand in for that inherited cardinality.
        if let Some((base, definition)) = self.binary_owned_base(i) {
            if let Some(&target) = expression_targets.get(base) {
                out.push(if definition {
                    (
                        "Subclassification",
                        "subclassifier",
                        "superclassifier",
                        target,
                    )
                } else {
                    (
                        "Subsetting",
                        "subsettingFeature",
                        "subsettedFeature",
                        target,
                    )
                });
            }
        }
        if let Some(rel) = self.elements[i].owning_relationship {
            if self.elements[rel].ty == "VariantMembership" {
                if let Some(variation) = rel_owner[rel] {
                    let vty = self.elements[variation].ty;
                    let id = self.elements[variation].id;
                    if conforms(vty, "Definition") {
                        out.push(("FeatureTyping", "typedFeature", "type", id));
                    } else if conforms(vty, "Usage") {
                        out.push(("Subsetting", "subsettingFeature", "subsettedFeature", id));
                    }
                }
            }
        }
        // Append the inherited generic obligation independently of narrower
        // roles, then let the shared minimizer preserve only necessary edges.
        if conforms(ty, "Feature") {
            if let Some(&id) = expression_targets.get(FEATURE_BASE) {
                out.push(("Subsetting", "subsettingFeature", "subsettedFeature", id));
            }
        }
        out
    }

    /// Remove a candidate only while another specialization path still
    /// satisfies it. Starting with all candidates and removing sequentially
    /// preserves reachability even in explicit cycles: the last necessary
    /// anchor cannot disappear. Testing every candidate against an independent
    /// hypothetical graph could incorrectly remove every anchor in a cycle.
    fn required_specialization_edges(
        &mut self,
        candidates: &[(usize, PlannedEdge)],
        explicit_len: usize,
        rel_owner: &[Option<usize>],
    ) -> (Vec<bool>, SpecializationGraph) {
        self.required_specialization_edges_with_budget(candidates, explicit_len, rel_owner, None)
            .expect("unbounded implied planning cannot exhaust its budget")
    }

    fn required_specialization_edges_with_budget(
        &mut self,
        candidates: &[(usize, PlannedEdge)],
        explicit_len: usize,
        rel_owner: &[Option<usize>],
        steps: Option<&mut usize>,
    ) -> Option<(Vec<bool>, SpecializationGraph)> {
        self.required_specialization_edges_with_fixed_prefix(
            candidates,
            0,
            explicit_len,
            rel_owner,
            steps,
        )
    }
}

impl ResolvedModel {
    /// Materialize the implied relationships on first demand.
    pub(super) fn ensure_implied(&mut self) {
        let status = self.b.ensure_semantic_graph();
        assert_eq!(
            status,
            super::publication::Status::Ready,
            "materialization demand requires a resolved query model"
        );
        self.sync_semantic_publication();
        self.ensure_by_id();
        self.ensure_rel_owner();
    }

    /// References and IDs can be patched after lazy materialization. Rebuild
    /// only the reachability index; existing implied elements and IDs stay put.
    pub(super) fn refresh_implied_specializations(&mut self) {
        self.b.refresh_materialized_specializations();
    }

    /// Whether `e` reaches `ancestor` through known explicit specializations,
    /// materialized implied library/variation specializations, or semantic
    /// metadata bases. Unlike [`Self::conforms`], this includes library heritage
    /// and lazily materializes the supported implied relationship families.
    /// This is a graph reachability query, not a complete implementation of
    /// KerML Type::specializes: other implied relationship families remain
    /// incomplete, so a negative answer does not establish non-conformance.
    pub fn conforms_with_implied(&mut self, e: ElementRef, ancestor: ElementRef) -> bool {
        self.ensure_implied();
        self.ensure_by_id();
        let mut steps = 0;
        if self
            .b
            .refresh_supported_chain_evidence(Some(&mut steps))
            .is_none()
            || self.b.certify_materialized_static_prefix(&mut steps) != Some(true)
        {
            return false;
        }
        let target = self.b.elements[ancestor.0].id;
        let mut stack = vec![self.b.elements[e.0].id];
        let mut seen = HashSet::new();
        while let Some(at) = stack.pop() {
            if at == target {
                return true;
            }
            if !seen.insert(at) {
                continue;
            }
            stack.extend(
                self.b
                    .implied
                    .as_ref()
                    .unwrap()
                    .specializations
                    .get(&at)
                    .into_iter()
                    .flatten()
                    .copied(),
            );
            if let Some(&element) = self.by_id.get(&at) {
                stack.extend(
                    self.b
                        .semantic_base_targets(element, 0)
                        .into_iter()
                        .map(|e| self.b.elements[e].id),
                );
            }
        }
        false
    }

    /// The implied relationships `e` owns — the library specializations
    /// of its kind (SysML Tables 31/32), a variant's specialization of
    /// its variation, and supported positional redefinitions — as relationship
    /// elements of the model, in emission order. Materialized for the whole
    /// model on first call (see the module documentation). Positional
    /// redefinitions between local elements do not require a loaded library.
    pub fn implied_relationships(&mut self, e: ElementRef) -> Vec<ElementRef> {
        self.ensure_implied();
        self.projected_owned_relationships(e)
            .into_iter()
            .filter(|&relationship| self.is_implied(relationship))
            .collect()
    }

    /// `Element::ownedRelationship` with the implied relationships
    /// included, as the specification lists them: the explicit ones in
    /// declaration order, then the implied ones.
    pub(super) fn d_owned_relationships(&mut self, e: ElementRef) -> Vec<ElementRef> {
        self.ensure_implied();
        self.projected_owned_relationships(e)
    }

    /// Whether `e` is a materialized implied relationship.
    pub fn is_implied(&self, e: ElementRef) -> bool {
        self.b
            .semantic_ownership
            .as_ref()
            .is_some_and(|view| view.contains(e.0))
            && conforms(self.b.elements[e.0].ty, "Relationship")
    }
}

#[cfg(test)]
mod value_context_tests {
    use super::*;
    use crate::model::Model;

    fn model() -> ResolvedModel {
        let mut model = Model::new();
        model.add_library_source(
            "parts.sysml",
            "standard library package Parts { part def Part; part def Alternate; part parts; }",
        );
        model.add_source(
            "user.sysml",
            "part def Base; part def Child :> Base; part def Missing :> absent;",
        );
        assert!(!model.has_errors());
        ResolvedModel::build(&model)
    }

    #[test]
    fn owned_and_retained_implied_targets_use_one_configuration() {
        let mut r = model();
        let base = r.resolve_qualified("Base").unwrap().0;
        let child = r.resolve_qualified("Child").unwrap().0;
        let standard = r.resolve_qualified("Parts::Part").unwrap().0;
        assert_eq!(r.b.value_context_bases(base, &mut 0), Some(vec![standard]));
        assert_eq!(r.b.value_context_bases(child, &mut 0), Some(vec![base]));
        let plan = Arc::clone(r.b.supported_implied.as_ref().unwrap());
        let mut steps = 0;
        assert_eq!(
            r.b.value_context_bases(base, &mut steps),
            Some(vec![standard])
        );
        assert!(
            steps < 20,
            "warm proof should inspect only this owner: {steps}"
        );
        assert!(Arc::ptr_eq(&plan, r.b.supported_implied.as_ref().unwrap()));
        let alternate = r.resolve_qualified("Parts::Alternate").unwrap();
        r.set_library_names(&HashMap::from([(
            r.element_id(alternate).to_string(),
            vec!["Parts".into(), "Part".into()],
        )]));
        assert_eq!(
            r.b.value_context_bases(base, &mut 0),
            Some(vec![alternate.0])
        );
        let external_plan = Arc::clone(r.b.supported_implied.as_ref().unwrap());
        assert_eq!(
            r.b.value_context_bases(base, &mut 0),
            Some(vec![alternate.0])
        );
        assert!(Arc::ptr_eq(
            &external_plan,
            r.b.supported_implied.as_ref().unwrap()
        ));
        r.set_library_names(&HashMap::from([(
            "12340000-0000-4000-8000-000000000004".into(),
            vec!["Parts".into(), "Part".into()],
        )]));
        assert_eq!(r.b.value_context_bases(base, &mut 0), None);
    }

    #[test]
    fn unresolved_targets_and_exhausted_plans_are_not_empty_bases() {
        let mut r = model();
        let missing = r.resolve_qualified("Missing").unwrap().0;
        assert_eq!(r.b.value_context_bases(missing, &mut 0), None);
        let base = r.resolve_qualified("Base").unwrap().0;
        r.b.supported_implied = None;
        let mut exhausted = crate::eval::MAX_STEPS;
        assert_eq!(r.b.value_context_bases(base, &mut exhausted), None);
        assert!(r.b.supported_implied.is_none());
        let names =
            r.b.lib_qnames
                .iter()
                .map(|(id, name)| (name.join("::"), *id))
                .collect();
        let mut budget = crate::eval::MAX_STEPS - 2;
        assert!(
            r.b.supported_implied_specializations_with_budget(&names, true, Some(&mut budget))
                .is_none()
        );
        assert!(
            r.b.supported_implied.is_none(),
            "never cache an interrupted plan"
        );
        assert!(r.b.value_context_bases(base, &mut 0).is_some());
    }

    #[test]
    fn same_name_lookup_convenience_is_not_a_semantic_base() {
        // A parameter's own name is no implied base of its scope (it used
        // to be, reaching a same-named feature); the semantic bases of a
        // parameter nothing redefines by position are none either way when
        // the unconditional Kernel library base is not loaded.
        let mut model = Model::new();
        model.add_source("names.kerml", "feature p; function F { in p; }");
        assert!(!model.has_errors());
        let mut r = ResolvedModel::build(&model);
        let p = r.resolve_qualified("F::p").unwrap().0;
        let scope = *r.b.elem_scope.get(&p).unwrap();
        assert_eq!(
            r.b.scopes[scope].implied_bases,
            [crate::json::lib_qn("Base::things")]
        );
        r.b.ensure_positional_redefinitions();
        assert_eq!(r.b.value_context_bases(p, &mut 0), Some(vec![]));
    }

    #[test]
    fn conjugation_replaces_specializations_and_must_be_unique() {
        let mut model = Model::new();
        model.add_source(
            "conjugation.kerml",
            "classifier A; classifier B; classifier X conjugates A; classifier Y specializes B;",
        );
        assert!(!model.has_errors());
        let mut r = ResolvedModel::build(&model);
        let x = r.resolve_qualified("X").unwrap().0;
        let a = r.resolve_qualified("A").unwrap().0;
        // Exercise Type::supertypes' conjugated branch even when a malformed
        // graph also records a specialization (forbidden by
        // validateSpecificationSpecificNotConjugated).
        let y = r.resolve_qualified("Y").unwrap().0;
        let specialization = *r.b.elements[y]
            .owned_relationships
            .iter()
            .find(|&&rel| conforms(r.b.elements[rel].ty, "Specialization"))
            .unwrap();
        r.b.elements[x].owned_relationships.push(specialization);
        assert_eq!(r.b.value_context_bases(x, &mut 0), Some(vec![a]));
        let relation = *r.b.elements[x]
            .owned_relationships
            .iter()
            .find(|&&rel| conforms(r.b.elements[rel].ty, "Conjugation"))
            .unwrap();
        r.b.elements[x].owned_relationships.push(relation);
        assert_eq!(r.b.value_context_bases(x, &mut 0), None);
        r.b.elements[x].owned_relationships.make_mut().pop();
        r.b.elements[relation]
            .props
            .insert("originalType", serde_json::Value::Null);
        assert_eq!(r.b.value_context_bases(x, &mut 0), None);
    }
}

#[cfg(test)]
mod invocation_static_tests {
    use super::*;
    use crate::{libcache::LibraryCache, model::Model, prepared::PreparedLibrary};
    const LIB: &str = "standard library package Base {classifier Anything; feature things:Anything;} standard library package Occurrences {class Occurrence specializes Base::Anything; feature occurrences:Occurrence subsets Base::things;} standard library package Performances {behavior Performance specializes Occurrences::Occurrence; function Evaluation specializes Performance; step performances:Performance subsets Occurrences::occurrences; expr evaluations:Evaluation subsets performances; expr other:Evaluation subsets performances;}";
    const USER: &str = "function F {return r;} feature decoy:F; feature call=F(); class C;";
    fn models() -> Vec<ResolvedModel> {
        let mut base = Model::new();
        assert!(
            base.add_library_source("evaluation-bases.kerml", LIB)
                .diagnostics
                .is_empty()
        );
        base.record_library_cache();
        ResolvedModel::build(&base);
        let cache =
            LibraryCache::from_bytes(&base.take_recorded_library_cache().unwrap().to_bytes())
                .unwrap();
        let prepared = base.prepare_library().unwrap();
        let decoded =
            Arc::new(PreparedLibrary::from_bytes(&prepared.to_bytes(73).unwrap(), 73).unwrap());
        (0..4)
            .map(|mode| {
                let mut m = Model::new();
                match mode {
                    2 => Arc::clone(&prepared).install(&mut m).unwrap(),
                    3 => Arc::clone(&decoded).install(&mut m).unwrap(),
                    _ => {
                        m.add_library_source("evaluation-bases.kerml", LIB);
                        if mode == 1 {
                            m.set_library_cache(cache.clone());
                        }
                    }
                }
                assert!(
                    m.add_source("invocation-static.kerml", USER)
                        .diagnostics
                        .is_empty()
                );
                ResolvedModel::build(&m)
            })
            .collect()
    }
    fn invocation(r: &ResolvedModel) -> usize {
        r.b.elements
            .iter()
            .position(|e| e.ty == "InvocationExpression")
            .unwrap()
    }
    fn names(r: &ResolvedModel) -> HashMap<String, Uuid> {
        r.b.lib_qnames
            .iter()
            .map(|(id, segments)| (segments.join("::"), *id))
            .collect()
    }
    #[test]
    fn static_evaluation_requirement_replays_and_preserves_legacy_ids() {
        let mut expected = None;
        for mut r in models() {
            let expression = invocation(&r);
            let target = r.resolve_qualified("Performances::evaluations").unwrap();
            let before: Vec<_> = r.user_elements().map(|e| r.element_id(e)).collect();
            let library = names(&r);
            let class = r.resolve_qualified("C").unwrap();
            let legacy = r.b.legacy_implied_plan_with_owners(
                class.0,
                &library,
                &r.b.semantic_relationship_owners(),
            );
            assert!(
                !legacy.is_empty(),
                "legacy Class requirement control must be active"
            );
            let rows = r.implied_relationships(ElementRef(expression));
            let evaluations: Vec<_> = rows
                .iter()
                .filter(|rel| {
                    r.b.elements[rel.0].ty == "Subsetting"
                        && specialization_target(&r.b.elements[rel.0]) == Some(r.element_id(target))
                })
                .copied()
                .collect();
            assert_eq!(evaluations.len(), 1);
            let callee = r.resolve_qualified("F").unwrap();
            let callee_typings: Vec<_> = rows
                .iter()
                .filter(|rel| r.b.elements[rel.0].ty == "FeatureTyping")
                .map(|rel| specialization_target(&r.b.elements[rel.0]))
                .collect();
            assert_eq!(callee_typings, vec![Some(r.element_id(callee))]);
            assert!(
                r.b.planned_literal_target("InvocationExpression").is_none(),
                "generic base must not activate the literal result provider"
            );
            let id = r.element_id(evaluations[0]);
            if let Some(expected) = expected {
                assert_eq!(id, expected);
            } else {
                expected = Some(id);
            }
            let mut checked_legacy = 0;
            for rel in r.implied_relationships(class) {
                let row = &r.b.elements[rel.0];
                if let Some(slot) = legacy
                    .iter()
                    .position(|edge| edge.0 == row.ty && Some(edge.3) == specialization_target(row))
                {
                    checked_legacy += 1;
                    let key = format!("{}/implied{slot}", r.element_id(class));
                    assert_eq!(row.id, Uuid::new_v5(&Uuid::NAMESPACE_OID, key.as_bytes()));
                }
            }
            assert!(checked_legacy > 0);
            assert_eq!(
                before,
                r.user_elements()
                    .map(|e| r.element_id(e))
                    .collect::<Vec<_>>()
            );
        }
    }
    #[test]
    fn unavailable_library_does_not_invent_evaluation_identity() {
        let mut m = Model::new();
        assert!(
            m.add_source("invocation-static.kerml", USER)
                .diagnostics
                .is_empty()
        );
        let mut r = ResolvedModel::build(&m);
        let expression = invocation(&r);
        let callee = r.resolve_qualified("F").unwrap();
        let rows = r.implied_relationships(ElementRef(expression));
        assert_eq!(rows.len(), 1);
        assert_eq!(r.b.elements[rows[0].0].ty, "FeatureTyping");
        assert_eq!(
            specialization_target(&r.b.elements[rows[0].0]),
            Some(r.element_id(callee))
        );
        assert!(r.b.planned_literal_target("InvocationExpression").is_none());
    }
    #[test]
    fn loaded_user_feature_cannot_be_relabelled_as_evaluations() {
        for mut r in models() {
            let expression = invocation(&r);
            let decoy = r.resolve_qualified("decoy").unwrap();
            let fake =
                HashMap::from([("Performances::evaluations".to_owned(), r.element_id(decoy))]);
            let plan = r.b.supported_implied_specializations(&fake, false);
            assert!(
                !plan
                    .candidates
                    .iter()
                    .any(|((owner, _), _)| *owner == expression)
            );
        }
    }
    #[test]
    fn ambiguous_loaded_role_and_duplicate_uuid_cannot_supply_evaluation_base() {
        for duplicate_uuid in [false, true] {
            let mut r = models().remove(0);
            let expression = invocation(&r);
            let target = r.resolve_qualified("Performances::evaluations").unwrap();
            let other = r.resolve_qualified("Performances::other").unwrap();
            if duplicate_uuid {
                r.b.elements[other.0].id = r.element_id(target);
            } else {
                let other_id = r.element_id(other);
                r.b.lib_qnames
                    .push((other_id, vec!["Performances".into(), "evaluations".into()]));
            }
            r.b.id_index = None;
            r.b.supported_implied = None;
            let configuration = names(&r);
            let plan = r.b.supported_implied_specializations(&configuration, true);
            let actual: Vec<_> = plan
                .candidates
                .iter()
                .filter_map(|((owner, edge), _)| (*owner == expression).then_some(edge.3))
                .collect();
            // Losing the Expression role does not remove the independent
            // Step and Feature requirements. Duplicate identity still makes
            // every specialization candidate unusable.
            assert_eq!(
                actual,
                if duplicate_uuid {
                    vec![]
                } else {
                    vec![
                        configuration["Performances::performances"],
                        configuration["Base::things"],
                    ]
                }
            );
        }
    }
}

// Result-family state retained independently of legacy static rows.

/// Lazy state for the new family, separate from legacy implied rows.
/// A work-limited attempt retries only after binding invalidates this state.
/// Attempted is NOT a conformance claim: only view.result(e) proves an admitted
/// subtree. Unknown/malformed/colliding expressions have no positive entry.
#[derive(Clone, Copy, PartialEq, Eq)]
pub(super) enum OwnedResultState {
    Pending,
    Attempted,
    WorkLimited,
}

impl ResolvedModel {
    /// Invalidate only new generated-result handles before binding replay.
    /// Called before the binder captures n or iterates properties. Source and
    /// old generic implied indices remain stable. An empty previous tail is
    /// also reset so newly resolved referents can gain a result.
    pub(super) fn discard_owned_result_tail(&mut self) {
        self.b.discard_semantic_result_tail();
        self.sync_semantic_publication();
    }
    /// A result ownership change can affect semantic readers even when source
    /// rows are untouched. Discard completed proofs rather than reusing an
    /// earlier empty projection. Catalog-only plans are unaffected.
    /// Observation only: never introduces a materialization demand. Current
    /// callers publish outside memo computations; future demand expansion must
    /// also guard in-flight computation results against generation changes.
    pub(crate) fn sync_semantic_publication(&mut self) {
        let current = self.b.publication.revision();
        if self.semantic_publication_seen.same_as(&current) {
            return;
        }
        self.semantic_publication_seen = current;
        self.rel_owner = Default::default();
        self.rel_member.clear();
        self.by_id = Arc::default();
        self.by_id_built_for = usize::MAX;
        self.quantity_index = None;
        self.name_memo.clear();
        self.redefiner_index = None;
        self.import_truncated.clear();
    }

    /// Positive evidence only. Missing, malformed, colliding and work-limited
    /// cases are all incomplete for checked owned-result composition reads.
    pub(super) fn owned_result_projection_ready(&mut self, e: ElementRef) -> bool {
        self.ensure_implied();
        let locally_reciprocal = self.b.semantic_ownership.as_ref().is_some_and(|view| {
            view.matches_suffix(&self.b)
                && view.result(e.0).is_some_and(|result| {
                    view.generated_relationship_owner(result.membership) == Some(e.0)
                        && self
                            .b
                            .elements
                            .get(result.membership)
                            .is_some_and(|membership| {
                                conforms(membership.ty, "ReturnParameterMembership")
                                    && *membership.children == [result.feature]
                            })
                        && self.b.elements.get(result.feature).is_some_and(|feature| {
                            conforms(feature.ty, "Feature")
                                && feature.owning_relationship == Some(result.membership)
                        })
                })
        });
        locally_reciprocal && self.b.literal_identities_unique(None) == Some(true)
    }
}
#[cfg(test)]
mod retained_typing_cache_tests {
    use super::*;
    use crate::model::Model;
    #[test]
    fn retained_typing_metadata_is_lazy_and_failed_attempt_can_retry() {
        let mut model = Model::new();
        assert!(model.add_library_source("typing-lib.kerml", "standard library package Occurrences {class Occurrence;} standard library package Performances {expr evaluations;}").diagnostics.is_empty());
        assert!(
            model
                .add_source("typing-user.kerml", "class C; function F; feature x=F();")
                .diagnostics
                .is_empty()
        );
        let mut r = ResolvedModel::build(&model);
        let names =
            r.b.lib_qnames
                .iter()
                .map(|(id, parts)| (parts.join("::"), *id))
                .collect();
        let plan = r.b.supported_implied_specializations(&names, true);
        assert!(!plan.candidates.is_empty());
        assert!(plan.typing_by_owner.get().is_none());
        let mut exhausted = crate::eval::MAX_STEPS - 1;
        assert!(r.b.retained_typing_edges(&mut exhausted).is_none());
        assert!(plan.typing_by_owner.get().is_none());
        let mut cold = 0;
        let typing = r.b.retained_typing_edges(&mut cold).unwrap();
        assert!(cold > 1);
        let mut warm = 0;
        let again = r.b.retained_typing_edges(&mut warm).unwrap();
        assert!(Arc::ptr_eq(&typing, &again));
        assert_eq!(warm, 1);
        assert!(Arc::ptr_eq(&plan, r.b.supported_implied.as_ref().unwrap()));
    }
}

#[cfg(test)]
mod constructor_static_tests {
    use super::*;
    use crate::{libcache::LibraryCache, model::Model, prepared::PreparedLibrary};
    const LIB: &str = "standard library package Base {classifier Anything; feature things:Anything;} standard library package Occurrences {class Occurrence specializes Base::Anything; feature occurrences:Occurrence subsets Base::things;} standard library package Performances {behavior Performance specializes Occurrences::Occurrence; function Evaluation specializes Performance; step performances:Performance subsets Occurrences::occurrences; expr evaluations:Evaluation subsets performances; expr constructorEvaluations subsets evaluations { return result [1]; } expr other:Evaluation subsets performances;}";
    const USER: &str = "class F {feature item;} feature decoy:F; feature call=new F(); feature nonempty=new F(item=1); class C;";
    fn models() -> Vec<ResolvedModel> {
        let mut base = Model::new();
        assert!(
            base.add_library_source("evaluation-bases.kerml", LIB)
                .diagnostics
                .is_empty()
        );
        base.record_library_cache();
        ResolvedModel::build(&base);
        let cache =
            LibraryCache::from_bytes(&base.take_recorded_library_cache().unwrap().to_bytes())
                .unwrap();
        let prepared = base.prepare_library().unwrap();
        let decoded =
            Arc::new(PreparedLibrary::from_bytes(&prepared.to_bytes(73).unwrap(), 73).unwrap());
        (0..4)
            .map(|mode| {
                let mut m = Model::new();
                match mode {
                    2 => Arc::clone(&prepared).install(&mut m).unwrap(),
                    3 => Arc::clone(&decoded).install(&mut m).unwrap(),
                    _ => {
                        m.add_library_source("evaluation-bases.kerml", LIB);
                        if mode == 1 {
                            m.set_library_cache(cache.clone());
                        }
                    }
                }
                assert!(
                    m.add_source("constructor-static.kerml", USER)
                        .diagnostics
                        .is_empty()
                );
                ResolvedModel::build(&m)
            })
            .collect()
    }
    fn constructor(r: &ResolvedModel) -> usize {
        r.b.elements
            .iter()
            .position(|e| e.ty == "ConstructorExpression")
            .unwrap()
    }
    fn names(r: &ResolvedModel) -> HashMap<String, Uuid> {
        r.b.lib_qnames
            .iter()
            .map(|(id, segments)| (segments.join("::"), *id))
            .collect()
    }
    #[test]
    fn static_evaluation_requirement_replays_and_preserves_legacy_ids() {
        let mut expected = None;
        for mut r in models() {
            let expression = constructor(&r);
            let target = r
                .resolve_qualified("Performances::constructorEvaluations")
                .unwrap();
            let before: Vec<_> = r.user_elements().map(|e| r.element_id(e)).collect();
            let library = names(&r);
            let class = r.resolve_qualified("C").unwrap();
            let legacy = r.b.legacy_implied_plan_with_owners(
                class.0,
                &library,
                &r.b.semantic_relationship_owners(),
            );
            assert!(
                !legacy.is_empty(),
                "legacy Class requirement control must be active"
            );
            let rows = r.implied_relationships(ElementRef(expression));
            let evaluations: Vec<_> = rows
                .iter()
                .filter(|rel| {
                    r.b.elements[rel.0].ty == "Subsetting"
                        && specialization_target(&r.b.elements[rel.0]) == Some(r.element_id(target))
                })
                .copied()
                .collect();
            assert_eq!(evaluations.len(), 1);
            assert!(
                !rows
                    .iter()
                    .any(|rel| r.b.elements[rel.0].ty == "FeatureTyping"),
                "no dynamic callee typing is introduced"
            );
            assert!(
                r.b.planned_literal_target("ConstructorExpression")
                    .is_none(),
                "generic base must not activate the literal result provider"
            );
            assert!(
                r.b.semantic_ownership
                    .as_ref()
                    .unwrap()
                    .result(expression)
                    .is_none()
            );
            assert!(matches!(
                r.model_level_evaluability(ElementRef(expression))
                    .classification,
                crate::json::ModelLevelEvaluability::Unknown(_)
            ));
            let id = r.element_id(evaluations[0]);
            let key = format!(
                "{}/implied/Subsetting/{}",
                r.element_id(ElementRef(expression)),
                r.element_id(target)
            );
            assert_eq!(id, Uuid::new_v5(&Uuid::NAMESPACE_OID, key.as_bytes()));
            if let Some(expected) = expected {
                assert_eq!(id, expected);
            } else {
                expected = Some(id);
            }
            let mut checked_legacy = 0;
            for rel in r.implied_relationships(class) {
                let row = &r.b.elements[rel.0];
                if let Some(slot) = legacy
                    .iter()
                    .position(|edge| edge.0 == row.ty && Some(edge.3) == specialization_target(row))
                {
                    checked_legacy += 1;
                    let key = format!("{}/implied{slot}", r.element_id(class));
                    assert_eq!(row.id, Uuid::new_v5(&Uuid::NAMESPACE_OID, key.as_bytes()));
                }
            }
            assert!(checked_legacy > 0);
            assert_eq!(
                before,
                r.user_elements()
                    .map(|e| r.element_id(e))
                    .collect::<Vec<_>>()
            );
        }
    }
    #[test]
    fn unavailable_library_does_not_invent_evaluation_identity() {
        let mut m = Model::new();
        assert!(
            m.add_source("constructor-static.kerml", USER)
                .diagnostics
                .is_empty()
        );
        let mut r = ResolvedModel::build(&m);
        let expression = constructor(&r);
        assert!(r.implied_relationships(ElementRef(expression)).is_empty());
    }
    #[test]
    fn loaded_user_feature_cannot_be_relabelled_as_evaluations() {
        for mut r in models() {
            let expression = constructor(&r);
            let decoy = r.resolve_qualified("decoy").unwrap();
            let fake = HashMap::from([(
                "Performances::constructorEvaluations".to_owned(),
                r.element_id(decoy),
            )]);
            let plan = r.b.supported_implied_specializations(&fake, false);
            assert!(
                !plan
                    .candidates
                    .iter()
                    .any(|((owner, _), _)| *owner == expression)
            );
        }
    }
    #[test]
    fn ambiguous_loaded_role_and_duplicate_uuid_cannot_supply_evaluation_base() {
        for duplicate_uuid in [false, true] {
            let mut r = models().remove(0);
            let expression = constructor(&r);
            let target = r
                .resolve_qualified("Performances::constructorEvaluations")
                .unwrap();
            let other = r.resolve_qualified("Performances::other").unwrap();
            if duplicate_uuid {
                r.b.elements[other.0].id = r.element_id(target);
            } else {
                let other_id = r.element_id(other);
                r.b.lib_qnames.push((
                    other_id,
                    vec!["Performances".into(), "constructorEvaluations".into()],
                ));
            }
            r.b.id_index = None;
            r.b.supported_implied = None;
            let configuration = names(&r);
            let plan = r.b.supported_implied_specializations(&configuration, true);
            let actual: Vec<_> = plan
                .candidates
                .iter()
                .filter_map(|((owner, edge), _)| (*owner == expression).then_some(edge.3))
                .collect();
            let expected = if duplicate_uuid {
                vec![]
            } else {
                vec![
                    configuration["Performances::performances"],
                    configuration["Performances::evaluations"],
                    configuration["Base::things"],
                ]
            };
            assert_eq!(
                actual, expected,
                "ambiguous narrow role preserves generic ancestry; duplicate UUID refuses all roles"
            );
        }
    }
    #[test]
    fn every_authored_constructor_gets_only_its_static_required_edge() {
        for mut r in models() {
            let constructors: Vec<_> =
                r.b.elements
                    .iter()
                    .enumerate()
                    .filter_map(|(i, e)| (e.ty == "ConstructorExpression").then_some(i))
                    .collect();
            assert_eq!(constructors.len(), 2);
            let target = r
                .resolve_qualified("Performances::constructorEvaluations")
                .unwrap();
            for expression in constructors {
                let original_owned = r.b.elements[expression].owned_relationships.clone();
                let rows = r.implied_relationships(ElementRef(expression));
                assert_eq!(rows.len(), 1, "only the fixed ancestry edge is introduced");
                assert!(matches!(
                    r.model_level_evaluability(ElementRef(expression))
                        .classification,
                    crate::json::ModelLevelEvaluability::Unknown(_)
                ));
                assert!(rows.iter().any(|rel| r.b.elements[rel.0].ty == "Subsetting"
                    && specialization_target(&r.b.elements[rel.0]) == Some(r.element_id(target))));
                assert_eq!(r.b.elements[expression].owned_relationships, original_owned);
                assert!(
                    r.b.semantic_ownership
                        .as_ref()
                        .unwrap()
                        .result(expression)
                        .is_none()
                );
            }
        }
    }
}

#[cfg(test)]
mod expression_static_tests {
    use super::*;
    use crate::{libcache::LibraryCache, model::Model, prepared::PreparedLibrary};

    const LIB: &str = "standard library package Base {classifier Anything; feature things:Anything;} standard library package Occurrences {class Occurrence specializes Base::Anything; feature occurrences:Occurrence subsets Base::things;} standard library package Performances {behavior Performance specializes Occurrences::Occurrence; function Evaluation specializes Performance {return result;} step performances:Performance subsets Occurrences::occurrences; expr evaluations:Evaluation subsets performances; expr literalEvaluations subsets evaluations; expr literalIntegerEvaluations subsets literalEvaluations; expr literalBooleanEvaluations subsets literalEvaluations; expr constructorEvaluations subsets evaluations; expr other:Evaluation subsets performances;}";
    const USER: &str = "class C {feature slot;} feature receiver:C; feature referenced=receiver; feature chained=receiver.slot; feature body={1}; feature plus=1+2; feature indexed=receiver#(1); feature selected=receiver.?{in p; true}; feature collected=receiver.{in p; p}; expr declared; expr already subsets Performances::evaluations; expr indirectly subsets already; expr cycleA subsets cycleB; expr cycleB subsets cycleA; bool boolean; inv true invariant {true} function F {return result;} feature invoked=F(); feature constructed=new C(); feature decoy;";
    const GENERIC: &[&str] = &[
        "Expression",
        "FeatureReferenceExpression",
        "FeatureChainExpression",
        "OperatorExpression",
        "IndexExpression",
        "SelectExpression",
        "CollectExpression",
        "BooleanExpression",
        "Invariant",
        "InvocationExpression",
    ];

    fn models() -> Vec<ResolvedModel> {
        let mut base = Model::new();
        assert!(
            base.add_library_source("evaluation-bases.kerml", LIB)
                .diagnostics
                .is_empty()
        );
        base.record_library_cache();
        ResolvedModel::build(&base);
        let cache =
            LibraryCache::from_bytes(&base.take_recorded_library_cache().unwrap().to_bytes())
                .unwrap();
        let prepared = base.prepare_library().unwrap();
        let decoded =
            Arc::new(PreparedLibrary::from_bytes(&prepared.to_bytes(73).unwrap(), 73).unwrap());
        (0..4)
            .map(|mode| {
                let mut model = Model::new();
                match mode {
                    2 => Arc::clone(&prepared).install(&mut model).unwrap(),
                    3 => Arc::clone(&decoded).install(&mut model).unwrap(),
                    _ => {
                        model.add_library_source("evaluation-bases.kerml", LIB);
                        if mode == 1 {
                            model.set_library_cache(cache.clone());
                        }
                    }
                }
                assert!(
                    model
                        .add_source("expression-static.kerml", USER)
                        .diagnostics
                        .is_empty()
                );
                ResolvedModel::build(&model)
            })
            .collect()
    }
    fn names(r: &ResolvedModel) -> HashMap<String, Uuid> {
        r.b.lib_qnames
            .iter()
            .map(|(id, segments)| (segments.join("::"), *id))
            .collect()
    }

    #[test]
    fn every_parsed_expression_reaches_evaluations_across_replay_and_policy() {
        let mut expected = None;
        for mut r in models() {
            let target = r.resolve_qualified("Performances::evaluations").unwrap();
            let source_ids: Vec<_> = r.user_elements().map(|e| r.element_id(e)).collect();
            let expressions: Vec<_> = r
                .user_elements()
                .filter(|e| conforms(r.element_type(*e), "Expression"))
                .collect();
            for ty in GENERIC {
                assert!(
                    expressions.iter().any(|e| r.element_type(*e) == *ty),
                    "missing fixture {ty}"
                );
                assert!(
                    r.b.planned_literal_target(ty).is_none(),
                    "generic ancestry must not widen leaf result provider: {ty}"
                );
            }
            let configuration = names(&r);
            let class = r.resolve_qualified("C").unwrap();
            let legacy = r.b.legacy_implied_plan_with_owners(
                class.0,
                &configuration,
                &r.b.semantic_relationship_owners(),
            );
            assert!(!legacy.is_empty());
            for policy in [
                super::super::ClosurePolicy::Passthrough,
                super::super::ClosurePolicy::Closure {
                    include_implied: false,
                },
                super::super::ClosurePolicy::Closure {
                    include_implied: true,
                },
            ] {
                r.set_closure_policy(policy);
                let mut ids = Vec::new();
                for &expression in &expressions {
                    assert!(
                        r.conforms_with_implied(expression, target),
                        "{}",
                        r.element_type(expression)
                    );
                    for rel in r.implied_relationships(expression) {
                        let row = &r.b.elements[rel.0];
                        if row.ty == "Subsetting"
                            && specialization_target(row) == Some(r.element_id(target))
                        {
                            let key = format!(
                                "{}/implied/Subsetting/{}",
                                r.element_id(expression),
                                r.element_id(target)
                            );
                            assert_eq!(row.id, Uuid::new_v5(&Uuid::NAMESPACE_OID, key.as_bytes()));
                            ids.push(row.id);
                        }
                    }
                }
                assert!(!ids.is_empty());
                if let Some(expected) = &expected {
                    assert_eq!(&ids, expected);
                } else {
                    expected = Some(ids);
                }
                for rel in r.implied_relationships(class) {
                    let row = &r.b.elements[rel.0];
                    if let Some(slot) = legacy.iter().position(|edge| {
                        edge.0 == row.ty && Some(edge.3) == specialization_target(row)
                    }) {
                        let key = format!("{}/implied{slot}", r.element_id(class));
                        assert_eq!(row.id, Uuid::new_v5(&Uuid::NAMESPACE_OID, key.as_bytes()));
                    }
                }
            }
            assert_eq!(
                source_ids,
                r.user_elements()
                    .map(|e| r.element_id(e))
                    .collect::<Vec<_>>()
            );
        }
    }

    #[test]
    fn existing_paths_and_specific_expression_bases_avoid_redundant_generic_edges() {
        for mut r in models() {
            let target = r.resolve_qualified("Performances::evaluations").unwrap();
            for name in ["already", "indirectly", "Performances::evaluations"] {
                let e = r.resolve_qualified(name).unwrap();
                assert!(r.conforms_with_implied(e, target));
                assert!(
                    !r.implied_relationships(e)
                        .into_iter()
                        .any(|rel| specialization_target(&r.b.elements[rel.0])
                            == Some(r.element_id(target)))
                );
            }
            let cycle_a = r.resolve_qualified("cycleA").unwrap();
            let cycle_b = r.resolve_qualified("cycleB").unwrap();
            assert!(r.conforms_with_implied(cycle_a, target));
            assert!(r.conforms_with_implied(cycle_b, target));
            let cycle_edges = r
                .implied_relationships(cycle_a)
                .into_iter()
                .chain(r.implied_relationships(cycle_b));
            assert_eq!(
                cycle_edges
                    .filter(|rel| specialization_target(&r.b.elements[rel.0])
                        == Some(r.element_id(target)))
                    .count(),
                1,
                "a cycle must retain exactly one generic anchor"
            );
            let specific: Vec<_> = r
                .user_elements()
                .filter(|e| {
                    matches!(
                        r.element_type(*e),
                        "LiteralInteger" | "LiteralBoolean" | "ConstructorExpression"
                    )
                })
                .collect();
            assert!(!specific.is_empty());
            for e in specific {
                let role = match r.element_type(e) {
                    "LiteralInteger" => "Performances::literalIntegerEvaluations",
                    "LiteralBoolean" => "Performances::literalBooleanEvaluations",
                    "ConstructorExpression" => "Performances::constructorEvaluations",
                    _ => unreachable!(),
                };
                let expected = r.resolve_qualified(role).unwrap();
                let edges = r.implied_relationships(e);
                assert_eq!(
                    edges
                        .iter()
                        .filter(|rel| specialization_target(&r.b.elements[rel.0])
                            == Some(r.element_id(expected)))
                        .count(),
                    1
                );
                assert!(
                    !edges
                        .iter()
                        .any(|rel| specialization_target(&r.b.elements[rel.0])
                            == Some(r.element_id(target)))
                );
                assert!(r.conforms_with_implied(e, target));
            }
        }
    }

    #[test]
    fn generic_requirement_refuses_missing_relabelled_ambiguous_or_duplicate_identity_roles() {
        for mode in 0..4 {
            let mut r = models().remove(0);
            let expression = r.resolve_qualified("declared").unwrap();
            let target = r.resolve_qualified("Performances::evaluations").unwrap();
            let other = r.resolve_qualified("Performances::other").unwrap();
            let mut configuration = names(&r);
            match mode {
                0 => {
                    configuration.remove("Performances::evaluations");
                }
                1 => {
                    let decoy = r.resolve_qualified("decoy").unwrap();
                    configuration.insert("Performances::evaluations".into(), r.element_id(decoy));
                }
                2 => {
                    r.b.lib_qnames.push((
                        r.element_id(other),
                        vec!["Performances".into(), "evaluations".into()],
                    ));
                }
                3 => {
                    r.b.elements[other.0].id = r.element_id(target);
                }
                _ => unreachable!(),
            }
            r.b.id_index = None;
            r.b.supported_implied = None;
            let plan = r.b.supported_implied_specializations(&configuration, false);
            let actual: Vec<_> = plan
                .candidates
                .iter()
                .filter_map(|((owner, edge), _)| (*owner == expression.0).then_some(edge.3))
                .collect();
            assert_eq!(
                actual,
                if mode == 3 {
                    vec![]
                } else {
                    vec![
                        configuration["Performances::performances"],
                        configuration["Base::things"],
                    ]
                },
                "bad expression role retains independent Step and Feature ancestry; duplicate UUID refuses all roles: mode {mode}"
            );
        }
        let mut model = Model::new();
        assert!(
            model
                .add_source(
                    "unavailable.kerml",
                    "expr declared; feature f; feature x=f;"
                )
                .diagnostics
                .is_empty()
        );
        let mut r = ResolvedModel::build(&model);
        let declared = r.resolve_qualified("declared").unwrap();
        assert!(r.implied_relationships(declared).is_empty());
    }

    #[test]
    fn step_requirement_checks_its_own_canonical_identity_and_kind() {
        for mode in 0..6 {
            let mut r = models().remove(0);
            let expression = r.resolve_qualified("declared").unwrap();
            let target = r.resolve_qualified(STEP_BASE).unwrap();
            let other = r.resolve_qualified("Performances::other").unwrap();
            let mut configuration = names(&r);
            match mode {
                0 => {
                    configuration.remove(STEP_BASE);
                }
                1 => {
                    let decoy = r.resolve_qualified("decoy").unwrap();
                    configuration.insert(STEP_BASE.into(), r.element_id(decoy));
                }
                2 => {
                    r.b.lib_qnames.push((
                        r.element_id(other),
                        vec!["Performances".into(), "performances".into()],
                    ));
                }
                3 => {
                    r.b.elements[other.0].id = r.element_id(target);
                }
                4 => {
                    r.b.elements[target.0].ty = "Feature";
                }
                5 => {
                    configuration.insert(
                        STEP_BASE.into(),
                        Uuid::new_v5(&Uuid::NAMESPACE_OID, b"unloaded step role"),
                    );
                }
                _ => unreachable!(),
            }
            r.b.id_index = None;
            r.b.supported_implied = None;
            let plan = r.b.supported_implied_specializations(&configuration, false);
            assert!(
                !plan.expression_targets.contains_key(STEP_BASE),
                "mode {mode}"
            );
            let actual: Vec<_> = plan
                .candidates
                .iter()
                .filter_map(|((owner, edge), _)| (*owner == expression.0).then_some(edge.3))
                .collect();
            assert_eq!(
                actual,
                if mode == 3 {
                    vec![]
                } else {
                    vec![
                        configuration["Performances::evaluations"],
                        configuration[FEATURE_BASE],
                    ]
                },
                "invalid Step role cannot suppress independent Expression and Feature roles: mode {mode}"
            );
        }
    }

    #[test]
    fn expression_inheritance_is_metaclass_based_and_does_not_widen_leaf_results() {
        for ty in [
            "Expression",
            "FeatureReferenceExpression",
            "FeatureChainExpression",
            "OperatorExpression",
            "IndexExpression",
            "SelectExpression",
            "CollectExpression",
            "BooleanExpression",
            "Invariant",
            "InstantiationExpression",
            "LiteralExpression",
            "CalculationUsage",
            "ConstraintUsage",
            "AssertConstraintUsage",
        ] {
            assert!(conforms(ty, "Expression"), "test metaclass {ty}");
            assert_eq!(
                expression_implied_base(ty),
                Some("Performances::evaluations"),
                "{ty}"
            );
            assert_eq!(literal_implied_base(ty), None, "{ty}");
        }
        for ty in [
            "Feature",
            "Function",
            "Behavior",
            "Step",
            "Class",
            "FakeExpression",
        ] {
            assert_eq!(expression_implied_base(ty), None, "{ty}");
        }
    }
}

#[cfg(test)]
mod expression_fixed_role_tests {
    use super::*;
    use crate::{libcache::LibraryCache, model::Model, prepared::PreparedLibrary};

    const LIB: &str = "standard library package Performances { function Evaluation {return result;} expr evaluations:Evaluation; expr booleanEvaluations subsets evaluations; expr trueEvaluations subsets booleanEvaluations; expr falseEvaluations subsets booleanEvaluations; expr literalEvaluations subsets evaluations; expr literalIntegerEvaluations subsets literalEvaluations; expr other subsets evaluations; }";
    const USER: &str = "bool condition; inv true positive; inv false negative; feature generic=1; bool direct subsets Performances::booleanEvaluations; bool indirect subsets direct; inv true directPositive subsets Performances::trueEvaluations; inv false directNegative subsets Performances::falseEvaluations; feature decoy;";

    fn models() -> Vec<ResolvedModel> {
        let mut base = Model::new();
        assert!(
            base.add_library_source("fixed-roles.kerml", LIB)
                .diagnostics
                .is_empty()
        );
        base.record_library_cache();
        ResolvedModel::build(&base);
        let cache =
            LibraryCache::from_bytes(&base.take_recorded_library_cache().unwrap().to_bytes())
                .unwrap();
        let prepared = base.prepare_library().unwrap();
        let decoded =
            Arc::new(PreparedLibrary::from_bytes(&prepared.to_bytes(79).unwrap(), 79).unwrap());
        (0..4)
            .map(|mode| {
                let mut model = Model::new();
                match mode {
                    2 => Arc::clone(&prepared).install(&mut model).unwrap(),
                    3 => Arc::clone(&decoded).install(&mut model).unwrap(),
                    _ => {
                        model.add_library_source("fixed-roles.kerml", LIB);
                        if mode == 1 {
                            model.set_library_cache(cache.clone());
                        }
                    }
                }
                let parsed = model.add_source("fixed-roles-user.kerml", USER);
                assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
                ResolvedModel::build(&model)
            })
            .collect()
    }
    fn names(r: &ResolvedModel) -> HashMap<String, Uuid> {
        r.b.lib_qnames
            .iter()
            .map(|(id, segments)| (segments.join("::"), *id))
            .collect()
    }
    fn retained_targets(plan: &SupportedImpliedSpecializations, owner: usize) -> Vec<Uuid> {
        plan.candidates
            .iter()
            .filter_map(|((at, edge), retained)| (*at == owner && retained).then_some(edge.3))
            .collect()
    }
    fn generic_literal(r: &mut ResolvedModel) -> ElementRef {
        let i =
            r.b.elements
                .iter()
                .enumerate()
                .skip(r.b.lib_boundary)
                .find(|(_, e)| e.ty == "LiteralInteger")
                .unwrap()
                .0;
        // Generic LiteralExpression has no dedicated textual production. Use
        // a model-level fixture to exercise its inherited static obligation.
        r.b.elements[i].ty = "LiteralExpression";
        let kept = r.b.elements[i].props.to_json();
        r.b.elements[i].props = crate::properties::Properties::new();
        for (key, value) in kept {
            if key != "value" {
                r.b.elements[i].props.insert(&key, value);
            }
        }
        r.b.supported_implied = None;
        ElementRef(i)
    }

    #[test]
    fn inherited_fixed_roles_replay_minimize_and_preserve_source_identities() {
        let mut expected = None;
        for mut r in models() {
            let literal = generic_literal(&mut r);
            let before: Vec<_> = r.user_elements().map(|e| r.element_id(e)).collect();
            let generic = r.resolve_qualified("Performances::evaluations").unwrap();
            let boolean = r
                .resolve_qualified("Performances::booleanEvaluations")
                .unwrap();
            let mut cases = Vec::new();
            for (name, role) in [
                ("condition", "Performances::booleanEvaluations"),
                ("positive", "Performances::trueEvaluations"),
                ("negative", "Performances::falseEvaluations"),
            ] {
                cases.push((
                    r.resolve_qualified(name).unwrap(),
                    r.resolve_qualified(role).unwrap(),
                ));
            }
            cases.push((
                literal,
                r.resolve_qualified("Performances::literalEvaluations")
                    .unwrap(),
            ));
            for policy in [
                super::super::ClosurePolicy::Passthrough,
                super::super::ClosurePolicy::Closure {
                    include_implied: false,
                },
                super::super::ClosurePolicy::Closure {
                    include_implied: true,
                },
            ] {
                r.set_closure_policy(policy);
                let mut ids = Vec::new();
                for &(owner, role) in &cases {
                    assert!(r.conforms_with_implied(owner, role));
                    assert!(r.conforms_with_implied(owner, generic));
                    if owner != literal {
                        assert!(r.conforms_with_implied(owner, boolean));
                    }
                    let rows = r.implied_relationships(owner);
                    assert_eq!(rows.len(), 1, "{}", r.element_type(owner));
                    assert_eq!(
                        specialization_target(&r.b.elements[rows[0].0]),
                        Some(r.element_id(role))
                    );
                    let key = format!(
                        "{}/implied/Subsetting/{}",
                        r.element_id(owner),
                        r.element_id(role)
                    );
                    assert_eq!(
                        r.element_id(rows[0]),
                        Uuid::new_v5(&Uuid::NAMESPACE_OID, key.as_bytes())
                    );
                    assert!(r.b.planned_literal_target(r.element_type(owner)).is_none());
                    ids.push(r.element_id(rows[0]));
                }
                for name in ["direct", "indirect", "directPositive", "directNegative"] {
                    let owner = r.resolve_qualified(name).unwrap();
                    assert!(r.conforms_with_implied(owner, generic));
                    assert!(
                        r.implied_relationships(owner).is_empty(),
                        "redundant edge on {name}"
                    );
                }
                if let Some(expected) = &expected {
                    assert_eq!(&ids, expected);
                } else {
                    expected = Some(ids);
                }
            }
            assert_eq!(
                before,
                r.user_elements()
                    .map(|e| r.element_id(e))
                    .collect::<Vec<_>>()
            );
        }
    }

    #[test]
    fn invariant_default_is_only_for_absence_and_invalid_flags_do_not_choose_a_branch() {
        for ty in [
            "Invariant",
            "AssertConstraintUsage",
            "SatisfyRequirementUsage",
        ] {
            let (_, effective) = crate::semantic_catalog::property(ty, "isNegated").unwrap();
            let spec = effective.unwrap();
            assert_eq!(spec.default_json, Some("false"));
            assert_eq!(
                (spec.target, spec.lower, spec.upper, spec.derived),
                ("Boolean", 1, Some(1), false)
            );
        }
        let variants = [
            None,
            Some(json!(false)),
            Some(json!(true)),
            Some(json!(null)),
            Some(json!("false")),
            Some(json!(0)),
            Some(json!([])),
            Some(json!({})),
        ];
        for (i, value) in variants.into_iter().enumerate() {
            let mut r = models().remove(0);
            let owner = r.resolve_qualified("positive").unwrap();
            let boolean = r
                .resolve_qualified("Performances::booleanEvaluations")
                .unwrap();
            let yes = r
                .resolve_qualified("Performances::trueEvaluations")
                .unwrap();
            let no = r
                .resolve_qualified("Performances::falseEvaluations")
                .unwrap();
            let kept = r.b.elements[owner.0].props.to_json();
            r.b.elements[owner.0].props = crate::properties::Properties::new();
            for (key, value) in kept {
                if key != "isNegated" {
                    r.b.elements[owner.0].props.insert(&key, value);
                }
            }
            if let Some(value) = value {
                r.b.elements[owner.0].props.insert("isNegated", value);
            }
            r.b.supported_implied = None;
            let plan = r.b.supported_implied_specializations(&names(&r), true);
            let wanted = match i {
                0 | 1 => r.element_id(yes),
                2 => r.element_id(no),
                _ => r.element_id(boolean),
            };
            assert_eq!(
                retained_targets(&plan, owner.0),
                vec![wanted],
                "flag case {i}"
            );
            if i >= 3 {
                assert!(!plan.candidates.iter().any(|((at, edge), _)| *at == owner.0
                    && [r.element_id(yes), r.element_id(no)].contains(&edge.3)));
            }
        }
        // A similarly named flag on a BooleanExpression is not an Invariant.
        let mut r = models().remove(0);
        let owner = r.resolve_qualified("condition").unwrap();
        let boolean = r
            .resolve_qualified("Performances::booleanEvaluations")
            .unwrap();
        r.b.elements[owner.0].props.insert("isNegated", json!(true));
        r.b.supported_implied = None;
        let plan = r.b.supported_implied_specializations(&names(&r), true);
        assert_eq!(
            retained_targets(&plan, owner.0),
            vec![r.element_id(boolean)]
        );
    }

    #[test]
    fn unavailable_narrower_roles_keep_independently_proven_general_obligations() {
        for (owner_name, role, parent) in [
            (
                "condition",
                "Performances::booleanEvaluations",
                "Performances::evaluations",
            ),
            (
                "positive",
                "Performances::trueEvaluations",
                "Performances::booleanEvaluations",
            ),
            (
                "negative",
                "Performances::falseEvaluations",
                "Performances::booleanEvaluations",
            ),
            (
                "literal",
                "Performances::literalEvaluations",
                "Performances::evaluations",
            ),
        ] {
            for problem in 0..6 {
                let mut r = models().remove(0);
                let owner = if owner_name == "literal" {
                    generic_literal(&mut r)
                } else {
                    r.resolve_qualified(owner_name).unwrap()
                };
                let target = r.resolve_qualified(role).unwrap();
                let parent = r.resolve_qualified(parent).unwrap();
                let mut configuration = names(&r);
                match problem {
                    0 => {
                        configuration.remove(role);
                    }
                    1 => {
                        let decoy = r.resolve_qualified("decoy").unwrap();
                        configuration.insert(role.into(), r.element_id(decoy));
                    }
                    2 => {
                        let other = r.resolve_qualified("Performances::other").unwrap();
                        r.b.lib_qnames.push((
                            r.element_id(other),
                            role.split("::").map(str::to_owned).collect(),
                        ));
                    }
                    3 => {
                        r.b.elements[target.0].ty = "Class";
                    }
                    4 => r.b.elements[target.0].ty = "Feature",
                    5 => r.b.elements[target.0].ty = "Step",
                    _ => unreachable!(),
                }
                r.b.id_index = None;
                r.b.supported_implied = None;
                let plan = r.b.supported_implied_specializations(&configuration, false);
                assert_eq!(
                    retained_targets(&plan, owner.0),
                    vec![r.element_id(parent)],
                    "{role}, bad role {problem}"
                );
                assert!(
                    !plan
                        .candidates
                        .iter()
                        .any(|((at, edge), _)| *at == owner.0 && edge.3 == r.element_id(target)),
                    "untrusted narrower role survived"
                );
            }
        }
    }

    #[test]
    fn duplicate_loaded_uuid_refuses_roles_and_exact_leaf_policy_is_unchanged() {
        let mut r = models().remove(0);
        let owner = r.resolve_qualified("condition").unwrap();
        let target = r
            .resolve_qualified("Performances::booleanEvaluations")
            .unwrap();
        let other = r.resolve_qualified("Performances::other").unwrap();
        r.b.elements[other.0].id = r.element_id(target);
        r.b.id_index = None;
        r.b.supported_implied = None;
        let plan = r.b.supported_implied_specializations(&names(&r), true);
        assert!(!plan.candidates.iter().any(|((at, _), _)| *at == owner.0));
        for ty in [
            "LiteralBoolean",
            "LiteralInteger",
            "LiteralInfinity",
            "LiteralRational",
            "LiteralString",
            "NullExpression",
            "MetadataAccessExpression",
            "ConstructorExpression",
        ] {
            assert_eq!(
                additional_expression_base(ty),
                conforms(ty, "LiteralExpression").then_some("Performances::literalEvaluations"),
                "inherited literal role: {ty}"
            );
            assert_eq!(
                literal_implied_base(ty).is_some(),
                ty != "ConstructorExpression",
                "exact leaf result-provider boundary: {ty}"
            );
        }
        for ty in [
            "BooleanExpression",
            "Invariant",
            "ConstraintUsage",
            "AssertConstraintUsage",
            "RequirementUsage",
            "SatisfyRequirementUsage",
        ] {
            assert_eq!(
                additional_expression_base(ty),
                Some("Performances::booleanEvaluations")
            );
            assert!(literal_implied_base(ty).is_none());
        }
    }
}

#[cfg(test)]
mod sysml_assertion_role_tests {
    use super::*;
    use crate::model::Model;
    const KERNEL: &str = "standard library package Performances { expr evaluations; expr booleanEvaluations subsets evaluations; expr trueEvaluations subsets booleanEvaluations; expr falseEvaluations subsets booleanEvaluations; }";
    const SYSTEMS: &str = "standard library package Constraints { constraint constraintChecks :> Performances::booleanEvaluations; constraint assertedConstraintChecks :> constraintChecks, Performances::trueEvaluations; constraint negatedConstraintChecks :> constraintChecks, Performances::falseEvaluations; constraint other; } standard library package Requirements { requirement requirementChecks :> Constraints::constraintChecks; requirement satisfiedRequirementChecks :> requirementChecks, Constraints::assertedConstraintChecks; requirement notSatisfiedRequirementChecks :> requirementChecks, Constraints::negatedConstraintChecks; requirement other; }";
    const USER: &str = "constraint plain; requirement ordinary; assert constraint yes; assert not constraint no; satisfy requirement sat; not satisfy requirement unsat; assert constraint direct :> Constraints::assertedConstraintChecks; assert constraint indirect :> direct; satisfy requirement directSat :> Requirements::satisfiedRequirementChecks; satisfy requirement indirectSat :> directSat; attribute decoy;";
    fn model() -> ResolvedModel {
        let mut m = Model::new();
        for (path, source, library) in [
            ("assert-kernel.kerml", KERNEL, true),
            ("assert-systems.sysml", SYSTEMS, true),
            ("assert-user.sysml", USER, false),
        ] {
            let p = if library {
                m.add_library_source(path, source)
            } else {
                m.add_source(path, source)
            };
            assert!(p.diagnostics.is_empty(), "{:?}", p.diagnostics);
        }
        ResolvedModel::build(&m)
    }
    fn names(r: &ResolvedModel) -> HashMap<String, Uuid> {
        r.b.lib_qnames
            .iter()
            .map(|(id, segs)| (segs.join("::"), *id))
            .collect()
    }
    fn candidates(plan: &SupportedImpliedSpecializations, owner: usize) -> Vec<Uuid> {
        plan.candidates
            .iter()
            .filter_map(|((at, edge), _)| (*at == owner).then_some(edge.3))
            .collect()
    }
    fn retained(plan: &SupportedImpliedSpecializations, owner: usize) -> Vec<Uuid> {
        plan.candidates
            .iter()
            .filter_map(|((at, edge), retained)| (*at == owner && retained).then_some(edge.3))
            .collect()
    }
    #[test]
    fn assertions_and_satisfaction_accumulate_then_minimize_and_keep_legacy_ids() {
        let mut r = model();
        let config = names(&r);
        let ids: Vec<_> = r.user_elements().map(|e| r.element_id(e)).collect();
        let mut cases = Vec::new();
        for (owner, role, assert_role) in [
            ("yes", assertion_implied_base(false), None),
            ("no", assertion_implied_base(true), None),
            (
                "sat",
                satisfaction_implied_base(false),
                Some(assertion_implied_base(false)),
            ),
            (
                "unsat",
                satisfaction_implied_base(true),
                Some(assertion_implied_base(true)),
            ),
        ] {
            let owner = r.resolve_qualified(owner).unwrap();
            let role = r.resolve_qualified(role).unwrap();
            let legacy = r.b.legacy_implied_plan_with_owners(
                owner.0,
                &config,
                &r.b.semantic_relationship_owners(),
            );
            cases.push((owner, role, assert_role, legacy));
        }
        let plan = r.b.supported_implied_specializations(&config, true);
        for (owner, role, inherited, _) in &cases {
            assert_eq!(retained(&plan, owner.0), vec![r.element_id(*role)]);
            if let Some(inherited) = inherited {
                let parent = r.resolve_qualified(inherited).unwrap();
                assert!(
                    candidates(&plan, owner.0).contains(&r.element_id(parent)),
                    "Satisfy must independently inherit Assert"
                );
            }
        }
        let plain = r.resolve_qualified("plain").unwrap();
        let old = r.b.legacy_implied_plan_with_owners(
            plain.0,
            &config,
            &r.b.semantic_relationship_owners(),
        );
        assert!(!old.is_empty());
        let mut expected = None;
        for policy in [
            super::super::ClosurePolicy::Passthrough,
            super::super::ClosurePolicy::Closure {
                include_implied: false,
            },
            super::super::ClosurePolicy::Closure {
                include_implied: true,
            },
        ] {
            r.set_closure_policy(policy);
            let mut edges = Vec::new();
            for (owner, role, _, _) in &cases {
                assert!(r.conforms_with_implied(*owner, *role));
                for base in [
                    "Constraints::constraintChecks",
                    "Performances::booleanEvaluations",
                    "Performances::evaluations",
                ] {
                    let base = r.resolve_qualified(base).unwrap();
                    assert!(r.conforms_with_implied(*owner, base));
                }
                let rows = r.implied_relationships(*owner);
                assert_eq!(rows.len(), 1);
                let key = format!(
                    "{}/implied/Subsetting/{}",
                    r.element_id(*owner),
                    r.element_id(*role)
                );
                assert_eq!(
                    r.element_id(rows[0]),
                    Uuid::new_v5(&Uuid::NAMESPACE_OID, key.as_bytes())
                );
                assert!(r.b.planned_literal_target(r.element_type(*owner)).is_none());
                edges.push(r.element_id(rows[0]));
            }
            for row in r.implied_relationships(plain) {
                let target = specialization_target(&r.b.elements[row.0]).unwrap();
                let slot = old
                    .iter()
                    .position(|edge| edge.3 == target)
                    .expect("surviving legacy role");
                let key = format!("{}/implied{slot}", r.element_id(plain));
                assert_eq!(
                    r.element_id(row),
                    Uuid::new_v5(&Uuid::NAMESPACE_OID, key.as_bytes())
                );
                edges.push(r.element_id(row));
            }
            for name in ["direct", "indirect", "directSat", "indirectSat"] {
                let owner = r.resolve_qualified(name).unwrap();
                assert!(
                    r.implied_relationships(owner).is_empty(),
                    "redundant {name}"
                );
            }
            if let Some(expected) = &expected {
                assert_eq!(&edges, expected)
            } else {
                expected = Some(edges)
            }
        }
        assert_eq!(
            ids,
            r.user_elements()
                .map(|e| r.element_id(e))
                .collect::<Vec<_>>()
        );
    }
    #[test]
    fn missing_or_untrusted_narrow_roles_do_not_erase_broader_candidates() {
        for (owner_name, narrow, broader) in [
            (
                "yes",
                assertion_implied_base(false),
                invariant_implied_base(false),
            ),
            (
                "no",
                assertion_implied_base(true),
                invariant_implied_base(true),
            ),
            (
                "sat",
                satisfaction_implied_base(false),
                assertion_implied_base(false),
            ),
            (
                "unsat",
                satisfaction_implied_base(true),
                assertion_implied_base(true),
            ),
            (
                "sat",
                assertion_implied_base(false),
                satisfaction_implied_base(false),
            ),
            (
                "unsat",
                assertion_implied_base(true),
                satisfaction_implied_base(true),
            ),
        ] {
            for problem in 0..5 {
                let mut r = model();
                let owner = r.resolve_qualified(owner_name).unwrap();
                let target = r.resolve_qualified(narrow).unwrap();
                let broader = r.resolve_qualified(broader).unwrap();
                let mut config = names(&r);
                match problem {
                    0 => {
                        config.remove(narrow);
                    }
                    1 => {
                        let decoy = r.resolve_qualified("decoy").unwrap();
                        config.insert(narrow.into(), r.element_id(decoy));
                    }
                    2 => {
                        let decoy = r.resolve_qualified("Constraints::other").unwrap();
                        r.b.lib_qnames.push((
                            r.element_id(decoy),
                            narrow.split("::").map(str::to_owned).collect(),
                        ));
                    }
                    3 => {
                        r.b.elements[target.0].ty = "Feature";
                    }
                    4 => {
                        r.b.elements[target.0].ty = "Class";
                    }
                    _ => unreachable!(),
                }
                r.b.id_index = None;
                r.b.supported_implied = None;
                let plan = r.b.supported_implied_specializations(&config, false);
                let candidates = candidates(&plan, owner.0);
                assert!(
                    !candidates.contains(&r.element_id(target)),
                    "{narrow}, {problem}"
                );
                assert!(
                    candidates.contains(&r.element_id(broader)),
                    "broader role lost: {owner_name}, {problem}"
                );
                assert!(!retained(&plan, owner.0).is_empty());
            }
        }
    }
    #[test]
    fn negation_default_requires_absence_and_malformed_retained_values_select_no_conditional_role()
    {
        for owner_name in ["yes", "sat"] {
            for value in [
                None,
                Some(json!(false)),
                Some(json!(true)),
                Some(json!(null)),
                Some(json!("false")),
                Some(json!(0)),
                Some(json!([])),
                Some(json!({})),
            ] {
                let mut r = model();
                let owner = r.resolve_qualified(owner_name).unwrap();
                let kept = r.b.elements[owner.0].props.to_json();
                r.b.elements[owner.0].props = crate::properties::Properties::new();
                for (key, value) in kept {
                    if key != "isNegated" {
                        r.b.elements[owner.0].props.insert(&key, value);
                    }
                }
                if let Some(value) = &value {
                    r.b.elements[owner.0]
                        .props
                        .insert("isNegated", value.clone());
                }
                r.b.supported_implied = None;
                let plan = r.b.supported_implied_specializations(&names(&r), true);
                let candidates = candidates(&plan, owner.0);
                let expected = match &value {
                    None => Some(false),
                    Some(value) => value.as_bool(),
                };
                for flag in [false, true] {
                    for role in [
                        invariant_implied_base(flag),
                        assertion_implied_base(flag),
                        satisfaction_implied_base(flag),
                    ] {
                        let role = r.resolve_qualified(role).unwrap();
                        let applicable = expected == Some(flag)
                            && (owner_name == "sat"
                                || !r.element_type(role).eq("RequirementUsage"));
                        assert_eq!(
                            candidates.contains(&r.element_id(role)),
                            applicable,
                            "{owner_name} {value:?} {}",
                            r.element_qualified_name(role).unwrap_or_default()
                        );
                    }
                }
                let boolean = r
                    .resolve_qualified("Performances::booleanEvaluations")
                    .unwrap();
                assert!(candidates.contains(&r.element_id(boolean)));
            }
        }
        let mut r = model();
        let owner = r.resolve_qualified("plain").unwrap();
        r.b.elements[owner.0].props.insert("isNegated", json!(true));
        r.b.supported_implied = None;
        let plan = r.b.supported_implied_specializations(&names(&r), true);
        let c = candidates(&plan, owner.0);
        for role in [
            assertion_implied_base(true),
            satisfaction_implied_base(true),
        ] {
            let role = r.resolve_qualified(role).unwrap();
            assert!(!c.contains(&r.element_id(role)));
        }
    }
    #[test]
    fn duplicate_loaded_identity_refuses_new_conditional_roles() {
        let mut r = model();
        let owner = r.resolve_qualified("sat").unwrap();
        let target = r
            .resolve_qualified(satisfaction_implied_base(false))
            .unwrap();
        let other = r.resolve_qualified("Requirements::other").unwrap();
        r.b.elements[other.0].id = r.element_id(target);
        r.b.id_index = None;
        r.b.supported_implied = None;
        let plan = r.b.supported_implied_specializations(&names(&r), true);
        for role in [
            assertion_implied_base(false),
            satisfaction_implied_base(false),
        ] {
            assert!(!plan.expression_targets.contains_key(role));
        }
        assert!(!candidates(&plan, owner.0).contains(&r.element_id(target)));
    }
}

#[cfg(test)]
mod performances_role_kind_tests {
    use super::*;
    use crate::model::Model;

    const ROLES: &[&str] = &[
        "evaluations",
        "constructorEvaluations",
        "booleanEvaluations",
        "trueEvaluations",
        "falseEvaluations",
        "metadataAccessEvaluations",
        "literalEvaluations",
        "literalBooleanEvaluations",
        "literalIntegerEvaluations",
        "literalRationalEvaluations",
        "literalStringEvaluations",
        "nullEvaluations",
    ];

    #[test]
    fn each_loaded_performances_role_requires_expression_ancestry_independently() {
        for declaration in ["expr", "bool", "feature", "step"] {
            for &changed in ROLES {
                let declarations = ROLES
                    .iter()
                    .map(|&role| {
                        format!(
                            "{} {role};",
                            if role == changed { declaration } else { "expr" }
                        )
                    })
                    .collect::<Vec<_>>()
                    .join(" ");
                let mut model = Model::new();
                let source = format!("standard library package Performances {{{declarations}}}");
                assert!(
                    model
                        .add_library_source("role-kinds.kerml", &source)
                        .diagnostics
                        .is_empty()
                );
                let mut r = ResolvedModel::build(&model);
                let names: HashMap<_, _> =
                    r.b.lib_qnames
                        .iter()
                        .map(|(id, path)| (path.join("::"), *id))
                        .collect();
                let admitted = r.b.expression_target_names(&names, &mut None).unwrap();
                for &role in ROLES {
                    let name = format!("Performances::{role}");
                    let expected = role != changed || matches!(declaration, "expr" | "bool");
                    assert_eq!(
                        admitted.contains_key(name.as_str()),
                        expected,
                        "{declaration} {changed}: {role}"
                    );
                    if expected {
                        assert_eq!(admitted[name.as_str()], names[&name]);
                    }
                }
            }
        }
    }
}

// Sole publisher. Existing ResolvedModel demand sites delegate here; ordinary
// Builder retained-evidence queries do not become publication demands.
impl Builder {
    pub(super) fn ensure_semantic_graph(&mut self) -> super::publication::Status {
        let _guard = match self.publication.begin(self.semantic_ready) {
            Ok(guard) => guard,
            Err(status) => return status,
        };
        self.materialize_semantic_graph();
        super::publication::Status::Ready
    }

    fn semantic_relationship_owners(&self) -> Vec<Option<usize>> {
        let mut owners = self.specialization_relation_owners();
        if let Some(view) = &self.semantic_ownership {
            for (relationship, owner) in view.relationship_owners() {
                owners[relationship] = Some(owner);
            }
        }
        owners
    }
    fn invalidate_semantic_indexes(&mut self) {
        self.reset_lookup_caches();
        self.recorded_lookup_prefix = None;
        self.parameter_sites = None;
        self.semantic_memo = Default::default();
        self.stored_structure = None;
    }
    fn materialize_semantic_graph(&mut self) {
        if self.implied.is_some() {
            self.materialize_owned_results(None);
            return;
        }
        let owners = self.semantic_relationship_owners();
        let from = self.elements.len();
        let lib_by_name: HashMap<String, Uuid> = self
            .lib_qnames
            .iter()
            .map(|(id, segments)| (segments.join("::"), *id))
            .chain(
                self.external_implied_names
                    .iter()
                    .map(|(name, id)| (name.clone(), *id)),
            )
            .collect();
        let mut ownership = super::semantic_ownership::SemanticOwnership::new(from);
        // Capture a newly computed positional authority together with the
        // recipes below, rather than certifying an older compatibility cache.
        self.positional_redefinitions = None;
        self.ensure_positional_redefinitions();
        let plan = self.supported_implied_specializations(
            &lib_by_name,
            self.external_implied_names.is_empty(),
        );
        let mut specializations: SpecializationGraph = plan
            .graph
            .iter()
            .map(|(&source, targets)| (source, targets.clone()))
            .collect();
        let mut planned = Vec::new();
        for (&(owner, edge), retained) in plan.candidates.iter() {
            if retained {
                let legacy_slot = (owner >= self.lib_boundary)
                    .then(|| {
                        self.legacy_implied_plan_with_owners(owner, &lib_by_name, &owners)
                            .iter()
                            .position(|old| *old == edge)
                    })
                    .flatten();
                planned.push((owner, edge, legacy_slot));
            }
        }
        let mut positional: Vec<_> = self
            .positional_redefinitions
            .as_ref()
            .unwrap()
            .targets
            .iter()
            .map(|(&source, targets)| (source, targets.clone()))
            .collect();
        positional.sort_by_key(|(source, _)| *source);
        for (source, targets) in positional {
            for target in targets {
                let target_id = self.elements[target].id;
                planned.push((
                    source,
                    (
                        "Redefinition",
                        "redefiningFeature",
                        "redefinedFeature",
                        target_id,
                    ),
                    None,
                ));
                let targets = specializations.entry(self.elements[source].id).or_default();
                if !targets.contains(&target_id) {
                    targets.push(target_id);
                }
            }
        }
        // Retain this producer's exact recipes for the immediately following
        // tail transaction. Its positional table was computed from this same
        // current static authority; no second whole-model positional run is
        // needed before checking the rows we are about to append.
        let (planner_bases, planner_incomplete) = self
            .positional_direct_bases_from_static_plan(&plan, None)
            .expect("unbounded static base capture");
        let static_prefix = Arc::new(super::semantic_batch::StaticPrefix {
            authored_end: from,
            rows: planned
                .iter()
                .map(|&(owner, edge, legacy_slot)| {
                    static_recipe(self.elements[owner].id, owner, edge, legacy_slot)
                })
                .collect(),
            positional: Arc::new(self.positional_redefinitions.as_ref().unwrap().clone()),
            chain_bases: Arc::clone(&plan.chain_bases),
            planner_bases,
            planner_incomplete,
            specializations: specializations.clone(),
        });
        let mut static_owners = HashSet::new();
        for row in &static_prefix.rows {
            let i = row.owner;
            static_owners.insert(i);
            let mut props = crate::properties::Properties::new();
            props.insert("isImplied", json!(true));
            props.insert(row.source_key, json!({ "@id": row.owner_id.to_string() }));
            props.insert(row.target_key, json!({ "@id": row.target.to_string() }));
            self.elements.push(Elem {
                ty: row.kind,
                id: row.id,
                path: String::new(),
                path_parent: None,
                props,
                owned_relationships: Default::default(),
                children: Default::default(),
                owning_relationship: None,
            });
            let idx = self.elements.len() - 1;
            ownership
                .register_generic(idx, i)
                .expect("the implied materializer appends ordered relationship nodes");
        }
        self.implied_from = Some(from);
        // This synchronous append cannot mutate an authored chain fact. Keep
        // the exact validated authority across the known static publication.
        *plan.source_rows.lock().unwrap() = self.elements.observe_revision();
        self.semantic_ownership = Some(Arc::new(ownership));
        self.implied = Some(ImpliedTable {
            from,
            owned_results_from: self.elements.len(),
            owned_results_state: OwnedResultState::Pending,
            specializations,
            static_authority: plan,
            static_rows: self.elements.observe_revision(),
            static_owners,
        });
        let before = self.publication.revision();
        self.materialize_owned_results(Some(static_prefix));
        if before.same_as(&self.publication.revision()) {
            self.publication.published();
        }
    }
    /// Complete planning before append, and publish one ownership view. A work
    /// limit discards all plans rather than freezing an order-dependent prefix.
    fn materialize_owned_results(
        &mut self,
        static_prefix: Option<Arc<super::semantic_batch::StaticPrefix>>,
    ) {
        let Some(table) = self.implied.as_ref() else {
            return;
        };
        if table.owned_results_state != OwnedResultState::Pending {
            return;
        }
        debug_assert_eq!(table.owned_results_from, self.elements.len());
        // Result admission retains its independent full allowance. Dynamic
        // refusal cannot erase a valid result or BindingConnector subtree.
        let before = self.elements.observe_revision();
        let before_epoch = self.publication.revision();
        let mut result_steps = 0;
        let plans = super::owned_results::plan_reference_results(self, &mut result_steps);
        let result_state = if plans.is_some() {
            OwnedResultState::Attempted
        } else {
            OwnedResultState::WorkLimited
        };
        let plans = plans.unwrap_or_default();
        let mut dynamic_steps = plans.len().saturating_mul(11);
        let mut reserved: HashSet<_> = if dynamic_steps <= crate::eval::MAX_STEPS {
            plans.iter().flat_map(|plan| plan.ids()).collect()
        } else {
            HashSet::new()
        };
        let mut default_steps = 0;
        let default_plans =
            super::owned_results::plan_constructor_defaults(self, &reserved, &mut default_steps)
                .unwrap_or_default();
        dynamic_steps = dynamic_steps.saturating_add(default_plans.len().saturating_mul(8));
        reserved.extend(default_plans.iter().flat_map(|plan| plan.ids()));
        let original_view = Arc::clone(self.semantic_ownership.as_ref().unwrap());
        let mut ownership = (!plans.is_empty() || !default_plans.is_empty())
            .then(|| original_view.as_ref().clone());
        let mut rows = Vec::new();
        let mut result_edges = Vec::new();
        let mut result_redefinition_steps = plans.len();
        let mut result_roles = Vec::new();
        let mut local_steps = plans.len().saturating_mul(3);
        let mut local_roles = Vec::new();
        for plan in plans {
            let start = self.elements.len() + rows.len();
            let staged = super::owned_results::stage_owned_result(
                self,
                ownership.as_mut().unwrap(),
                plan,
                start,
                &mut rows,
            );
            result_edges.extend(staged.specializations);
            if result_redefinition_steps <= crate::eval::MAX_STEPS {
                result_roles.push(staged.featuring[0]);
            }
            if local_steps <= crate::eval::MAX_STEPS {
                local_roles.extend(staged.featuring);
            }
        }
        for plan in default_plans {
            let start = self.elements.len() + rows.len();
            let (edges, roles) = super::owned_results::stage_constructor_default(
                self,
                ownership.as_mut().unwrap(),
                plan,
                start,
                &mut rows,
            );
            result_edges.extend(edges);
            local_steps = local_steps.saturating_add(roles.len());
            if local_steps <= crate::eval::MAX_STEPS {
                local_roles.extend(roles);
            }
        }
        let mut dynamic = if dynamic_steps > crate::eval::MAX_STEPS {
            Err(super::dynamic_invocations::Refusal::WorkLimit)
        } else {
            self.prepare_dynamic_graph(&reserved, &mut dynamic_steps, static_prefix)
        };
        let mut graph = None;
        if let Ok(Some(plan)) = &dynamic {
            if !plan.tail.is_empty() {
                let staged = (|| {
                    let mut next = ownership
                        .as_ref()
                        .unwrap_or(original_view.as_ref())
                        .clone_with_budget(&mut dynamic_steps)
                        .ok_or(super::dynamic_invocations::Refusal::WorkLimit)?;
                    let graph =
                        super::dynamic_graph::stage_dynamic_adjacency(plan, &mut dynamic_steps)?;
                    let tail = super::dynamic_graph::stage_dynamic_rows(
                        self,
                        plan,
                        self.elements.len() + rows.len(),
                        &mut next,
                        &mut dynamic_steps,
                    )?;
                    Ok::<_, super::dynamic_invocations::Refusal>((tail, next, graph))
                })();
                match staged {
                    Ok((tail, next, edges)) => {
                        rows.extend(tail);
                        ownership = Some(next);
                        graph = Some(edges);
                    }
                    Err(reason) => dynamic = Err(reason),
                }
            }
        }
        if !result_edges.is_empty() {
            let graph =
                graph.get_or_insert_with(|| self.implied.as_ref().unwrap().specializations.clone());
            for (specific, general) in result_edges {
                graph.entry(specific).or_default().push(general);
            }
        }
        let local = if local_steps > crate::eval::MAX_STEPS {
            Err(super::dynamic_invocations::Refusal::WorkLimit)
        } else if local_roles.is_empty() {
            Ok(HashSet::new())
        } else {
            super::local_featuring::prepare(self, &rows, &local_roles, &mut local_steps).map(
                |plan| {
                    plan.append(
                        &mut rows,
                        ownership.as_mut().expect("generated local owners"),
                    )
                },
            )
        };
        let result_redefinition = if result_redefinition_steps > crate::eval::MAX_STEPS {
            Err(super::dynamic_invocations::Refusal::WorkLimit)
        } else if result_roles.is_empty() {
            Ok(super::result_redefinition::Evidence::default())
        } else {
            super::result_redefinition::prepare(
                self,
                &rows,
                &result_roles,
                &mut result_redefinition_steps,
            )
            .map(|plan| {
                plan.append(
                    &mut rows,
                    ownership.as_mut().expect("generated result owners"),
                    graph.as_mut().expect("result specialization graph"),
                )
            })
        };
        // Allocate the accepted snapshot and its exact next epoch before the
        // first physical append. Installation performs no semantic reads.
        let epoch = super::publication::Revision::next();
        let after_rows = if rows.is_empty() {
            before.clone()
        } else {
            crate::layered::Revision::default()
        };
        let accepted = Arc::new(
            super::dynamic_graph::Snapshot::new(self, epoch.clone(), after_rows.clone(), dynamic)
                .with_local(local)
                .with_result_redefinition(result_redefinition),
        );
        let ownership = ownership.map(Arc::new);
        assert!(
            self.elements
                .revision()
                .is_some_and(|now| now.same_as(&before))
        );
        assert!(before_epoch.same_as(&self.publication.revision()));
        let semantic_change = !rows.is_empty() || accepted.plan.is_some();
        let static_plan = self
            .supported_implied
            .clone()
            .filter(|_| self.supported_chain_evidence_current());
        let physical_was_current = self.physical_static_authority_current();
        self.elements
            .append_staged(rows, &before, after_rows.clone());
        if physical_was_current {
            let table = self.implied.as_mut().unwrap();
            table.static_rows = after_rows.clone();
            *table.static_authority.source_rows.lock().unwrap() = after_rows.clone();
        }
        // Staged tail rows cannot alter the already checked authored chain facts.
        // Retain the same static authority across this known semantic append.
        if let Some(plan) = &static_plan {
            *plan.source_rows.lock().unwrap() = after_rows;
        }
        if let Some(ownership) = ownership {
            self.semantic_ownership = Some(ownership);
        }
        let table = self.implied.as_mut().unwrap();
        table.owned_results_state = result_state;
        if let Some(graph) = graph {
            table.specializations = graph;
        }
        if semantic_change {
            self.invalidate_semantic_indexes();
            self.supported_implied = static_plan;
        }
        self.dynamic_graph = Some(accepted);
        self.publication.install(epoch);
    }

    fn discard_semantic_result_tail(&mut self) {
        self.dynamic_graph = None;
        let Some(table) = self.implied.as_ref() else {
            self.publication.published();
            return;
        };
        let boundary = table.owned_results_from;
        let ownership = self
            .semantic_ownership
            .as_ref()
            .unwrap()
            .without_result_tail(boundary)
            .expect("certified result tail");
        // Validate the mutable-tail boundary before changing caches or rows.
        assert!(self.elements.can_truncate_tail(boundary));
        self.invalidate_semantic_indexes();
        self.elements.truncate_tail(boundary);
        self.semantic_ownership = Some(Arc::new(ownership));
        self.implied.as_mut().unwrap().owned_results_state = OwnedResultState::Pending;
        self.refresh_materialized_specializations();
        self.publication.published();
    }
    fn refresh_materialized_specializations(&mut self) {
        if self.implied.is_none() {
            return;
        }
        let owners = self.semantic_relationship_owners();
        let (_, graph) = self.required_specialization_edges(&[], self.elements.len(), &owners);
        if let Some(table) = self.implied.as_mut() {
            table.specializations = graph;
        }
    }
    /// The former plan, used only to preserve identifiers for relationships
    /// already emitted by earlier versions. It does not decide semantics.
    fn legacy_implied_plan_with_owners(
        &self,
        i: usize,
        names: &HashMap<String, Uuid>,
        owners: &[Option<usize>],
    ) -> Vec<PlannedEdge> {
        self.legacy_implied_plan_with_budget(i, names, owners, None)
            .expect("unbounded legacy recipe cannot exhaust budget")
    }
}

#[cfg(test)]
mod central_publication_tests {
    use super::*;
    fn fixture() -> ResolvedModel {
        let mut m = crate::model::Model::new();
        m.add_source(
            "publication.kerml",
            "feature original=4; feature use=original;",
        );
        assert!(!m.has_errors());
        ResolvedModel::build(&m)
    }
    #[test]
    fn stored_and_retained_report_reads_do_not_become_demands() {
        let mut r = fixture();
        let before = r.b.elements.len();
        let original = r.resolve_qualified("original").unwrap();
        assert_eq!(r.element_name(original), Some("original"));
        let expression =
            r.b.elements
                .iter()
                .position(|e| e.ty == "FeatureReferenceExpression")
                .unwrap();
        let _report = r.model_level_evaluability(ElementRef(expression));
        assert_eq!(r.b.elements.len(), before);
        assert!(r.b.implied.is_none());
        assert!(r.b.semantic_ownership.is_none());
    }
    #[test]
    fn builder_and_resolved_demand_share_one_table_and_order() {
        let mut direct = fixture();
        let mut wrapped = fixture();
        assert_eq!(
            direct.b.ensure_semantic_graph(),
            super::super::publication::Status::Ready
        );
        wrapped.ensure_implied();
        let rows = |r: &ResolvedModel| {
            r.b.elements
                .iter()
                .map(|e| (e.ty, e.id))
                .collect::<Vec<_>>()
        };
        assert_eq!(rows(&direct), rows(&wrapped));
        let count = direct.b.elements.len();
        let revision = direct.b.publication.revision();
        direct.ensure_implied();
        direct.ensure_implied();
        assert_eq!(direct.b.elements.len(), count);
        assert!(revision.same_as(&direct.b.publication.revision()));
        assert_eq!(direct.by_id_built_for, count);
    }
    #[test]
    fn suppressed_preparation_keeps_logical_readiness_without_publication() {
        let mut r = fixture();
        r.b.suppress_semantic_publication();
        assert!(r.b.semantic_ready);
        let count = r.b.elements.len();
        assert_eq!(
            r.b.ensure_semantic_graph(),
            super::super::publication::Status::Construction
        );
        r.prepare_quantity_memo();
        let _facts = r.b.prepare_facts();
        assert_eq!(r.b.elements.len(), count);
        assert!(r.b.implied.is_none());
        assert!(r.b.semantic_ownership.is_none());
    }
    #[test]
    fn prepared_build_and_decoded_install_keep_source_prefix_unpublished() {
        let mut model = crate::model::Model::new();
        model.add_library_source(
            "publication-library.kerml",
            "standard library package L { feature n=4; feature read=n; }",
        );
        assert!(!model.has_errors());
        let prepared = model.prepare_library().unwrap();
        assert!(prepared.builder.implied.is_none());
        assert!(prepared.builder.semantic_ownership.is_none());
        assert!(
            prepared
                .builder
                .publication
                .revision()
                .same_as(&Default::default())
        );
        let decoded = Arc::new(
            crate::prepared::PreparedLibrary::from_bytes(&prepared.to_bytes(918).unwrap(), 918)
                .unwrap(),
        );
        assert!(decoded.builder.implied.is_none());
        assert!(decoded.builder.semantic_ownership.is_none());
        assert!(
            decoded
                .builder
                .publication
                .revision()
                .same_as(&Default::default())
        );
        let mut replay = crate::model::Model::new();
        decoded.install(&mut replay).unwrap();
        replay.add_source("publication-user.kerml", "feature answer=L::n;");
        let mut r = ResolvedModel::build(&replay);
        assert!(r.b.implied.is_none());
        assert!(r.b.semantic_ownership.is_none());
        r.ensure_implied();
        assert!(r.b.implied.is_some());
        assert!(r.b.semantic_ownership.is_some());
    }
    #[test]
    fn reentrant_demand_publishes_nothing_and_outer_retry_succeeds() {
        let mut r = fixture();
        let count = r.b.elements.len();
        let guard = r.b.publication.begin(true).unwrap();
        assert_eq!(
            r.b.ensure_semantic_graph(),
            super::super::publication::Status::Reentrant
        );
        assert_eq!(r.b.elements.len(), count);
        assert!(r.b.implied.is_none());
        drop(guard);
        r.ensure_implied();
        assert!(r.b.implied.is_some());
    }
    #[test]
    fn equal_length_tail_republication_invalidates_resolved_memos() {
        let mut r = fixture();
        r.ensure_implied();
        let count = r.b.elements.len();
        let revision = r.b.publication.revision();
        r.redefiner_index = Some(HashMap::new());
        r.import_truncated.insert((0, true), true);
        r.b.discard_semantic_result_tail();
        assert_eq!(
            r.b.ensure_semantic_graph(),
            super::super::publication::Status::Ready
        );
        assert_eq!(r.b.elements.len(), count);
        assert!(!revision.same_as(&r.b.publication.revision()));
        // Entry sync is observation-only, and detects equal-size replacement.
        r.ensure_by_id();
        assert!(r.redefiner_index.is_none());
        assert!(r.import_truncated.is_empty());
        assert_eq!(r.by_id_built_for, count);
    }
}

impl Builder {
    pub(super) fn required_specialization_edges_with_fixed_prefix(
        &mut self,
        candidates: &[(usize, PlannedEdge)],
        fixed: usize,
        explicit_len: usize,
        rel_owner: &[Option<usize>],
        mut steps: Option<&mut usize>,
    ) -> Option<(Vec<bool>, SpecializationGraph)> {
        let chains = self.checked_chain_bases(explicit_len, steps.as_deref_mut())?;
        self.required_specialization_edges_with_chain_bases(
            candidates,
            fixed,
            explicit_len,
            rel_owner,
            &chains,
            steps,
        )
    }

    pub(super) fn required_specialization_edges_with_chain_bases(
        &self,
        candidates: &[(usize, PlannedEdge)],
        fixed: usize,
        explicit_len: usize,
        rel_owner: &[Option<usize>],
        chains: &super::type_relations::FeatureChainBases,
        mut steps: Option<&mut usize>,
    ) -> Option<(Vec<bool>, SpecializationGraph)> {
        planning_charge(&mut steps, 1)?;
        if fixed > candidates.len() {
            return None;
        }
        let mut graph: HashMap<Uuid, Vec<(Uuid, Option<usize>)>> = HashMap::new();
        for (r, relation) in self.elements.iter().take(explicit_len).enumerate() {
            planning_charge(&mut steps, 1)?;
            if !conforms(relation.ty, "Specialization") {
                continue;
            }
            let source = [
                "specific",
                "subclassifier",
                "typedFeature",
                "subsettingFeature",
                "redefiningFeature",
                "referencingFeature",
                "crossingFeature",
            ]
            .iter()
            .find_map(|key| relation.props.get(key));
            let source = match source {
                Some(value) => value.as_reference(),
                None => rel_owner[r].map(|owner| self.elements[owner].id),
            };
            let target = specialization_target(relation);
            if let (Some(source), Some(target)) = (source, target) {
                graph.entry(source).or_default().push((target, None));
            }
        }
        for (index, &(owner, edge)) in candidates.iter().enumerate() {
            planning_charge(&mut steps, 1)?;
            graph
                .entry(self.elements[owner].id)
                .or_default()
                .push((edge.3, Some(index)));
        }
        for (&source, &target) in &chains.targets {
            planning_charge(&mut steps, 1)?;
            graph
                .entry(self.elements[source].id)
                .or_default()
                .push((self.elements[target].id, None));
        }
        // Consider dependents before their bases. On a long inheritance
        // chain, each candidate can then find the next ancestor's still-live
        // base edge immediately instead of repeatedly walking to the root.
        // Reverse DFS postorder also handles cycles without recursion.
        let mut visited = HashSet::new();
        let mut postorder = Vec::new();
        let mut todo = Vec::new();
        for &(owner, _) in candidates {
            planning_charge(&mut steps, 1)?;
            let source = self.elements[owner].id;
            // Each prior DFS drains before the next candidate. An already
            // visited source therefore has a complete postorder, including
            // cyclic graphs. Repeated candidates need no new traversal stack.
            if visited.contains(&source) {
                continue;
            }
            todo.push((source, false));
            while let Some((at, exiting)) = todo.pop() {
                planning_charge(&mut steps, 1)?;
                if exiting {
                    postorder.push(at);
                } else if visited.insert(at) {
                    todo.push((at, true));
                    planning_charge(&mut steps, graph.get(&at).map_or(0, Vec::len))?;
                    todo.extend(
                        graph
                            .get(&at)
                            .into_iter()
                            .flatten()
                            .map(|&(next, _)| (next, false)),
                    );
                }
            }
        }
        planning_charge(&mut steps, postorder.len())?;
        let rank: HashMap<_, _> = postorder
            .into_iter()
            .enumerate()
            .map(|(rank, id)| (id, rank))
            .collect();
        // Rank is dense. Stable buckets produce exactly the previous stable
        // descending-rank order without comparing every candidate O(log n)
        // times. Keeping each bucket in candidate order preserves cycle anchors
        // and the fixed prefix while avoiding a second semantic graph.
        let order = reverse_rank_order(
            fixed..candidates.len(),
            rank.len(),
            |index| rank[&self.elements[candidates[index].0].id],
            &mut steps,
        )?;
        planning_charge(&mut steps, candidates.len())?;
        let mut retained = vec![true; candidates.len()];
        let mut seen = HashSet::new();
        let mut stack = Vec::new();
        for index in order {
            planning_charge(&mut steps, 1)?;
            let (owner, edge) = candidates[index];
            // A ReferenceSubsetting identifies an end, not merely a reachable
            // superfeature. Keep the required relationship itself.
            if edge.0 == "ReferenceSubsetting" {
                continue;
            }
            retained[index] = false;
            seen.clear();
            stack.clear();
            stack.push(self.elements[owner].id);
            let mut reaches = false;
            while let Some(at) = stack.pop() {
                planning_charge(&mut steps, 1)?;
                if at == edge.3 {
                    reaches = true;
                    break;
                }
                if !seen.insert(at) {
                    continue;
                }
                for &(next, candidate) in graph.get(&at).into_iter().flatten() {
                    planning_charge(&mut steps, 1)?;
                    if candidate.is_none_or(|candidate| retained[candidate]) {
                        // Reachability consumes a Boolean, not a traversal
                        // sequence. A witnessed edge can decide immediately.
                        if next == edge.3 {
                            reaches = true;
                            break;
                        }
                        stack.push(next);
                    }
                }
                if reaches {
                    break;
                }
            }
            retained[index] = !reaches;
        }
        let mut final_graph = HashMap::new();
        for (source, edges) in graph {
            planning_charge(&mut steps, 1)?;
            let mut targets = Vec::new();
            for (target, candidate) in edges {
                planning_charge(&mut steps, 1 + targets.len())?;
                if candidate.is_none_or(|candidate| retained[candidate])
                    && !targets.contains(&target)
                {
                    targets.push(target);
                }
            }
            final_graph.insert(source, targets);
        }
        Some((retained, final_graph))
    }
}

impl Builder {
    pub(super) fn static_specialization_prefix(
        &mut self,
        names: &HashMap<String, Uuid>,
        library_configuration: bool,
        steps: Option<&mut usize>,
    ) -> Option<Arc<super::semantic_batch::StaticPrefix>> {
        self.static_specialization_prefix_with_workspace(
            names,
            library_configuration,
            steps,
            &mut super::positional::PositionalWorkspace::one_shot(),
        )
    }

    pub(super) fn static_specialization_prefix_with_workspace(
        &mut self,
        names: &HashMap<String, Uuid>,
        library_configuration: bool,
        mut steps: Option<&mut usize>,
        workspace: &mut super::positional::PositionalWorkspace,
    ) -> Option<Arc<super::semantic_batch::StaticPrefix>> {
        let required = self.supported_implied_specializations_with_budget(
            names,
            library_configuration,
            steps.as_deref_mut(),
        )?;
        let (direct_bases, incomplete_bases) =
            self.positional_direct_bases_from_static_plan(&required, steps.as_deref_mut())?;
        let positional = self.plan_positional_redefinitions_with_workspace(
            &direct_bases,
            &incomplete_bases,
            steps.as_deref_mut(),
            workspace,
        )?;
        planning_charge(&mut steps, self.elements.len())?;
        for element in &self.elements {
            planning_charge(&mut steps, element.owned_relationships.len())?;
        }
        let owners = self.specialization_relation_owners();
        let mut rows = Vec::new();
        for (&(owner, edge), retained) in required.candidates.iter() {
            planning_charge(&mut steps, 1)?;
            if !retained {
                continue;
            }
            let legacy_slot = if owner >= self.lib_boundary {
                self.legacy_implied_plan_with_budget(owner, names, &owners, steps.as_deref_mut())?
                    .iter()
                    .position(|old| *old == edge)
            } else {
                None
            };
            rows.push(static_recipe(
                self.elements[owner].id,
                owner,
                edge,
                legacy_slot,
            ));
        }
        planning_charge(
            &mut steps,
            positional.targets.len().saturating_mul(
                (usize::BITS - positional.targets.len().max(1).leading_zeros()) as usize + 1,
            ),
        )?;
        let mut sources: Vec<_> = positional.targets.keys().copied().collect();
        sources.sort_unstable();
        for source in sources {
            let targets = &positional.targets[&source];
            planning_charge(&mut steps, targets.len())?;
            for &target in targets {
                rows.push(static_recipe(
                    self.elements[source].id,
                    source,
                    (
                        "Redefinition",
                        "redefiningFeature",
                        "redefinedFeature",
                        self.elements[target].id,
                    ),
                    None,
                ));
            }
        }
        let mut specializations = HashMap::new();
        for (&source, targets) in &required.graph {
            planning_charge(&mut steps, targets.len().saturating_add(1))?;
            specializations.insert(source, targets.clone());
        }
        for row in &rows {
            planning_charge(&mut steps, 1)?;
            let targets = specializations.entry(row.owner_id).or_insert_with(Vec::new);
            planning_charge(&mut steps, targets.len().saturating_add(1))?;
            if !targets.contains(&row.target) {
                targets.push(row.target);
            }
        }
        Some(Arc::new(super::semantic_batch::StaticPrefix {
            authored_end: self.explicit_len(),
            rows,
            positional: Arc::new(positional),
            planner_bases: direct_bases,
            planner_incomplete: incomplete_bases,
            chain_bases: Arc::clone(&required.chain_bases),
            specializations,
        }))
    }
}

fn static_recipe(
    owner_id: Uuid,
    owner: usize,
    edge: PlannedEdge,
    legacy_slot: Option<usize>,
) -> super::semantic_batch::Edge {
    let (kind, source_key, target_key, target) = edge;
    let key = match legacy_slot {
        Some(n) => format!("{owner_id}/implied{n}"),
        None => format!("{owner_id}/implied/{kind}/{target}"),
    };
    super::semantic_batch::Edge {
        owner,
        owner_id,
        id: Uuid::new_v5(&Uuid::NAMESPACE_OID, key.as_bytes()),
        kind,
        source_key,
        target_key,
        target,
    }
}

impl Builder {
    fn legacy_implied_plan_with_budget(
        &self,
        i: usize,
        lib_by_name: &HashMap<String, Uuid>,
        rel_owner: &[Option<usize>],
        mut steps: Option<&mut usize>,
    ) -> Option<Vec<(&'static str, &'static str, &'static str, Uuid)>> {
        planning_charge(
            &mut steps,
            self.elements[i]
                .owned_relationships
                .len()
                .saturating_mul(4)
                .saturating_add(1),
        )?;
        let t = self.elements[i].ty;
        let mut plan = Vec::new();
        let explicit: Vec<usize> = self.elements[i].owned_relationships.to_vec();
        // Tables 31/32: the library bases of the element's kind, unless an
        // explicit specialization of the covering kind is present
        // (anti-redundancy, approximated as any explicit same-kind
        // specialization — the emitter's rule).
        let bases: Option<ImpliedBases> = if let Some(kind) = def_kind_of(t) {
            Some((
                implicit_def_bases(kind),
                "Subclassification",
                "subclassifier",
                "superclassifier",
                &["Subclassification", "Specialization"],
            ))
        } else {
            usage_kind_of(t, Dialect::Sysml).map(|kind| {
                (
                    implicit_usage_bases(kind),
                    "Subsetting",
                    "subsettingFeature",
                    "subsettedFeature",
                    &["Subsetting", "Redefinition", "ReferenceSubsetting"] as &[&str],
                )
            })
        };
        if let Some((bases, rel_ty, src, tgt, covering)) = bases {
            planning_charge(&mut steps, bases.len())?;
            let covered = explicit
                .iter()
                .any(|&r| covering.contains(&self.elements[r].ty));
            if !covered {
                for base in bases {
                    if let Some(&id) = lib_by_name.get(*base) {
                        plan.push((rel_ty, src, tgt, id));
                    }
                }
            }
        }
        // A variant specializes the variation it belongs to: a typing by
        // the owning variation definition, a subsetting of the owning
        // variation usage — unless written explicitly. The specification
        // asks for a direct *or indirect* specialization; only a direct
        // one is recognized here (`variant part small : Sub` with `Sub :>
        // Box` still gets the implied typing by `Box`), the same
        // approximation as the covering rule above.
        if let Some(rel) = self.elements[i].owning_relationship {
            if self.elements[rel].ty == "VariantMembership" {
                if let Some(variation) = rel_owner[rel] {
                    let variation_id = self.elements[variation].id;
                    let targets = |kinds: &[&str], key: &str| -> bool {
                        explicit.iter().any(|&r| {
                            kinds.contains(&self.elements[r].ty)
                                && self.elements[r]
                                    .props
                                    .get(key)
                                    .and_then(|v| v.as_reference())
                                    == Some(variation_id)
                        })
                    };
                    let vty = self.elements[variation].ty;
                    if conforms(vty, "Definition") {
                        if !targets(&["FeatureTyping", "ConjugatedPortTyping"], "type") {
                            plan.push(("FeatureTyping", "typedFeature", "type", variation_id));
                        }
                    } else if conforms(vty, "Usage")
                        && !targets(
                            &["Subsetting", "Redefinition", "ReferenceSubsetting"],
                            "subsettedFeature",
                        )
                    {
                        plan.push((
                            "Subsetting",
                            "subsettingFeature",
                            "subsettedFeature",
                            variation_id,
                        ));
                    }
                }
            }
        }
        Some(plan)
    }
}

#[cfg(test)]
mod feature_chain_operator_tests {
    use super::*;
    use crate::{
        json::{ElementRef, ResolvedModel},
        model::Model,
    };
    const LIB: &str = "standard library package ControlFunctions {function '.' {in source {feature target;} return result;}}";
    const USER: &str = "class A {feature x;} feature a:A; feature y=a.x;";
    fn fixture(library: &str) -> (ResolvedModel, usize, usize) {
        let mut m = Model::new();
        assert!(
            m.add_library_source("dot-library.kerml", library)
                .diagnostics
                .is_empty()
        );
        assert!(m.add_source("dot-user.kerml", USER).diagnostics.is_empty());
        let r = ResolvedModel::build(&m);
        let chain = r
            .user_elements()
            .find(|&e| r.element_type(e) == "FeatureChainExpression")
            .unwrap()
            .0;
        let parameter = r.b.elements[chain]
            .owned_relationships
            .iter()
            .copied()
            .find(|&rel| r.b.elements[rel].ty == "ParameterMembership")
            .unwrap();
        let input = r.b.elements[parameter].children[0];
        (r, chain, input)
    }
    fn typing(r: &mut ResolvedModel, chain: usize) -> Vec<Uuid> {
        r.implied_relationships(ElementRef(chain))
            .into_iter()
            .filter(|&rel| r.element_type(rel) == "FeatureTyping")
            .filter_map(|rel| {
                r.b.elements[rel.0]
                    .props
                    .get("type")
                    .and_then(|v| v.as_reference())
            })
            .collect()
    }
    #[test]
    fn fixed_dot_function_typing_and_input_redefinition_share_the_static_plan() {
        let (mut r, chain, input) = fixture(LIB);
        let dot = r.resolve_qualified("ControlFunctions::'.'").unwrap();
        let source = r
            .resolve_qualified("ControlFunctions::'.'::source")
            .unwrap();
        let authored: Vec<_> = r.b.elements.iter().map(|e| e.id).collect();
        assert_eq!(typing(&mut r, chain), vec![r.element_id(dot)]);
        assert!(
            r.b.semantic_redefinition_targets(input, true)
                .contains(&source.0)
        );
        assert!(
            r.b.completed_positional_targets(input)
                .unwrap()
                .contains(&source.0)
        );
        assert_eq!(
            r.b.elements
                .iter()
                .take(authored.len())
                .map(|e| e.id)
                .collect::<Vec<_>>(),
            authored
        );
        assert!(r.feature_type_report(ElementRef(chain)).function.is_err());
    }
    #[test]
    fn fixed_dot_role_requires_a_loaded_unique_function_and_exact_operator() {
        for kind in ["feature", "class", "behavior", "expr"] {
            let (mut r, chain, _) = fixture(&format!(
                "standard library package ControlFunctions {{{kind} '.';}}"
            ));
            assert!(typing(&mut r, chain).is_empty(), "{kind}");
        }
        for operator in [
            serde_json::json!("+"),
            serde_json::Value::Null,
            serde_json::json!(false),
        ] {
            let (mut r, chain, _) = fixture(LIB);
            r.b.elements[chain].props.insert("operator", operator);
            assert!(typing(&mut r, chain).is_empty());
        }
        let (mut r, chain, _) = fixture(LIB);
        let user = r.resolve_qualified("a").unwrap();
        let id = r.element_id(user);
        r.b.lib_qnames
            .push((id, vec!["ControlFunctions".into(), ".".into()]));
        assert!(typing(&mut r, chain).is_empty());
        let (mut r, chain, _) = fixture(LIB);
        let dot = r.resolve_qualified("ControlFunctions::'.'").unwrap();
        let user = r.resolve_qualified("a").unwrap();
        r.b.elements[user.0].id = r.element_id(dot);
        assert!(typing(&mut r, chain).is_empty());
    }
    #[test]
    fn absent_fixed_operator_uses_default_but_external_spelling_does_not_certify_role() {
        let (mut r, chain, _) = fixture(LIB);
        let mut props = r.b.elements[chain].props.to_json();
        props.remove("operator");
        let mut retained = crate::properties::Properties::new();
        for (key, value) in props {
            retained.insert(&key, value);
        }
        r.b.elements[chain].props = retained;
        assert_eq!(typing(&mut r, chain).len(), 1);
        let (mut r, chain, _) = fixture("");
        let id = Uuid::new_v5(&Uuid::NAMESPACE_OID, b"external dot role");
        r.set_library_names(&HashMap::from([(
            id.to_string(),
            vec!["ControlFunctions".into(), ".".into()],
        )]));
        assert!(typing(&mut r, chain).is_empty());
    }
    #[test]
    fn fixed_dot_bounded_planning_refuses_before_publication_and_retries() {
        let (mut r, chain, input) = fixture(LIB);
        let source = r
            .resolve_qualified("ControlFunctions::'.'::source")
            .unwrap();
        r.b.positional_redefinitions = None;
        r.b.supported_implied = None;
        let count = r.b.elements.len();
        let mut steps = crate::eval::MAX_STEPS - 1;
        assert!(!r.b.ensure_positional_redefinitions_with_budget(&mut steps));
        assert!(steps > crate::eval::MAX_STEPS);
        assert!(r.b.positional_redefinitions.is_none());
        assert!(r.b.implied.is_none());
        assert_eq!(r.b.elements.len(), count);
        assert!(r.b.ensure_positional_redefinitions_with_budget(&mut 0));
        assert!(
            r.b.completed_positional_targets(input)
                .unwrap()
                .contains(&source.0)
        );
        assert_eq!(typing(&mut r, chain).len(), 1);
    }

    #[test]
    fn actual_dot_library_reuses_checked_parameter_identity() {
        let mut m = Model::new();
        let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../../spec-refs/SysML-v2-Release/sysml.library");
        m.load_library_dir(&path).unwrap();
        m.add_source("actual-dot.kerml", USER);
        let mut r = ResolvedModel::build(&m);
        let chain = r
            .user_elements()
            .find(|&e| r.element_type(e) == "FeatureChainExpression")
            .unwrap()
            .0;
        let parameter = r.b.elements[chain]
            .owned_relationships
            .iter()
            .copied()
            .find(|&rel| r.b.elements[rel].ty == "ParameterMembership")
            .unwrap();
        let raw =
            super::super::structural_index::StoredStructure::for_query(&mut r.b, &mut 0).unwrap();
        let input = super::super::membership_evidence::member(&r.b, &raw, chain, parameter, &mut 0)
            .unwrap();
        let dot = r.resolve_qualified("ControlFunctions::'.'").unwrap();
        let source = r
            .resolve_qualified("ControlFunctions::'.'::source")
            .unwrap();
        assert_eq!(typing(&mut r, chain), vec![r.element_id(dot)]);
        assert!(
            r.b.semantic_redefinition_targets(input, true)
                .contains(&source.0)
        );
    }
}

#[cfg(test)]
mod partial_expression_role_tests {
    use super::*;
    use crate::{libcache::LibraryCache, model::Model, prepared::PreparedLibrary};

    const GENERIC: &str = "standard library package Values {datatype Value;} standard library package Performances {function Evaluation {return result:Values::Value;} expr evaluations:Evaluation;";
    const USER: &str = "class C; feature constructed=new C(); feature literal=1; feature decoy;";

    fn models(library: &str) -> Vec<ResolvedModel> {
        let mut base = Model::new();
        assert!(
            base.add_library_source("partial-roles.kerml", library)
                .diagnostics
                .is_empty()
        );
        base.record_library_cache();
        ResolvedModel::build(&base);
        let cache =
            LibraryCache::from_bytes(&base.take_recorded_library_cache().unwrap().to_bytes())
                .unwrap();
        let prepared = base.prepare_library().unwrap();
        let decoded =
            Arc::new(PreparedLibrary::from_bytes(&prepared.to_bytes(127).unwrap(), 127).unwrap());
        (0..4)
            .map(|mode| {
                let mut model = Model::new();
                match mode {
                    2 => Arc::clone(&prepared).install(&mut model).unwrap(),
                    3 => Arc::clone(&decoded).install(&mut model).unwrap(),
                    _ => {
                        model.add_library_source("partial-roles.kerml", library);
                        if mode == 1 {
                            model.set_library_cache(cache.clone());
                        }
                    }
                }
                assert!(
                    model
                        .add_source("partial-roles-user.kerml", USER)
                        .diagnostics
                        .is_empty()
                );
                ResolvedModel::build(&model)
            })
            .collect()
    }

    fn names(r: &ResolvedModel) -> HashMap<String, Uuid> {
        r.b.lib_qnames
            .iter()
            .map(|(id, parts)| (parts.join("::"), *id))
            .collect()
    }

    fn expression(r: &ResolvedModel, ty: &str) -> ElementRef {
        r.user_elements()
            .find(|&e| r.element_type(e) == ty)
            .unwrap()
    }

    fn retained(plan: &SupportedImpliedSpecializations, owner: usize) -> Vec<Uuid> {
        plan.candidates
            .iter()
            .filter_map(|((at, edge), retained)| (*at == owner && retained).then_some(edge.3))
            .collect()
    }

    #[test]
    fn actually_missing_leaf_and_constructor_roles_keep_broader_ancestry_across_replay() {
        for literal_role in [false, true] {
            let library = format!(
                "{GENERIC} {} }}",
                if literal_role {
                    "expr literalEvaluations subsets evaluations;"
                } else {
                    ""
                }
            );
            let mut expected = None;
            for mut r in models(&library) {
                let sources: Vec<_> = r.user_elements().map(|e| r.element_id(e)).collect();
                let generic = r.resolve_qualified("Performances::evaluations").unwrap();
                let literal = expression(&r, "LiteralInteger");
                let constructor = expression(&r, "ConstructorExpression");
                let literal_base = if literal_role {
                    r.resolve_qualified("Performances::literalEvaluations")
                        .unwrap()
                } else {
                    generic
                };
                let mut ids = Vec::new();
                for (owner, target) in [(literal, literal_base), (constructor, generic)] {
                    assert!(r.conforms_with_implied(owner, generic));
                    let rows = r.implied_relationships(owner);
                    assert_eq!(
                        rows.len(),
                        1,
                        "only the available broader Subsetting is retained"
                    );
                    let row = &r.b.elements[rows[0].0];
                    assert_eq!(row.ty, "Subsetting");
                    assert_eq!(specialization_target(row), Some(r.element_id(target)));
                    let key = format!(
                        "{}/implied/Subsetting/{}",
                        r.element_id(owner),
                        r.element_id(target)
                    );
                    assert_eq!(row.id, Uuid::new_v5(&Uuid::NAMESPACE_OID, key.as_bytes()));
                    ids.push(row.id);
                }
                if let Some(expected) = &expected {
                    assert_eq!(&ids, expected);
                } else {
                    expected = Some(ids);
                }
                assert!(r.b.planned_literal_target("LiteralInteger").is_none());
                assert!(
                    r.b.literal_inherited_memberships(literal.0, true)
                        .incomplete,
                    "even a typed broader return cannot certify a missing leaf role"
                );
                assert!(matches!(
                    r.model_level_evaluability(constructor).classification,
                    crate::json::ModelLevelEvaluability::Unknown(_)
                ));
                assert!(
                    r.b.semantic_ownership
                        .as_ref()
                        .unwrap()
                        .result(constructor.0)
                        .is_none()
                );
                assert_eq!(
                    sources,
                    r.user_elements()
                        .map(|e| r.element_id(e))
                        .collect::<Vec<_>>()
                );
            }
        }
    }

    #[test]
    fn all_leaf_kinds_accumulate_independent_generic_and_literal_requirements() {
        // Deliberately disconnected roles: availability of the leaf role says
        // nothing about whether the library supplied its required ancestry.
        let library = format!(
            "{GENERIC} expr literalEvaluations; expr literalBooleanEvaluations; expr literalIntegerEvaluations; expr literalRationalEvaluations; expr literalStringEvaluations; expr nullEvaluations; expr metadataAccessEvaluations; expr constructorEvaluations; }}"
        );
        for ty in [
            "LiteralBoolean",
            "LiteralInteger",
            "LiteralInfinity",
            "LiteralRational",
            "LiteralString",
            "NullExpression",
            "MetadataAccessExpression",
            "ConstructorExpression",
        ] {
            let mut r = models(&library).remove(0);
            let owner = expression(&r, "LiteralInteger");
            // Planning depends on metaclass, not literal value. This exercises
            // abstract-syntax kinds without pretending they share text syntax.
            r.b.elements[owner.0].ty = ty;
            let configuration = names(&r);
            let plan = r.b.supported_implied_specializations(&configuration, true);
            let mut expected = vec![configuration[expression_implied_base(ty).unwrap()]];
            if conforms(ty, "LiteralExpression") {
                expected.push(configuration["Performances::literalEvaluations"]);
            }
            expected.push(configuration["Performances::evaluations"]);
            let actual: Vec<_> = plan
                .candidates
                .iter()
                .filter_map(|((at, edge), _)| (*at == owner.0).then_some(edge.3))
                .collect();
            assert_eq!(
                actual, expected,
                "{ty}: every independent obligation is planned"
            );
            let survivors = retained(&plan, owner.0);
            for target in expected {
                let target = ElementRef(r.b.element_index_of_uuid(target).unwrap());
                assert!(
                    r.conforms_with_implied(owner, target),
                    "{ty}: required target remains reachable"
                );
            }
            assert!(!survivors.is_empty());
        }
    }

    #[test]
    fn invalid_narrow_roles_do_not_suppress_available_broader_roles() {
        let library = format!(
            "{GENERIC} expr literalEvaluations subsets evaluations; expr literalIntegerEvaluations subsets literalEvaluations; expr constructorEvaluations subsets evaluations; expr other; }}"
        );
        for (ty, role, parent) in [
            (
                "LiteralInteger",
                "Performances::literalIntegerEvaluations",
                "Performances::literalEvaluations",
            ),
            (
                "ConstructorExpression",
                "Performances::constructorEvaluations",
                "Performances::evaluations",
            ),
        ] {
            for problem in 0..6 {
                let mut r = models(&library).remove(0);
                let owner = expression(&r, ty);
                let target = r.resolve_qualified(role).unwrap();
                let mut configuration = names(&r);
                match problem {
                    0 => {
                        configuration.remove(role);
                    }
                    1 => {
                        r.b.elements[target.0].ty = "Class";
                    }
                    2 => {
                        r.b.elements[target.0].ty = "Feature";
                    }
                    3 => {
                        r.b.elements[target.0].ty = "Step";
                    }
                    4 => {
                        let other = r.resolve_qualified("Performances::other").unwrap();
                        r.b.lib_qnames.push((
                            r.element_id(other),
                            role.split("::").map(str::to_owned).collect(),
                        ));
                    }
                    5 => {
                        let decoy = r.resolve_qualified("decoy").unwrap();
                        configuration.insert(role.into(), r.element_id(decoy));
                    }
                    _ => unreachable!(),
                }
                r.b.id_index = None;
                r.b.supported_implied = None;
                let plan = r.b.supported_implied_specializations(&configuration, true);
                assert_eq!(
                    retained(&plan, owner.0),
                    vec![configuration[parent]],
                    "{ty}: invalid role {problem}"
                );
                assert!(
                    !plan
                        .candidates
                        .iter()
                        .any(|((at, edge), _)| *at == owner.0 && edge.3 == r.element_id(target))
                );
                assert!(!plan.expression_targets.contains_key(role));
            }
        }
    }
}

#[cfg(test)]
mod generic_feature_tests {
    use super::*;
    use crate::{json::model_to_compact_json, model::Model};
    const LIB: &str = "standard library package Base {classifier Anything; feature things:Anything; feature narrow subsets things;}";
    fn fixture() -> (Model, ResolvedModel) {
        let mut m = Model::new();
        assert!(
            m.add_library_source("generic-feature.kerml", LIB)
                .diagnostics
                .is_empty()
        );
        assert!(m.add_source("kinds.kerml","feature plain; var feature variable; class C {end feature e; portion feature piece;} step s; expr x; feature narrower subsets Base::narrow;").diagnostics.is_empty());
        assert!(
            m.add_source("usages.sysml", "part def P {ref r; end item e; action a;}")
                .diagnostics
                .is_empty()
        );
        let r = ResolvedModel::build(&m);
        (m, r)
    }
    fn names(r: &ResolvedModel) -> HashMap<String, Uuid> {
        r.b.lib_qnames
            .iter()
            .map(|(id, q)| (q.join("::"), *id))
            .collect()
    }
    fn required(r: &mut ResolvedModel, owner: usize) -> Vec<Uuid> {
        let plan = r.b.supported_implied_specializations(&names(r), true);
        plan.candidates
            .iter()
            .filter_map(|((e, edge), _)| (*e == owner).then_some(edge.3))
            .collect()
    }
    #[test]
    fn feature_ancestry_applies_to_variable_end_portion_and_usage_descendants() {
        let (_, mut r) = fixture();
        let target = r.resolve_qualified("Base::things").unwrap();
        let id = r.element_id(target);
        for name in [
            "plain", "variable", "C::e", "C::piece", "s", "x", "P::r", "P::e", "P::a",
        ] {
            let e = r.resolve_qualified(name).unwrap();
            assert!(required(&mut r, e.0).contains(&id), "{name}");
        }
        let classifier = r.resolve_qualified("C").unwrap();
        assert!(!required(&mut r, classifier.0).contains(&id));
        // Independent unconditional ancestry is not a Boolean validity proof.
        let plain = r.resolve_qualified("plain").unwrap();
        r.b.set(plain.0, "isVariable", json!("malformed"));
        r.b.supported_implied = None;
        assert!(required(&mut r, plain.0).contains(&id));
    }
    #[test]
    fn feature_role_requires_unique_loaded_feature_identity() {
        for mode in 0..5 {
            let (_, mut r) = fixture();
            let e = r.resolve_qualified("plain").unwrap();
            let target = r.resolve_qualified("Base::things").unwrap();
            let mut configuration = names(&r);
            match mode {
                0 => {
                    configuration.remove(FEATURE_BASE);
                }
                1 => r.b.elements[target.0].ty = "Class",
                2 => {
                    let other = r.resolve_qualified("Base::narrow").unwrap();
                    r.b.lib_qnames
                        .push((r.element_id(other), vec!["Base".into(), "things".into()]));
                }
                3 => {
                    let other = r.resolve_qualified("Base::narrow").unwrap();
                    r.b.elements[other.0].id = r.element_id(target);
                }
                _ => {
                    configuration.insert(
                        FEATURE_BASE.into(),
                        Uuid::new_v5(&Uuid::NAMESPACE_OID, b"unloaded-feature-role"),
                    );
                }
            }
            r.b.id_index = None;
            r.b.supported_implied = None;
            let plan = r.b.supported_implied_specializations(&configuration, false);
            assert!(
                !plan.expression_targets.contains_key(FEATURE_BASE),
                "mode {mode}"
            );
            assert!(!plan.candidates.iter().any(|((owner, _), _)| *owner == e.0));
        }
    }
    #[test]
    fn generic_requirement_minimizes_self_and_indirect_paths_and_preserves_source_identity() {
        let (m, mut r) = fixture();
        let compact = model_to_compact_json(&m);
        let source: Vec<_> = r.user_elements().map(|e| r.element_id(e)).collect();
        let base = r.resolve_qualified(FEATURE_BASE).unwrap();
        let narrower = r.resolve_qualified("narrower").unwrap();
        let plain = r.resolve_qualified("plain").unwrap();
        let base_id = r.element_id(base);
        let relationships = r.implied_relationships(plain);
        let edge = relationships
            .iter()
            .find(|&&e| specialization_target(&r.b.elements[e.0]) == Some(base_id))
            .unwrap();
        assert_eq!(r.element_type(*edge), "Subsetting");
        assert_eq!(
            r.element_id(*edge),
            Uuid::new_v5(
                &Uuid::NAMESPACE_OID,
                format!("{}/implied/Subsetting/{base_id}", r.element_id(plain)).as_bytes()
            )
        );
        for owner in [base, narrower] {
            assert!(
                !r.implied_relationships(owner)
                    .iter()
                    .any(|e| specialization_target(&r.b.elements[e.0]) == Some(base_id))
            );
        }
        assert!(r.conforms_with_implied(narrower, base));
        assert_eq!(
            source,
            r.user_elements()
                .map(|e| r.element_id(e))
                .collect::<Vec<_>>()
        );
        assert_eq!(compact, model_to_compact_json(&m));
    }
    #[test]
    fn generic_feature_plan_exhaustion_is_unpublished_and_retryable() {
        let (_, mut r) = fixture();
        r.b.supported_implied = None;
        let names = names(&r);
        let mut steps = crate::eval::MAX_STEPS;
        assert!(
            r.b.supported_implied_specializations_with_budget(&names, true, Some(&mut steps))
                .is_none()
        );
        assert!(r.b.supported_implied.is_none());
        assert!(
            r.b.supported_implied_specializations_with_budget(&names, true, Some(&mut 0))
                .is_some()
        );
    }
}

#[cfg(test)]
mod reduction_rank_tests {
    use super::*;

    #[test]
    fn buckets_preserve_stable_comparison_order_for_every_fixed_prefix() {
        // Exhaust all four-rank words up to length seven, including ties,
        // empty ranks and every immutable prefix used by dynamic reduction.
        for len in 0..=7 {
            for word in 0..4usize.pow(len as u32) {
                let ranks: Vec<_> = (0..len).map(|shift| (word >> (shift * 2)) & 3).collect();
                for fixed in 0..=len {
                    let mut expected: Vec<_> = (fixed..len).collect();
                    expected.sort_by_key(|&i| std::cmp::Reverse(ranks[i]));
                    let mut steps = 0;
                    let actual =
                        reverse_rank_order(fixed..len, 4, |i| ranks[i], &mut Some(&mut steps))
                            .unwrap();
                    assert_eq!(actual, expected, "ranks={ranks:?}, fixed={fixed}");
                    assert_eq!(steps, 8 + 2 * (len - fixed));
                }
            }
        }
        assert_eq!(
            reverse_rank_order(0..0, 0, |_| unreachable!(), &mut None),
            Some(vec![])
        );
    }

    #[test]
    fn exhausted_order_is_not_published_and_fresh_budget_retries() {
        let mut exhausted = crate::eval::MAX_STEPS;
        assert!(reverse_rank_order(0..3, 3, |i| i, &mut Some(&mut exhausted)).is_none());
        let mut mid = crate::eval::MAX_STEPS - 4;
        assert!(reverse_rank_order(0..3, 3, |i| i, &mut Some(&mut mid)).is_none());
        let mut fresh = 0;
        assert_eq!(
            reverse_rank_order(0..3, 3, |i| i, &mut Some(&mut fresh)),
            Some(vec![2, 1, 0])
        );
    }
}

#[cfg(test)]
mod checked_chain_base_tests {
    use super::*;
    use crate::{json::id_ref, model::Model};

    fn fixture() -> ResolvedModel {
        let mut model = Model::new();
        let parsed=model.add_source("chain-bases.kerml", "function F {in p; return r;} class Holder {feature fnMember:F {end feature terminal;}} feature h:Holder; feature chain chains h.fnMember; feature next subsets chain {end feature q;} feature call=chain(1);");
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        ResolvedModel::build(&model)
    }
    #[test]
    fn static_producer_rebuilds_positional_evidence_before_sharing_its_prefix() {
        for format in [
            crate::model::GraphFormat::LegacyV2,
            crate::model::GraphFormat::CanonicalV3,
        ] {
            let mut model = Model::with_graph_format(format);
            let parsed = model.add_source(
                "producer-evidence.kerml",
                "class A {end feature a;} class B specializes A {end feature b;}",
            );
            assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
            let mut r = ResolvedModel::build(&model);
            let a = r.resolve_qualified("A::a").unwrap();
            let b = r.resolve_qualified("B::b").unwrap();
            r.b.ensure_positional_redefinitions();
            assert!(r.b.positional_redefinitions.as_ref().unwrap().targets[&b.0].contains(&a.0));
            // A compatibility cache is not the producer's new certificate.
            r.b.positional_redefinitions
                .as_mut()
                .unwrap()
                .targets
                .clear();
            let relationships = r.implied_relationships(b);
            assert!(relationships.iter().any(|at| {
                r.b.elements[at.0].ty == "Redefinition"
                    && specialization_target(&r.b.elements[at.0]) == Some(r.element_id(a))
            }));
            let boundary = r.b.implied.as_ref().unwrap().owned_results_from;
            let prefix =
                r.b.static_specialization_prefix(&HashMap::new(), true, Some(&mut 0))
                    .unwrap();
            assert!(
                super::super::dynamic_invocations::capture_static_prefix(
                    &mut r.b,
                    prefix,
                    Some(boundary),
                    &mut 0,
                )
                .is_ok()
            );
        }
    }
    #[test]
    fn checked_one_hop_chain_bases_supply_static_positional_ends() {
        let mut r = fixture();
        let chain = r.resolve_qualified("chain").unwrap().0;
        let last = r.resolve_qualified("Holder::fnMember").unwrap().0;
        let p = r.resolve_qualified("Holder::fnMember::terminal").unwrap().0;
        let q = r.resolve_qualified("next::q").unwrap().0;
        let prefix =
            r.b.static_specialization_prefix(&HashMap::new(), true, Some(&mut 0))
                .unwrap();
        assert_eq!(prefix.chain_bases.targets[&chain], last);
        assert!(prefix.planner_bases[&chain].contains(&last));
        assert!(prefix.specializations[&r.b.elements[chain].id].contains(&r.b.elements[last].id));
        assert!(prefix.positional.targets[&q].contains(&p));
        let supers = super::super::type_relations::TypeRelations::default()
            .checked_supertypes(&mut r.b, chain, true, &mut 0)
            .unwrap();
        assert_eq!(supers, vec![last]);
        // Admission remains separate while owned-callee and whole-family
        // qualification are reviewed; this prerequisite does not bypass guard.
        assert!(matches!(
            super::super::dynamic_invocations::prepare(
                &mut r.b,
                prefix,
                &HashSet::new(),
                None,
                &mut 0
            ),
            Err(super::super::dynamic_invocations::Refusal::Incomplete)
        ));
    }
    #[test]
    fn invalid_chain_never_supplies_a_partial_final_target() {
        for malformed in 0..5 {
            let mut r = fixture();
            let chain = r.resolve_qualified("chain").unwrap().0;
            let q = r.resolve_qualified("next::q").unwrap().0;
            let last = r.resolve_qualified("Holder::fnMember").unwrap().0;
            let relations: Vec<_> = r.b.elements[chain]
                .owned_relationships
                .iter()
                .copied()
                .filter(|&e| r.b.elements[e].ty == "FeatureChaining")
                .collect();
            match malformed {
                0 => {
                    r.b.set(relations[0], "chainingFeature", serde_json::json!(null))
                }
                1 => {
                    let id = r.b.elements[last].id;
                    r.b.set(relations[0], "featureChained", id_ref(id));
                }
                2 => {
                    let id = r.b.elements[chain].id;
                    r.b.set(
                        relations[1],
                        "target",
                        crate::properties::Atom::Array(vec![id_ref(id)]),
                    );
                }
                3 => r.b.elements[chain].owned_relationships.push(relations[0]),
                4 => {
                    let f = r.resolve_qualified("F").unwrap().0;
                    let id = r.b.elements[f].id;
                    r.b.set(relations[1], "chainingFeature", id_ref(id));
                }
                _ => unreachable!(),
            }
            let prefix =
                r.b.static_specialization_prefix(&HashMap::new(), true, Some(&mut 0))
                    .unwrap();
            assert!(
                prefix.chain_bases.incomplete.contains(&chain),
                "{malformed}"
            );
            assert!(!prefix.chain_bases.targets.contains_key(&chain));
            assert!(!prefix.positional.targets.contains_key(&q));
        }
    }
    #[test]
    fn cached_chain_projection_observes_same_length_endpoint_edits() {
        let mut r = fixture();
        let chain = r.resolve_qualified("chain").unwrap().0;
        let h = r.resolve_qualified("h").unwrap().0;
        let first =
            r.b.static_specialization_prefix(&HashMap::new(), true, Some(&mut 0))
                .unwrap();
        let last = r.b.elements[chain]
            .owned_relationships
            .iter()
            .copied()
            .rfind(|&e| r.b.elements[e].ty == "FeatureChaining")
            .unwrap();
        let id = r.b.elements[h].id;
        r.b.set(last, "chainingFeature", id_ref(id));
        let second =
            r.b.static_specialization_prefix(&HashMap::new(), true, Some(&mut 0))
                .unwrap();
        assert_ne!(first.chain_bases.targets[&chain], h);
        assert_eq!(second.chain_bases.targets[&chain], h);
    }
    #[test]
    fn unchanged_static_append_preserves_chain_authority_and_warm_work() {
        let mut r = fixture();
        let q = r.resolve_qualified("next::q").unwrap().0;
        let p = r.resolve_qualified("Holder::fnMember::terminal").unwrap().0;
        r.b.static_specialization_prefix(&HashMap::new(), true, Some(&mut 0))
            .unwrap();
        let plan = Arc::clone(r.b.supported_implied.as_ref().unwrap());
        r.implied_relationships(ElementRef(q));
        assert!(Arc::ptr_eq(&plan, r.b.supported_implied.as_ref().unwrap()));
        assert_eq!(
            super::super::type_relations::TypeRelations::default()
                .specializes(&mut r.b, q, p, &mut 0),
            super::super::type_relations::RelationFact::Yes
        );
        assert!(Arc::ptr_eq(&plan, r.b.supported_implied.as_ref().unwrap()));
        let mut warm = 0;
        r.b.refresh_supported_chain_evidence(Some(&mut warm))
            .unwrap();
        assert_eq!(warm, 1);
    }
    #[test]
    fn changed_chain_budget_refusal_does_not_refresh_old_stamp() {
        let mut r = fixture();
        let chain = r.resolve_qualified("chain").unwrap().0;
        r.b.static_specialization_prefix(&HashMap::new(), true, Some(&mut 0))
            .unwrap();
        let old = Arc::clone(r.b.supported_implied.as_ref().unwrap());
        let last = r.b.elements[chain]
            .owned_relationships
            .iter()
            .copied()
            .rfind(|&e| r.b.elements[e].ty == "FeatureChaining")
            .unwrap();
        r.b.set(last, "chainingFeature", serde_json::json!(null));
        assert!(
            r.b.refresh_supported_chain_evidence(Some(&mut (crate::eval::MAX_STEPS - 1)))
                .is_none()
        );
        assert!(Arc::ptr_eq(&old, r.b.supported_implied.as_ref().unwrap()));
        assert!(!r.b.supported_chain_evidence_current());
        let prefix =
            r.b.static_specialization_prefix(&HashMap::new(), true, Some(&mut 0))
                .unwrap();
        assert!(prefix.chain_bases.incomplete.contains(&chain));
        assert!(!Arc::ptr_eq(&old, r.b.supported_implied.as_ref().unwrap()));
    }
    #[test]
    fn materialized_chain_positional_rows_do_not_survive_endpoint_mutation() {
        let mut r = fixture();
        let chain = r.resolve_qualified("chain").unwrap().0;
        let q = r.resolve_qualified("next::q").unwrap().0;
        let p = r.resolve_qualified("Holder::fnMember::terminal").unwrap().0;
        let h = r.resolve_qualified("h").unwrap().0;
        let rows = r.implied_relationships(ElementRef(q));
        assert!(rows.iter().any(|e| r.b.elements[e.0].ty == "Redefinition"));
        let last = r.b.elements[chain]
            .owned_relationships
            .iter()
            .copied()
            .rfind(|&e| r.b.elements[e].ty == "FeatureChaining")
            .unwrap();
        let id = r.b.elements[h].id;
        r.b.set(last, "chainingFeature", id_ref(id));
        let fact = super::super::type_relations::TypeRelations::default()
            .specializes(&mut r.b, q, p, &mut 0);
        assert_ne!(
            fact,
            super::super::type_relations::RelationFact::Yes,
            "old physical positional edge is not current evidence"
        );
    }
    #[test]
    fn changed_end_membership_cannot_be_hidden_by_unchanged_chain_targets() {
        let mut r = fixture();
        let q = r.resolve_qualified("next::q").unwrap().0;
        let p = r.resolve_qualified("Holder::fnMember::terminal").unwrap().0;
        r.implied_relationships(ElementRef(q));
        r.b.set(p, "isEnd", serde_json::json!(false));
        let fact = super::super::type_relations::TypeRelations::default()
            .specializes(&mut r.b, q, p, &mut 0);
        assert_ne!(fact, super::super::type_relations::RelationFact::Yes);
        assert!(r.b.value_context_bases(q, &mut 0).is_none());
        let explicit = super::super::type_relations::TypeRelations::default()
            .checked_supertypes(&mut r.b, q, true, &mut 0)
            .unwrap();
        assert!(
            explicit.is_empty(),
            "stale implied rows are outside explicit-only domain"
        );
    }
    #[test]
    fn remapped_static_chain_rows_recertify_without_any_invocation() {
        let mut model = Model::new();
        model.add_source("chain-remap.kerml","class C {feature last {end feature terminal;}} feature h:C; feature chain chains h.last; feature next subsets chain {end feature q;}");
        let mut r = ResolvedModel::build(&model);
        let q = r.resolve_qualified("next::q").unwrap();
        let p = r.resolve_qualified("C::last::terminal").unwrap();
        let before = r.implied_relationships(q);
        let relation = before
            .into_iter()
            .find(|e| r.element_type(*e) == "Redefinition")
            .unwrap();
        let relation_id = r.element_id(relation);
        let new = Uuid::new_v4();
        r.override_ids(&HashMap::from([(r.element_id(p), new)]));
        r.implied_relationships(q);
        let fact = super::super::type_relations::TypeRelations::default()
            .specializes(&mut r.b, q.0, p.0, &mut 0);
        assert_eq!(fact, super::super::type_relations::RelationFact::Yes);
        assert_eq!(r.element_id(relation), relation_id);
        assert!(r.b.value_context_bases(q.0, &mut 0).unwrap().contains(&p.0));
    }
    #[test]
    fn name_only_role_change_revokes_physical_and_positional_authority() {
        let mut model = Model::new();
        model.add_library_source(
            "chain-role.kerml",
            "standard library package Performances {expr evaluations;}",
        );
        model.add_source("chain-role-user.kerml", "feature answer=1;");
        let mut r = ResolvedModel::build(&model);
        let literal = r
            .user_elements()
            .find(|&e| r.element_type(e) == "LiteralInteger")
            .unwrap();
        let role = r.resolve_qualified("Performances::evaluations").unwrap();
        let rows = r.implied_relationships(literal);
        let edge = rows
            .into_iter()
            .find(|e| r.element_type(*e) == "Subsetting")
            .unwrap();
        let edge_id = r.element_id(edge);
        assert!(r.b.physical_static_authority_current());
        let row_revision = r.b.elements.observe_revision();
        let role_id = r.element_id(role);
        for at in 0..r.b.lib_qnames.len() {
            let (id, parts) = &mut r.b.lib_qnames[at];
            if *id == role_id {
                *parts = vec!["Performances".into(), "renamed".into()];
            }
        }
        assert!(r.b.elements.revision().unwrap().same_as(&row_revision));
        assert!(!r.b.physical_static_authority_current());
        assert!(r.b.effective_positional_redefinitions().is_none());
        r.b.supported_implied = None;
        assert!(!r.b.physical_static_authority_current());
        assert_ne!(
            super::super::type_relations::TypeRelations::default()
                .specializes(&mut r.b, literal.0, role.0, &mut 0),
            super::super::type_relations::RelationFact::Yes
        );
        assert_eq!(r.element_id(edge), edge_id);
        assert!(!r.b.static_chain_row_current(edge.0));
    }
    #[test]
    fn missing_required_authority_cannot_leave_a_positional_cache_current() {
        let mut r = fixture();
        let q = r.resolve_qualified("next::q").unwrap().0;
        assert!(r.b.ensure_positional_redefinitions_with_budget(&mut 0));
        assert!(r.b.completed_positional_targets(q).is_some());
        r.b.supported_implied = None;
        assert!(r.b.completed_positional_targets(q).is_none());
        r.b.refresh_supported_chain_evidence(Some(&mut 0)).unwrap();
        assert!(r.b.positional_redefinitions.is_none());
        assert!(r.b.ensure_positional_redefinitions_with_budget(&mut 0));
        assert!(r.b.completed_positional_targets(q).is_some());
    }
    #[test]
    fn virtual_chain_graph_refreshes_even_when_physical_recipes_are_unchanged() {
        let mut model = Model::new();
        model.add_source(
            "chain-virtual.kerml",
            "class C {feature a; feature b;} feature h:C; feature chain chains h.a;",
        );
        let mut r = ResolvedModel::build(&model);
        let chain = r.resolve_qualified("chain").unwrap();
        let old = r.resolve_qualified("C::a").unwrap();
        let new = r.resolve_qualified("C::b").unwrap();
        assert!(r.conforms_with_implied(chain, old));
        let count = r.b.elements.len();
        let last = *r.b.elements[chain.0]
            .owned_relationships
            .iter()
            .rfind(|&&at| r.b.elements[at].ty == "FeatureChaining")
            .unwrap();
        let id = r.element_id(new);
        r.b.set(last, "chainingFeature", id_ref(id));
        assert!(!r.conforms_with_implied(chain, old));
        assert!(r.conforms_with_implied(chain, new));
        assert_eq!(r.b.elements.len(), count);
    }
    #[test]
    fn static_chain_prerequisites_cannot_depend_on_semantic_tail_features() {
        for intermediate in [false, true] {
            let mut r = fixture();
            let chain = r.resolve_qualified("chain").unwrap().0;
            let h = r.resolve_qualified("h").unwrap().0;
            r.implied_relationships(ElementRef(chain));
            let boundary = r.b.explicit_len();
            let mut suffix = r.b.elements[h].clone();
            suffix.id = Uuid::new_v4();
            suffix.owning_relationship = None;
            let id = suffix.id;
            r.b.elements.push(suffix);
            let links: Vec<_> = r.b.elements[chain]
                .owned_relationships
                .iter()
                .copied()
                .filter(|&at| r.b.elements[at].ty == "FeatureChaining")
                .collect();
            r.b.set(
                links[usize::from(!intermediate)],
                "chainingFeature",
                id_ref(id),
            );
            let bases = r.b.checked_chain_bases(boundary, Some(&mut 0)).unwrap();
            assert!(bases.incomplete.contains(&chain));
            assert!(!bases.targets.contains_key(&chain));
        }
    }
    #[test]
    fn chain_projection_budget_refusal_does_not_publish_a_prefix() {
        let mut r = fixture();
        let mut steps = crate::eval::MAX_STEPS;
        assert!(
            r.b.static_specialization_prefix(&HashMap::new(), true, Some(&mut steps))
                .is_none()
        );
        assert!(r.b.implied.is_none());
        assert!(r.b.positional_redefinitions.is_none());
        let chain = r.resolve_qualified("chain").unwrap().0;
        let prefix =
            r.b.static_specialization_prefix(&HashMap::new(), true, Some(&mut 0))
                .unwrap();
        assert!(prefix.chain_bases.targets.contains_key(&chain));
    }
}

#[cfg(test)]
mod minimizer_witness_tests {
    use crate::{json::ResolvedModel, model::Model};

    #[test]
    fn direct_witness_skips_irrelevant_branches_and_keeps_order() {
        let mut m = Model::new();
        assert!(
            m.add_source(
                "witness.kerml",
                "class Goal; class Wide; class A specializes Goal, Wide;"
            )
            .diagnostics
            .is_empty()
        );
        let mut r = ResolvedModel::build(&m);
        let a = r.resolve_qualified("A").unwrap().0;
        let goal = r.resolve_qualified("Goal").unwrap().0;
        let wide = r.resolve_qualified("Wide").unwrap().0;
        let edge = (
            a,
            (
                "Subclassification",
                "subclassifier",
                "superclassifier",
                r.b.elements[goal].id,
            ),
        );
        let owners = r.b.specialization_relation_owners();
        let limit = r.b.explicit_len();
        let (keep, graph) =
            r.b.required_specialization_edges_with_fixed_prefix(
                &[edge],
                0,
                limit,
                &owners,
                Some(&mut 0),
            )
            .unwrap();
        assert_eq!(keep, [false]);
        assert_eq!(
            graph[&r.b.elements[a].id],
            [r.b.elements[goal].id, r.b.elements[wide].id]
        );
        let (keep, _) =
            r.b.required_specialization_edges_with_fixed_prefix(
                &[edge],
                1,
                limit,
                &owners,
                Some(&mut 0),
            )
            .unwrap();
        assert_eq!(
            keep,
            [true],
            "fixed prefix must survive even a direct witness"
        );
    }

    #[test]
    fn disabled_candidate_is_not_its_own_witness_and_cycles_keep_an_anchor() {
        let mut m = Model::new();
        assert!(
            m.add_source(
                "cycle.kerml",
                "class Goal; class A specializes B; class B specializes A;"
            )
            .diagnostics
            .is_empty()
        );
        let mut r = ResolvedModel::build(&m);
        let a = r.resolve_qualified("A").unwrap().0;
        let b = r.resolve_qualified("B").unwrap().0;
        let goal = r.resolve_qualified("Goal").unwrap().0;
        let edge = |owner| {
            (
                owner,
                (
                    "Subclassification",
                    "subclassifier",
                    "superclassifier",
                    r.b.elements[goal].id,
                ),
            )
        };
        let candidates = [edge(a), edge(b)];
        let owners = r.b.specialization_relation_owners();
        let limit = r.b.explicit_len();
        let (keep, _) =
            r.b.required_specialization_edges_with_fixed_prefix(
                &candidates[..1],
                0,
                limit,
                &owners,
                Some(&mut 0),
            )
            .unwrap();
        assert_eq!(keep, [true]);
        let (keep, graph) =
            r.b.required_specialization_edges_with_fixed_prefix(
                &candidates,
                0,
                limit,
                &owners,
                Some(&mut 0),
            )
            .unwrap();
        assert_eq!(keep.iter().filter(|&&keep| keep).count(), 1);
        for owner in [a, b] {
            assert!(
                graph[&r.b.elements[owner].id]
                    .contains(&r.b.elements[if owner == a { b } else { a }].id)
            );
        }
    }
}

#[cfg(test)]
mod owned_typing_requirement_tests {
    use super::*;
    use crate::{
        json::id_ref,
        model::{GraphFormat, Model},
    };

    const LIB: &str = "standard library package Base { classifier Anything; datatype DataValue specializes Anything; feature things : Anything; feature dataValues : DataValue subsets things; } standard library package Occurrences { class Occurrence specializes Base::Anything; feature occurrences : Occurrence subsets Base::things; } standard library package Objects { struct Object specializes Occurrences::Occurrence; feature objects : Object subsets Occurrences::occurrences; }";

    fn fixture(format: GraphFormat) -> ResolvedModel {
        let mut model = Model::with_graph_format(format);
        assert!(
            model
                .add_library_source("typed-roles.kerml", LIB)
                .diagnostics
                .is_empty()
        );
        assert!(model.add_source("typed-features.kerml", "struct O; class C; datatype D; feature object : O; feature occurrence : C; feature datum : D; feature inherited subsets object;").diagnostics.is_empty());
        ResolvedModel::build(&model)
    }
    fn names(r: &ResolvedModel) -> HashMap<String, Uuid> {
        r.b.lib_qnames
            .iter()
            .map(|(id, name)| (name.join("::"), *id))
            .collect()
    }
    fn targets(r: &mut ResolvedModel, owner: usize) -> Vec<Uuid> {
        let plan = r.b.supported_implied_specializations(&names(r), true);
        plan.candidates
            .iter()
            .filter_map(|((source, edge), _)| (*source == owner).then_some(edge.3))
            .collect()
    }
    fn typing(r: &ResolvedModel, owner: usize) -> usize {
        *r.b.elements[owner]
            .owned_relationships
            .iter()
            .find(|&&rel| r.b.elements[rel].ty == "FeatureTyping")
            .unwrap()
    }
    #[test]
    fn canonical_owned_typings_add_each_applicable_obligation_before_reduction() {
        for format in [GraphFormat::LegacyV2, GraphFormat::CanonicalV3] {
            let mut r = fixture(format);
            for (name, kinds) in [
                (
                    "object",
                    vec!["Objects::objects", "Occurrences::occurrences"],
                ),
                ("occurrence", vec!["Occurrences::occurrences"]),
                ("datum", vec!["Base::dataValues"]),
            ] {
                let owner = r.resolve_qualified(name).unwrap();
                let obligations = targets(&mut r, owner.0);
                for role in kinds {
                    let role = r.resolve_qualified(role).unwrap();
                    assert_eq!(
                        obligations.contains(&r.element_id(role)),
                        format == GraphFormat::CanonicalV3,
                        "{format:?} {name}"
                    );
                }
            }
            let inherited = r.resolve_qualified("inherited").unwrap();
            let object_role = r.resolve_qualified("Objects::objects").unwrap();
            assert!(!targets(&mut r, inherited.0).contains(&r.element_id(object_role)));
            if format == GraphFormat::CanonicalV3 {
                let object = r.resolve_qualified("object").unwrap();
                let object_id = r.element_id(object_role);
                let emitted = r.implied_relationships(object);
                assert_eq!(
                    emitted
                        .iter()
                        .filter(|e| specialization_target(&r.b.elements[e.0]) == Some(object_id))
                        .count(),
                    1
                );
                assert!(r.conforms_with_implied(inherited, object_role));
            }
        }
    }
    #[test]
    fn duplicate_typing_obligations_preserve_minimized_paths_and_recipe_order() {
        let mut r = fixture(GraphFormat::CanonicalV3);
        let object = r.resolve_qualified("object").unwrap();
        let occurrence = r.resolve_qualified("occurrence").unwrap();
        let base = r.resolve_qualified("Base::things").unwrap();
        let objects = r.resolve_qualified("Objects::objects").unwrap();
        let occurrences = r.resolve_qualified("Occurrences::occurrences").unwrap();
        let edge = |owner: ElementRef, target: ElementRef| {
            (
                owner.0,
                (
                    "Subsetting",
                    "subsettingFeature",
                    "subsettedFeature",
                    r.element_id(target),
                ),
            )
        };
        // Repeated requirements interleave with both stronger obligations and
        // a feature cycle; a weaker family may be independently necessary.
        let duplicated = vec![
            edge(object, objects),
            edge(object, base),
            edge(object, occurrence),
            edge(object, objects),
            edge(object, occurrences),
            edge(occurrence, occurrences),
            edge(occurrence, object),
            edge(occurrence, occurrences),
        ];
        let reduced_input = vec![
            edge(object, base),
            edge(object, occurrence),
            edge(object, objects),
            edge(object, occurrences),
            edge(occurrence, object),
            edge(occurrence, occurrences),
        ];
        let owners = r.b.specialization_relation_owners();
        for missing_base_path in [false, true] {
            if missing_base_path {
                // Keep the canonical occurrence role but remove its inherited
                // Base::things path, so that independent weak role must survive.
                let relationships = r.b.elements[occurrences.0].owned_relationships.to_vec();
                for relationship in relationships {
                    if r.b.elements[relationship].ty == "Subsetting" {
                        r.b.set(relationship, "subsettedFeature", json!(null));
                    }
                }
            }
            let (before, before_graph) =
                r.b.required_specialization_edges(&duplicated, r.b.explicit_len(), &owners);
            let (after, after_graph) =
                r.b.required_specialization_edges(&reduced_input, r.b.explicit_len(), &owners);
            let retained_before: Vec<_> = duplicated
                .iter()
                .zip(before)
                .filter_map(|(edge, keep)| keep.then_some(edge))
                .collect();
            let retained_after: Vec<_> = reduced_input
                .iter()
                .zip(after)
                .filter_map(|(edge, keep)| keep.then_some(edge))
                .collect();
            assert_eq!(retained_before, retained_after);
            assert_eq!(before_graph, after_graph);
        }
    }
    #[test]
    fn malformed_owned_typing_never_supplies_an_object_specialization() {
        for mutation in 0..7 {
            let mut r = fixture(GraphFormat::CanonicalV3);
            let object = r.resolve_qualified("object").unwrap();
            let other = r.resolve_qualified("occurrence").unwrap();
            let datum = r.resolve_qualified("D").unwrap();
            let role = r.resolve_qualified("Objects::objects").unwrap();
            let relationship = typing(&r, object.0);
            match mutation {
                0 => r.b.set(
                    relationship,
                    "owningRelatedElement",
                    id_ref(r.element_id(other)),
                ),
                1 => {
                    r.b.set(relationship, "specific", id_ref(r.element_id(other)))
                }
                2 => {
                    r.b.set(relationship, "general", id_ref(r.element_id(datum)))
                }
                3 => r.b.set(
                    relationship,
                    "source",
                    crate::properties::Atom::Array(vec![id_ref(r.element_id(other))]),
                ),
                4 => r.b.set(relationship, "type", id_ref(r.element_id(other))),
                5 => {
                    r.b.set(
                        relationship,
                        "owningRelatedElement",
                        id_ref(r.element_id(object)),
                    );
                    r.b.elements[object.0].owned_relationships = Vec::new().into();
                }
                _ => {
                    r.b.elements[datum.0].id = r.element_id(object);
                    r.b.id_index = None;
                }
            }
            assert!(
                !targets(&mut r, object.0).contains(&r.element_id(role)),
                "mutation {mutation}"
            );
        }
    }
    #[test]
    fn typed_roles_require_unique_loaded_feature_identities() {
        for role_name in [
            "Objects::objects",
            "Occurrences::occurrences",
            "Base::dataValues",
        ] {
            for mutation in 0..4 {
                let mut r = fixture(GraphFormat::CanonicalV3);
                let role = r.resolve_qualified(role_name).unwrap();
                let other = r.resolve_qualified("Base::things").unwrap();
                let mut configuration = names(&r);
                match mutation {
                    0 => {
                        configuration.remove(role_name);
                    }
                    1 => r.b.elements[role.0].ty = "Class",
                    2 => r.b.lib_qnames.push((
                        r.element_id(other),
                        role_name.split("::").map(str::to_owned).collect(),
                    )),
                    _ => {
                        configuration.insert(role_name.into(), r.element_id(other));
                    }
                }
                let plan = r.b.supported_implied_specializations(&configuration, false);
                assert!(
                    !plan.expression_targets.contains_key(role_name),
                    "{role_name} mutation {mutation}"
                );
            }
        }
    }
    #[test]
    fn changed_typing_cannot_reuse_old_static_evidence_and_exhaustion_retries() {
        let mut r = fixture(GraphFormat::CanonicalV3);
        let object = r.resolve_qualified("object").unwrap();
        let datatype = r.resolve_qualified("D").unwrap();
        let role = r.resolve_qualified("Base::dataValues").unwrap();
        let relationship = typing(&r, object.0);
        r.implied_relationships(object);
        assert!(r.b.physical_static_authority_current());
        r.b.set(relationship, "type", id_ref(r.element_id(datatype)));
        assert!(!r.b.physical_static_authority_current());
        r.b.supported_implied = None;
        let names = names(&r);
        let mut exhausted = crate::eval::MAX_STEPS;
        assert!(
            r.b.supported_implied_specializations_with_budget(&names, true, Some(&mut exhausted))
                .is_none()
        );
        assert!(r.b.supported_implied.is_none());
        let plan =
            r.b.supported_implied_specializations_with_budget(&names, true, Some(&mut 0))
                .unwrap();
        assert!(
            plan.candidates
                .iter()
                .any(|((source, edge), _)| *source == object.0 && edge.3 == r.element_id(role))
        );
        assert!(!r.b.physical_static_authority_current());
    }
}

#[cfg(test)]
mod binary_role_tests {
    use super::*;
    use crate::model::{GraphFormat, Model};

    const LIB: &str = "standard library package Connections {
        connection def Connection;
        connection def BinaryConnection :> Connection { end source; end target; }
        connection connections : Connection;
        connection binaryConnections : BinaryConnection;
    }
    standard library package Interfaces {
        interface def Interface;
        interface def BinaryInterface :> Interface { end port a; end port b; }
        interface interfaces : Interface;
        interface binaryInterfaces : BinaryInterface;
    }";
    const USER: &str = "connection def CD { end a; end b; }
        interface def ID { end port a; end port b; }
        connection cu { end a; end b; }
        interface iu { end port a; end port b; }
        ref decoy;";

    #[test]
    fn binary_roles_require_canonical_loaded_identity_and_kind() {
        for format in [GraphFormat::LegacyV2, GraphFormat::CanonicalV3] {
            for (role, owner) in BINARY_ROLES.iter().zip(["CD", "ID", "cu", "iu"]) {
                for mode in 0..7 {
                    let mut model = Model::with_graph_format(format);
                    model.add_library_source("binary.sysml", LIB);
                    model.add_source("user.sysml", USER);
                    assert!(
                        !model.has_errors(),
                        "{:?}",
                        model
                            .units()
                            .iter()
                            .flat_map(|unit| &unit.diagnostics)
                            .collect::<Vec<_>>()
                    );
                    let mut r = ResolvedModel::build(&model);
                    let target = r.resolve_qualified(role.0).unwrap();
                    let receiver = r.resolve_qualified(owner).unwrap();
                    let decoy = r.resolve_qualified("decoy").unwrap();
                    let target_id = r.element_id(target);
                    let mut names: HashMap<_, _> =
                        r.b.lib_qnames
                            .iter()
                            .map(|(id, parts)| (parts.join("::"), *id))
                            .collect();
                    match mode {
                        0 => {}
                        1 => {
                            names.remove(role.0);
                        }
                        2 => {
                            names.insert(role.0.into(), r.element_id(decoy));
                        }
                        3 => {
                            r.b.lib_qnames.push((
                                r.element_id(decoy),
                                role.0.split("::").map(str::to_owned).collect(),
                            ));
                        }
                        4 => {
                            r.b.elements[decoy.0].id = target_id;
                        }
                        5 => {
                            r.b.elements[target.0].ty = "Feature";
                        }
                        6 => {
                            names.insert(
                                role.0.into(),
                                Uuid::new_v5(&Uuid::NAMESPACE_OID, b"unloaded binary role"),
                            );
                        }
                        _ => unreachable!(),
                    }
                    r.b.id_index = None;
                    r.b.supported_implied = None;
                    let plan = r.b.supported_implied_specializations(&names, false);
                    assert_eq!(
                        plan.expression_targets.contains_key(role.0),
                        mode == 0,
                        "{} mode {mode}",
                        role.0
                    );
                    assert_eq!(
                        plan.candidates
                            .iter()
                            .any(|((source, edge), _)| *source == receiver.0 && edge.3 == target_id),
                        mode == 0,
                        "{owner} mode {mode}"
                    );
                    if matches!(mode, 0 | 3 | 4 | 5) {
                        assert_eq!(
                            r.b.binary_lookup_target(target.0, role.0),
                            mode == 0,
                            "lookup {} mode {mode}",
                            role.0
                        );
                    }
                }
            }
        }
    }
}
