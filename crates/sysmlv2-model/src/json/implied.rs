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
use crate::flat::ListsByRow;
use crate::layered::{IdMap, IdSet};
use crate::lift::{def_kind_of, usage_kind_of};
use crate::metaclass::conforms;
use crate::metaclass::is_a;
use serde_json::json;
use std::collections::HashMap;
use std::sync::{Arc, OnceLock};
use sysmlv2_syntax::ast::{Dialect, UsageKind};
use uuid::Uuid;

/// One element's implied specializations: the library roles (qualified
/// names), the relationship metaclass, its source and target keys, and
/// the explicit metaclasses that cover them.
type ImpliedBases<'a> = (Vec<&'static str>, &'a str, &'a str, &'a str, &'a [&'a str]);

type SpecializationGraph = crate::id_graph::IdMap<Uuid, Vec<Uuid>>;
type StaticPlannerBases = (IdMap<usize, Vec<usize>>, IdSet<usize>);
/// The direct bases a static prefix keeps: a build's own rows' over the
/// frozen table its prepared library's plans give, and the types whose bases
/// are incomplete.
type PlannedBases = (crate::layered::LayeredMap<usize, Vec<usize>>, IdSet<usize>);

pub(super) type PlannedEdge = (&'static str, &'static str, &'static str, Uuid);

pub(super) type RetainedTypings = IdMap<usize, Vec<(&'static str, Uuid)>>;

/// The immutable supported library/variation plan. The positional graph and
/// materialized relationship graph share this calculation, but own any later
/// positional edges independently.
pub(super) struct SupportedImpliedSpecializations {
    candidates: Candidates,
    /// The final specialization graph and the retained targets by owner. A
    /// prepared library's plan keeps both frozen, and a plan extending it adds
    /// a build's own entries over them (see [`super::LibraryPlans`]).
    graph: crate::id_graph::IdGraph,
    by_owner: RetainedByOwner,
    typing_by_owner: OnceLock<Arc<RetainedTypings>>,
    library_configuration: bool,
    expression_targets: HashMap<&'static str, Uuid>,
    chain_bases: Arc<super::type_relations::FeatureChainBases>,
    // Validation memo only: the graph stays immutable and the token is the
    // existing row revision, never a separate semantic generation.
    source_rows: std::sync::Mutex<crate::layered::Revision>,
    source_names: crate::layered::Revision,
}

/// A plan's retained targets by owner row: a build's own owners' over the
/// lists of the prepared library's plan, which are laid out by row once
/// the plan is frozen (see [`ListsByRow`]) and shared by the plans that
/// extend it. A frozen list is never empty — an owner has a list for a
/// target it retained — so an empty one is a row of another table the
/// lists are laid out on (see [`Self::lay_on`]) that has none here.
#[derive(Clone, Default)]
struct RetainedByOwner {
    frozen: Arc<ListsByRow<Uuid>>,
    own: IdMap<usize, Vec<Uuid>>,
}

impl RetainedByOwner {
    fn get(&self, owner: usize) -> Option<&[Uuid]> {
        match self.own.get(&owner) {
            Some(targets) => Some(targets),
            None => self.frozen.get(owner).filter(|targets| !targets.is_empty()),
        }
    }
    /// Retain `target` for `owner`, after the targets it has.
    fn push(&mut self, owner: usize, target: Uuid) {
        let frozen = &self.frozen;
        self.own
            .entry(owner)
            .or_insert_with(|| frozen.get(owner).map(<[Uuid]>::to_vec).unwrap_or_default())
            .push(target);
    }
    /// Every owner's targets: the frozen lists no own list replaces, by
    /// row, then the own lists.
    fn iter(&self) -> impl Iterator<Item = (usize, &[Uuid])> {
        self.frozen
            .iter()
            .filter(|(owner, targets)| !targets.is_empty() && !self.own.contains_key(owner))
            .chain(
                self.own
                    .iter()
                    .map(|(&owner, targets)| (owner, targets.as_slice())),
            )
    }
    /// The capacity of the own lists: what dropping this table frees (the
    /// frozen lists are shared).
    fn local_capacity(&self) -> usize {
        self.own.capacity()
    }
    /// Lay every list out by row, frozen.
    fn freeze(&mut self) {
        if self.own.is_empty() {
            return;
        }
        let lists: IdMap<usize, Vec<Uuid>> = self
            .iter()
            .map(|(owner, targets)| (owner, targets.to_vec()))
            .collect();
        let rows = lists
            .keys()
            .map(|&owner| owner + 1)
            .max()
            .unwrap_or(0)
            .max(self.frozen.rows());
        self.frozen = Arc::new(ListsByRow::from_map(rows, &lists));
        self.own = IdMap::default();
    }
    /// Lay the frozen lists out on `other`'s rows, sharing its ranks, when
    /// every owner is a row with a list there and no own list lies over
    /// them.
    fn lay_on<U>(&mut self, other: &ListsByRow<U>) {
        if !self.own.is_empty() {
            return;
        }
        if let Some(laid) = self.frozen.laid_on(other) {
            self.frozen = Arc::new(laid);
        }
    }
}

impl FromIterator<(usize, Vec<Uuid>)> for RetainedByOwner {
    fn from_iter<I: IntoIterator<Item = (usize, Vec<Uuid>)>>(iter: I) -> Self {
        Self {
            frozen: Arc::default(),
            own: iter.into_iter().collect(),
        }
    }
}

/// A relationship as a planned edge spells it: the kind, the source role
/// and the target role.
type Spelling = (&'static str, &'static str, &'static str);

/// A plan's candidate edges with whether each was retained, in the order a
/// plan of every row lists them: the kinds' and variants' requirements, then
/// the succession endpoints'. A plan extending a prepared library's lists the
/// library plan's before its own in each part, without copying them.
///
/// The own candidates are held in columns — an owner row, a spelling's
/// index and a target each — rather than as the planner's rows of owner and
/// edge: a library's plan holds eighty thousand of them, and a row of three
/// string slices and a padded tuple is three times a column entry's width.
pub(super) struct Candidates {
    library: Option<Arc<SupportedImpliedSpecializations>>,
    /// Each own candidate's owner row.
    owners: Vec<u32>,
    /// Each own candidate's relationship, as an index into `spellings`.
    spelled: Vec<u8>,
    /// Each own candidate's target.
    targets: Vec<Uuid>,
    /// The distinct spellings the own candidates use, in order of first use.
    spellings: Vec<Spelling>,
    /// The own candidates before this index are the kinds' and variants'
    /// requirements, the rest the succession endpoints'.
    kinds: usize,
    retained: Vec<bool>,
}

/// A candidate edge as a plan lists it — its owner row and its edge — and
/// whether it was retained.
type Candidate = ((usize, PlannedEdge), bool);

impl Candidates {
    /// The plan's own candidates `own`, the first `kinds` of them the kinds'
    /// and variants' requirements, with `retained` saying which of them the
    /// minimizer kept, over `library`'s when the plan extends a prepared
    /// library's.
    fn new(
        library: Option<Arc<SupportedImpliedSpecializations>>,
        own: Vec<(usize, PlannedEdge)>,
        kinds: usize,
        retained: Vec<bool>,
    ) -> Self {
        debug_assert_eq!(own.len(), retained.len());
        let mut spellings: Vec<Spelling> = Vec::new();
        let mut owners = Vec::with_capacity(own.len());
        let mut spelled = Vec::with_capacity(own.len());
        let mut targets = Vec::with_capacity(own.len());
        for (owner, (kind, source, target_role, target)) in own {
            let spelling = (kind, source, target_role);
            let index = match spellings.iter().position(|known| *known == spelling) {
                Some(index) => index,
                None => {
                    spellings.push(spelling);
                    spellings.len() - 1
                }
            };
            // Neither bound is reached: no build holds 2^32 rows, and the
            // planner spells only the four relationships of
            // `SPELLED_RELATIONSHIPS` (a fifth spelling still fits the byte;
            // the table's own length bounds the wire form). A stop here is
            // preferred to a column holding a wrong owner or spelling.
            owners.push(u32::try_from(owner).expect("a row index fits the owner column"));
            spelled.push(u8::try_from(index).expect("the planner spells few relationships"));
            targets.push(target);
        }
        Self {
            library,
            owners,
            spelled,
            targets,
            spellings,
            kinds,
            retained,
        }
    }
    /// The own candidates `range`, each with whether it was retained.
    fn part(&self, range: std::ops::Range<usize>) -> impl Iterator<Item = Candidate> + '_ {
        range.map(move |i| {
            let (kind, source, target_role) = self.spellings[usize::from(self.spelled[i])];
            let edge = (kind, source, target_role, self.targets[i]);
            ((self.owners[i] as usize, edge), self.retained[i])
        })
    }
    /// Every candidate, with whether it was retained, in the plan's order.
    pub(super) fn iter(&self) -> impl Iterator<Item = Candidate> + '_ {
        // (with no library plan beneath, the library's parts are empty
        // ranges of this plan's own columns)
        let library = self.library.as_deref().map(|plan| &plan.candidates);
        let (kinds, end) = library.map_or((0, 0), |c| (c.kinds, c.owners.len()));
        let library = library.unwrap_or(self);
        library
            .part(0..kinds)
            .chain(self.part(0..self.kinds))
            .chain(library.part(kinds..end))
            .chain(self.part(self.kinds..self.owners.len()))
    }
    /// The plan's own candidates (a library plan's are not), in order.
    pub(super) fn own(&self) -> impl Iterator<Item = Candidate> + '_ {
        self.part(0..self.owners.len())
    }
    pub(super) fn len(&self) -> usize {
        self.owners.len()
            + self
                .library
                .as_ref()
                .map_or(0, |plan| plan.candidates.owners.len())
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

/// A prepared library's own materialized rows (its elements' static implied
/// relationships, made once when it was prepared), as a build on the
/// library reads them: they lie in the frozen prefix from
/// `Builder::lib_implied_from`, owned through the prefix ownership view,
/// and the build materializes its own rows after them. Owned results stay a
/// build's own: a build on the library materializes its library's
/// expressions' results with its own, as a build from source does.
#[derive(Clone, serde::Serialize, serde::Deserialize)]
pub(super) struct PrefixImplied {
    /// The specialization edges the library's materialized rows add to the
    /// planned graph — its static implied relationships and positional
    /// redefinitions — from the owner's id to the target's, in row order.
    pub(super) edges: Vec<(Uuid, Uuid)>,
    /// The rows these edges change in the planned graph (see
    /// [`Self::graph_over`]), made by the first build that materializes over
    /// a plan's frozen graph and shared by every build over that graph. Not
    /// serialized: a decoded library's builds make their own.
    #[serde(skip)]
    graph: Arc<std::sync::Mutex<Option<PrefixOverlay>>>,
    /// The materialized rows as the fixed recipes a build from source hands
    /// its dynamic planner (see [`Builder::prefix_static_candidates`]), made
    /// by the first build that plans and shared by every build on the
    /// library while its frozen rows are unwritten.
    #[serde(skip)]
    candidates: std::sync::OnceLock<Arc<Vec<(usize, PlannedEdge)>>>,
}

/// The rows a prefix's edges change in a plan's frozen specialization graph,
/// kept by the frozen graph's identity: the frozen graph with the edges in
/// it is these rows over it. Most of the edges are in the frozen graph
/// already (the plan retained them), so the rows are few.
struct PrefixOverlay {
    base: Arc<crate::id_graph::Frozen>,
    rows: Arc<crate::id_graph::Overlay>,
    /// The edges' distinct sources, sorted, for the rows a build's own plan
    /// lays over the frozen graph: few of those rows are a source's.
    sources: Arc<Vec<Uuid>>,
}

impl PrefixImplied {
    /// The rows this prefix's edges change in the frozen graph `base`, and
    /// the edges' sources: made once per frozen graph and shared.
    fn graph_over(
        &self,
        base: &Arc<crate::id_graph::Frozen>,
    ) -> (Arc<crate::id_graph::Overlay>, Arc<Vec<Uuid>>) {
        let mut cell = self.graph.lock().unwrap();
        if let Some(kept) = cell.as_ref().filter(|kept| Arc::ptr_eq(&kept.base, base)) {
            return (Arc::clone(&kept.rows), Arc::clone(&kept.sources));
        }
        // A row takes an edge's target once, after the targets it has: a
        // row the edges add nothing to stays the frozen graph's.
        let mut rows = SpecializationGraph::default();
        for &(source, target) in &self.edges {
            let present = rows
                .get(&source)
                .map(Vec::as_slice)
                .or_else(|| base.get(&source))
                .is_some_and(|targets| targets.contains(&target));
            if !present {
                rows.entry(source)
                    .or_insert_with(|| base.get(&source).map(<[Uuid]>::to_vec).unwrap_or_default())
                    .push(target);
            }
        }
        let mut sources: Vec<Uuid> = self.edges.iter().map(|&(source, _)| source).collect();
        sources.sort_unstable();
        sources.dedup();
        let rows = Arc::new(crate::id_graph::Overlay::new(base, rows));
        let sources = Arc::new(sources);
        *cell = Some(PrefixOverlay {
            base: Arc::clone(base),
            rows: Arc::clone(&rows),
            sources: Arc::clone(&sources),
        });
        (rows, sources)
    }

    /// The targets of this prefix's edges from `source`, each once, in the
    /// edges' order.
    fn targets_from(&self, source: Uuid) -> Vec<Uuid> {
        let mut targets = Vec::new();
        for &(from, target) in &self.edges {
            if from == source && !targets.contains(&target) {
                targets.push(target);
            }
        }
        targets
    }
}

impl Builder {
    /// The first row a build materializes static implied relationships
    /// for: past the library's rows when the library carries its own
    /// materialized rows (they lie in the prefix), else every source row.
    pub(super) fn own_rows_start(&self) -> usize {
        if self.prefix_implied.is_some() {
            self.lib_boundary
        } else {
            0
        }
    }

    /// Make this library-only build's materialized rows the prepared
    /// library's own: the rows stay as the last of the frozen prefix, its
    /// ownership view becomes the prefix view every build on the library
    /// layers over, and the build-side state that produced them is
    /// cleared, so that the frozen builder reads as unmaterialized to the
    /// builds that start from it. Nothing changes when the build
    /// materialized nothing.
    /// The prepared library's own materialized rows as the fixed recipes a
    /// build from source hands its dynamic planner (the library's static
    /// implied relationships come first among them there): owner and edge,
    /// in row order; empty without such rows.
    pub(super) fn prefix_static_candidates(&self) -> Arc<Vec<(usize, PlannedEdge)>> {
        let (Some(prefix), Some(view)) = (&self.prefix_implied, &self.prefix_ownership) else {
            return Arc::default();
        };
        let make = || {
            // A static recipe writes its source and its target only.
            const KEYS: [(&str, &str); 7] = [
                ("subclassifier", "superclassifier"),
                ("typedFeature", "type"),
                ("subsettingFeature", "subsettedFeature"),
                ("redefiningFeature", "redefinedFeature"),
                ("referencingFeature", "referencedFeature"),
                ("crossingFeature", "crossedFeature"),
                ("specific", "general"),
            ];
            let mut out = Vec::new();
            for i in self.lib_implied_from..self.lib_boundary {
                let row = &self.elements[i];
                if !is_a!(row, "Specialization") {
                    continue;
                }
                let Some(owner) = view.generated_relationship_owner(i) else {
                    continue;
                };
                let Some(&(source_key, target_key)) = KEYS
                    .iter()
                    .find(|(source, _)| row.props.get(source).is_some())
                else {
                    continue;
                };
                let Some(target) = row.props.get(target_key).and_then(|v| v.as_reference()) else {
                    continue;
                };
                out.push((owner, (row.ty, source_key, target_key, target)));
            }
            Arc::new(out)
        };
        if self.elements.base_untouched() {
            Arc::clone(prefix.candidates.get_or_init(make))
        } else {
            make()
        }
    }

    /// The specialization edges the prepared library's own materialized
    /// rows add to the planned graph, from the owner's id to the target's,
    /// as the rows give them now.
    fn prefix_edges_now(&self) -> Vec<(Uuid, Uuid)> {
        let Some(view) = &self.prefix_ownership else {
            return Vec::new();
        };
        prefix_edges(self, view, self.lib_implied_from, self.lib_boundary)
    }

    pub(crate) fn seal_prefix_semantics(&mut self) {
        let Some(from) = self.implied_from.take() else {
            return;
        };
        let table = self
            .implied
            .take()
            .expect("materialized rows have their table");
        let view = self
            .semantic_ownership
            .take()
            .expect("materialized rows have their ownership view");
        let edges = prefix_edges(self, &view, from, self.elements.len());
        self.lib_implied_from = from;
        self.lib_boundary = self.elements.len();
        // The kept lookup graph was built over the source rows: it covers
        // the materialized rows too, so that the snapshot's graph fits the
        // rows it is read for, and the rows are found by id.
        if let Some(mut graph) = self.recorded_lookup_graph.take() {
            graph.cover_rows(self, from);
            self.recorded_lookup_graph = Some(graph);
        }
        self.prefix_ownership = Some(Arc::new(
            Arc::try_unwrap(view).unwrap_or_else(|arc| (*arc).clone()),
        ));
        debug_assert_eq!(
            table.owned_results_from,
            self.elements.len(),
            "a prefix materializes its static rows only"
        );
        self.prefix_implied = Some(Arc::new(PrefixImplied {
            edges,
            graph: Default::default(),
            candidates: Default::default(),
        }));
        self.prefix_static_only = false;
        self.dynamic_graph = None;
        self.supported_implied = None;
        self.positional_redefinitions = None;
        self.library_plans_decided = None;
        self.stored_structure = None;
        self.id_index = None;
        self.publication = super::publication::Control::default();
        self.semantic_ready = false;
    }
}

/// The specialization edges of the materialized rows `from..to`, owned
/// through `view`: from the owner's id to the target's, in row order.
fn prefix_edges(
    b: &Builder,
    view: &super::semantic_ownership::SemanticOwnership,
    from: usize,
    to: usize,
) -> Vec<(Uuid, Uuid)> {
    let mut edges = Vec::new();
    for i in from..to {
        let row = &b.elements[i];
        if !is_a!(row, "Specialization") {
            continue;
        }
        let (Some(target), Some(owner)) = (
            specialization_target(row),
            view.generated_relationship_owner(i),
        ) else {
            continue;
        };
        edges.push((b.elements[owner].id, target));
    }
    edges
}

impl ResolvedModel {
    /// Materialize this library-only build's implied relationships and
    /// owned results and seal them into the prefix a prepared library
    /// keeps (see [`Builder::seal_prefix_semantics`]). Publication is left
    /// suppressed, as a prepared library's build keeps it.
    pub(crate) fn materialize_prefix_semantics(&mut self) {
        self.b.publication.enable();
        // The static implied relationships only: owned results stay a
        // build's own (the planners' witnesses read a library expression as
        // a build from source has it while it plans: without a result).
        self.b.prefix_static_only = true;
        self.ensure_implied();
        self.b.seal_prefix_semantics();
        self.b.publication.suppress();
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
    /// Known explicit and retained implied specialization targets: a
    /// build's own over the frozen table its library's plans give.
    specializations: crate::id_graph::IdGraph,
    static_authority: Arc<SupportedImpliedSpecializations>,
    static_rows: crate::layered::Revision,
    static_owners: IdSet<usize>,
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
pub(super) fn expression_implied_base(ty: &str) -> Option<&'static str> {
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
pub(super) fn additional_expression_base(ty: &str) -> Option<&'static str> {
    if conforms(ty, "BooleanExpression") {
        Some("Performances::booleanEvaluations")
    } else if conforms(ty, "LiteralExpression") {
        Some("Performances::literalEvaluations")
    } else {
        None
    }
}

pub(super) fn invariant_implied_base(negated: bool) -> &'static str {
    if negated {
        "Performances::falseEvaluations"
    } else {
        "Performances::trueEvaluations"
    }
}

/// isNegated is a required Boolean with default false. Only absence uses
/// that default; an explicitly malformed value cannot select either branch.
pub(super) fn invariant_negation(element: &Elem) -> Option<bool> {
    match element.props.get("isNegated") {
        None => Some(false),
        Some(value) => value.as_bool(),
    }
}

/// SysML assert/satisfy obligations accumulate independently of inherited
/// Invariant requirements. A missing narrower role never removes another one.
pub(super) fn assertion_implied_base(negated: bool) -> &'static str {
    if negated {
        "Constraints::negatedConstraintChecks"
    } else {
        "Constraints::assertedConstraintChecks"
    }
}

pub(super) fn satisfaction_implied_base(negated: bool) -> &'static str {
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
/// checkMultiplicitySpecialization (KerML 8.3.3.1.9): every Multiplicity
/// subsets the root feature of all multiplicities, `Base::naturals`, which
/// subsets `dataValues` and so `things`.
const MULTIPLICITY_BASE: &str = "Base::naturals";
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
        | "Occurrences::Occurrence::portions"
        | FEATURE_BASE
        | MULTIPLICITY_BASE
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
    /// library's own, which the plans extending it share. Its retained
    /// flags, grown by the planner's pushes, are cut to their length: a
    /// frozen plan gains none.
    fn into_frozen(mut self) -> Self {
        self.graph.freeze();
        self.by_owner.freeze();
        self.candidates.retained.shrink_to_fit();
        self
    }

    /// Lay the retained targets by owner out on `rows`'s rows, sharing its
    /// ranks, when every owner is a row with a list there: a library's
    /// direct bases have a list on every owner of a retained target.
    pub(super) fn lay_owners_on<U>(&mut self, rows: &ListsByRow<U>) {
        self.by_owner.lay_on(rows);
    }

    /// The wire form of a library's own plan — one with no plan beneath it,
    /// in the library configuration, every edge of which the planner spells
    /// — as a snapshot carries it (see [`super::LibraryPlansWire`]); `None`
    /// for any other plan. The expression targets are not carried: they are
    /// derived again from the library's names when the plan is read back.
    /// The maps are written sorted by key, so the same plan is written the
    /// same way every time.
    pub(super) fn to_wire(&self) -> Option<ImpliedWire> {
        if self.candidates.library.is_some() || !self.library_configuration {
            return None;
        }
        // (each of the plan's spellings as the wire indexes it, once)
        let spelled = self
            .candidates
            .spellings
            .iter()
            .map(|&(kind, source, target)| spelled_relationship_index(kind, source, target))
            .collect::<Option<Vec<u8>>>()?;
        Some(ImpliedWire {
            candidates: CandidateColumns {
                owners: crate::bulk::Ints(
                    self.candidates
                        .owners
                        .iter()
                        .map(|&owner| owner as usize)
                        .collect(),
                ),
                spelled: crate::bulk::Bytes(
                    self.candidates
                        .spelled
                        .iter()
                        .map(|&index| spelled[usize::from(index)])
                        .collect(),
                ),
                ids: crate::bulk::Ids(self.candidates.targets.clone()),
            },
            kinds: self.candidates.kinds,
            retained: self.candidates.retained.clone().into(),
            graph: sorted_by_key(self.graph.iter().map(|(k, v)| (*k, v.to_vec()))).into(),
            by_owner: sorted_by_key(self.by_owner.iter().map(|(k, v)| (k, v.to_vec()))).into(),
            library_configuration: self.library_configuration,
            chain_targets: sorted_by_key(self.chain_bases.targets.iter().map(|(&f, &b)| (f, b)))
                .into(),
            chain_incomplete: crate::bulk::Ints(sorted(
                self.chain_bases.incomplete.iter().copied(),
            )),
        })
    }

    /// A library's own plan read back from its wire form, for the `row_count`
    /// rows at revision `rows` and the names at revision `names`, with the
    /// expression targets `expression_targets` derived from those names,
    /// and the retained targets by owner laid out on `owner_rows`'s rows
    /// (see [`Self::lay_owners_on`]).
    /// `None` when the wire names a relationship the planner does not spell,
    /// a row the library does not have, a configuration other than the
    /// library's, or disagrees with itself.
    pub(super) fn from_wire<U>(
        wire: ImpliedWire,
        row_count: usize,
        rows: crate::layered::Revision,
        names: crate::layered::Revision,
        expression_targets: HashMap<&'static str, Uuid>,
        owner_rows: &ListsByRow<U>,
    ) -> Option<Self> {
        let (owners, spelled, targets) = wire.candidates.into_columns()?;
        let retained = wire.retained.into_flags()?;
        let (graph_keys, graph_lengths, graph_targets) = wire.graph.into_columns()?;
        let (owner_keys, owner_lengths, owner_targets) = wire.by_owner.into_columns()?;
        let chain_targets = wire.chain_targets.into_pairs()?;
        let chain_incomplete = wire.chain_incomplete.0;
        let in_range = |i: usize| i < row_count;
        if retained.len() != owners.len()
            || wire.kinds > owners.len()
            || !wire.library_configuration
            || !owners.iter().all(|&owner| in_range(owner))
            || !spelled
                .iter()
                .all(|&index| usize::from(index) < SPELLED_RELATIONSHIPS.len())
            || !owner_keys.iter().all(|&owner| in_range(owner))
            || !chain_targets
                .iter()
                .all(|&(f, b)| in_range(f) && in_range(b))
            || !chain_incomplete.iter().all(|&f| in_range(f))
        {
            return None;
        }
        // The wire's spelled and target columns are the plan's as they are;
        // its owners narrow to the owner column.
        let owners = owners
            .into_iter()
            .map(u32::try_from)
            .collect::<Result<Vec<u32>, _>>()
            .ok()?;
        Some(
            Self {
                candidates: Candidates {
                    library: None,
                    owners,
                    spelled,
                    targets,
                    spellings: SPELLED_RELATIONSHIPS.to_vec(),
                    kinds: wire.kinds,
                    retained,
                },
                graph: crate::id_graph::IdGraph::frozen(crate::id_graph::Frozen::from_columns(
                    &graph_keys,
                    &graph_lengths,
                    graph_targets,
                )?),
                by_owner: RetainedByOwner {
                    // (the wire's lists are written by ascending owner, each
                    // a row with direct bases in a library's own plans: else
                    // they are laid out over the rows alone)
                    frozen: Arc::new(
                        if owner_keys.iter().all(|&owner| owner_rows.contains(owner)) {
                            ListsByRow::from_sorted_on(
                                owner_rows,
                                &owner_keys,
                                &owner_lengths,
                                owner_targets,
                            )?
                        } else {
                            ListsByRow::from_sorted(
                                row_count,
                                &owner_keys,
                                &owner_lengths,
                                owner_targets,
                            )?
                        },
                    ),
                    own: IdMap::default(),
                },
                typing_by_owner: OnceLock::new(),
                library_configuration: wire.library_configuration,
                expression_targets,
                chain_bases: Arc::new(super::type_relations::FeatureChainBases {
                    targets: chain_targets.into_iter().collect(),
                    incomplete: chain_incomplete.into_iter().collect(),
                }),
                source_rows: std::sync::Mutex::new(rows),
                source_names: names,
            }
            .into_frozen(),
        )
    }
}

/// The relationships the implied planner spells — kind, source role, target
/// role — in the order a candidate edge's wire form indexes them.
const SPELLED_RELATIONSHIPS: [(&str, &str, &str); 4] = [
    ("Subclassification", "subclassifier", "superclassifier"),
    ("Subsetting", "subsettingFeature", "subsettedFeature"),
    (
        "ReferenceSubsetting",
        "subsettingFeature",
        "referencedFeature",
    ),
    ("FeatureTyping", "typedFeature", "type"),
];

/// The index of a spelled relationship in [`SPELLED_RELATIONSHIPS`]; `None`
/// for a relationship the table does not list, which no wire carries.
fn spelled_relationship_index(kind: &str, source: &str, target: &str) -> Option<u8> {
    SPELLED_RELATIONSHIPS
        .iter()
        .position(|&(k, s, t)| k == kind && s == source && t == target)
        .map(|i| u8::try_from(i).expect("a four-entry table"))
}

/// The entries of a map as a vector sorted by key.
pub(super) fn sorted_by_key<K: Ord, V>(entries: impl Iterator<Item = (K, V)>) -> Vec<(K, V)> {
    let mut entries: Vec<(K, V)> = entries.collect();
    entries.sort_by(|a, b| a.0.cmp(&b.0));
    entries
}

/// The elements of a set as a sorted vector.
pub(super) fn sorted<T: Ord>(elements: impl Iterator<Item = T>) -> Vec<T> {
    let mut elements: Vec<T> = elements.collect();
    elements.sort_unstable();
    elements
}

/// A library's own implied plan as a snapshot carries it. A candidate edge
/// is its owner, its index in [`SPELLED_RELATIONSHIPS`] and its target.
#[derive(serde::Serialize, serde::Deserialize)]
pub(crate) struct ImpliedWire {
    pub(super) candidates: CandidateColumns,
    pub(super) kinds: usize,
    pub(super) retained: crate::bulk::Flags,
    pub(super) graph: crate::bulk::IdLists,
    pub(super) by_owner: crate::bulk::IndexIdLists,
    pub(super) library_configuration: bool,
    pub(super) chain_targets: crate::bulk::Pairs,
    pub(super) chain_incomplete: crate::bulk::Ints,
}

/// The candidate edges as columns: the owners, the spelled-relationship
/// indices, the target ids.
#[derive(serde::Serialize, serde::Deserialize)]
pub(super) struct CandidateColumns {
    pub(super) owners: crate::bulk::Ints,
    pub(super) spelled: crate::bulk::Bytes,
    pub(super) ids: crate::bulk::Ids,
}
impl CandidateColumns {
    /// The columns, each of the candidates' length; `None` for columns of
    /// unequal length.
    fn into_columns(self) -> Option<(Vec<usize>, Vec<u8>, Vec<Uuid>)> {
        if self.owners.0.len() != self.spelled.0.len() || self.owners.0.len() != self.ids.0.len() {
            return None;
        }
        Some((self.owners.0, self.spelled.0, self.ids.0))
    }
}

#[cfg(test)]
fn same_graph(a: &crate::id_graph::IdGraph, b: &crate::id_graph::IdGraph) -> bool {
    a.iter().count() == b.iter().count() && a.iter().all(|(k, v)| b.get(k) == Some(v))
}

#[cfg(test)]
impl SupportedImpliedSpecializations {
    /// Drop this plan a member at a time, naming each to `note` once it is
    /// gone, for the tests that measure what each holds.
    pub(super) fn drop_members(self, note: &mut dyn FnMut(&str)) {
        let Self {
            candidates,
            graph,
            by_owner,
            typing_by_owner,
            library_configuration: _,
            expression_targets,
            chain_bases,
            source_rows,
            source_names,
        } = self;
        println!(
            "  candidates {} (kinds {}), graph {} keys / {} targets, by_owner {} keys / {} targets",
            candidates.owners.len(),
            candidates.kinds,
            graph.iter().count(),
            graph.iter().map(|(_, v)| v.len()).sum::<usize>(),
            by_owner.iter().count(),
            by_owner.iter().map(|(_, v)| v.len()).sum::<usize>(),
        );
        drop(candidates);
        note("candidates");
        drop(graph);
        note("graph");
        drop(by_owner);
        note("by_owner");
        drop(typing_by_owner);
        note("typing_by_owner");
        drop(expression_targets);
        note("expression_targets");
        drop(chain_bases);
        note("chain_bases");
        drop((source_rows, source_names));
        note("revisions");
    }
}

#[cfg(test)]
impl SupportedImpliedSpecializations {
    /// Whether the plan has no candidate edge of its own.
    pub(super) fn is_empty(&self) -> bool {
        self.candidates.owners.is_empty()
    }

    /// The first field in which two plans differ, the memo and the row
    /// revisions aside.
    pub(super) fn difference(&self, other: &Self) -> Option<String> {
        let first =
            |what: &str, a: String, b: String| (a != b).then(|| format!("{what}: {a} != {b}"));
        let listed = |plan: &Self| -> Vec<(usize, PlannedEdge)> {
            plan.candidates.iter().map(|(c, _)| c).collect()
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
        .or_else(|| (!same_graph(&self.graph, &other.graph)).then(|| "final graph".to_string()))
        .or_else(|| {
            let lists = |plan: &Self| -> IdMap<usize, Vec<Uuid>> {
                plan.by_owner
                    .iter()
                    .map(|(owner, targets)| (owner, targets.to_vec()))
                    .collect()
            };
            (lists(self) != lists(other)).then(|| "by owner".to_string())
        })
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
        let names = self.implied_names();
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
            self.implied.as_ref()?.specializations.local_capacity(),
        )?;
        let rows = self.elements.observe_revision();
        if let Some(table) = &mut self.implied {
            table.static_authority = plan;
            table.static_rows = rows;
            table.specializations = graph.into();
        }
        Some(())
    }

    /// Structural owners, including memberships without a name or body scope.
    /// The frozen rows' part is shared by every build on them (a frozen
    /// row's relationships are frozen rows): a build on a prepared library
    /// reads the library's own table of its relationships' owners, which it
    /// keeps for every build on it; a build cut to the library's source rows
    /// (the one its plans are made on) makes the part once in the cell it
    /// shares. This build's rows follow. The library's table owns its
    /// materialized rows where a scan of the frozen rows' own relationships
    /// finds no owner, and no planner reads a materialized row's owner: a
    /// materialized row names its source in its properties, and an
    /// element's owning membership is an authored row.
    fn specialization_relation_owners(&self) -> Vec<Option<usize>> {
        fn scan(elements: &super::Elem, owners: &mut [Option<usize>], owner: usize) {
            for &relationship in &elements.owned_relationships {
                owners[relationship] = Some(owner);
            }
        }
        let frozen = self.elements.base_len();
        if !self.elements.base_untouched() {
            // A frozen row written since the freeze: no shared part.
            let mut owners = vec![None; self.elements.len()];
            for (owner, element) in self.elements.iter().enumerate() {
                scan(element, &mut owners, owner);
            }
            return owners;
        }
        let library = self.prepared_from.as_ref().filter(|prepared| {
            Arc::ptr_eq(
                self.elements.base_arc(),
                prepared.builder.elements.base_arc(),
            ) && prepared.builder.elements.len() == frozen
        });
        let shared = match library {
            Some(prepared) => Arc::clone(prepared.library_rel_owners()),
            None => Arc::clone(self.prefix_relation_owners.get_or_init(|| {
                let mut owners = vec![None; frozen];
                for (owner, element) in self.elements.iter().enumerate().take(frozen) {
                    scan(element, &mut owners, owner);
                }
                Arc::new(owners)
            })),
        };
        let mut owners = vec![None; self.elements.len()];
        // The shared part serves the rows it was made of: a build over the
        // frozen rows cut to their source rows shares the cell with no
        // other.
        let from = if shared.len() == frozen {
            owners[..frozen].copy_from_slice(&shared);
            frozen
        } else {
            0
        };
        for (owner, element) in self.elements.iter().enumerate().skip(from) {
            scan(element, &mut owners, owner);
        }
        owners
    }

    /// The work [`Self::implied_names`] is about to do: the shared part's
    /// names, spelled once, when it is not built yet, and a copy with the
    /// build's own names when it has some; a built shared part alone costs
    /// a step.
    fn charge_implied_names(&self, steps: &mut Option<&mut usize>) -> Option<()> {
        let frozen = self.lib_qnames.base_len();
        let shared_built =
            self.lib_qnames.base_untouched() && self.prefix_implied_names.get().is_some();
        if shared_built && self.lib_qnames.len() == frozen && self.external_implied_names.is_empty()
        {
            return planning_charge(steps, 1);
        }
        planning_charge(
            steps,
            self.lib_qnames
                .len()
                .saturating_add(self.external_implied_names.capacity()),
        )?;
        for (_, segments) in self
            .lib_qnames
            .iter()
            .skip(if shared_built { frozen } else { 0 })
        {
            planning_charge(steps, segments.len())?;
            for segment in segments {
                planning_charge(steps, segment.len())?;
            }
        }
        for name in self.external_implied_names.keys() {
            planning_charge(steps, name.len())?;
        }
        Some(())
    }

    /// The names implied relationships are planned by: the library's
    /// qualified names by name, then a build's own library units' and its
    /// external names (the later entry of a name winning). The frozen rows'
    /// part is made once and shared by every build on them; a build with
    /// names of its own takes a copy with them added.
    pub(super) fn implied_names(&self) -> Arc<HashMap<String, Uuid>> {
        if !self.lib_qnames.base_untouched() {
            // A library name written since the freeze (an identity override):
            // the shared part no longer describes these rows.
            return Arc::new(
                self.lib_qnames
                    .iter()
                    .map(|(id, segments)| (segments.join("::"), *id))
                    .chain(
                        self.external_implied_names
                            .iter()
                            .map(|(name, id)| (name.clone(), *id)),
                    )
                    .collect(),
            );
        }
        let frozen = self.lib_qnames.base_len();
        let shared = self.prefix_implied_names.get_or_init(|| {
            Arc::new(
                self.lib_qnames
                    .iter()
                    .take(frozen)
                    .map(|(id, segments)| (segments.join("::"), *id))
                    .collect(),
            )
        });
        if self.lib_qnames.len() == frozen && self.external_implied_names.is_empty() {
            return Arc::clone(shared);
        }
        let mut names = HashMap::clone(shared);
        names.extend(
            self.lib_qnames
                .iter()
                .skip(frozen)
                .map(|(id, segments)| (segments.join("::"), *id)),
        );
        names.extend(
            self.external_implied_names
                .iter()
                .map(|(name, id)| (name.clone(), *id)),
        );
        Arc::new(names)
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
        // The owner roles read a transition's written source through the
        // element-id index.
        self.ensure_ids();
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
                    if is_a!(self.elements[i], "Feature")
                        && (self.graph_format == crate::model::GraphFormat::CanonicalV3
                            || self.elements[i]
                                .props
                                .get("isComposite")
                                .and_then(|v| v.as_bool())
                                == Some(true)
                            || is_portion(&self.elements[i]))
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

    /// The implied specializations semantic metadata gives (KerML 9.2,
    /// `Metaobjects::SemanticMetadata`): a type annotated by a metadata
    /// usage whose definition conforms to it specializes the metadata's
    /// `baseType` value — a classifier a classifier by a Subclassification,
    /// a feature a feature by a Subsetting, a feature a classifier by a
    /// FeatureTyping — planned as rows beside the kind roles, from `floor`
    /// on, so the checked lists certify them and the full form writes them
    /// (the resolver already inherits through them, `base_scopes`). A base
    /// that does not resolve plans nothing, and the audit keeps the element
    /// out ([`super::Builder::semantically_annotated`]).
    fn semantic_base_candidates(
        &mut self,
        floor: usize,
        steps: &mut Option<&mut usize>,
    ) -> Option<Vec<(usize, PlannedEdge)>> {
        let end = self.explicit_len();
        let mut annotated: Vec<usize> = self
            .metadata_of
            .iter()
            .filter(|(owner, metas)| **owner >= floor && **owner < end && !metas.is_empty())
            .map(|(owner, _)| *owner)
            .collect();
        annotated.sort_unstable();
        planning_charge(steps, annotated.len())?;
        let mut out = Vec::new();
        for owner in annotated {
            if !self.is_authored(owner) || !is_a!(self.elements[owner], "Type") {
                continue;
            }
            let targets = self.semantic_base_targets(owner, 0);
            planning_charge(steps, 1 + targets.len())?;
            let feature = is_a!(self.elements[owner], "Feature");
            let classifier = is_a!(self.elements[owner], "Classifier");
            for target in targets {
                let edge = match (
                    feature,
                    is_a!(self.elements[target], "Feature"),
                    is_a!(self.elements[target], "Classifier"),
                ) {
                    (false, false, true) if classifier => {
                        ("Subclassification", "subclassifier", "superclassifier")
                    }
                    // A classifier whose base is a feature (`baseType =
                    // systemContexts meta SysML::Type`, the library's own
                    // idiom) specializes the feature's declared types.
                    (false, true, _) if classifier => {
                        let types = self.direct_typing_elems(target);
                        planning_charge(steps, types.len())?;
                        for ty in types {
                            if is_a!(self.elements[ty], "Classifier") {
                                out.push((
                                    owner,
                                    (
                                        "Subclassification",
                                        "subclassifier",
                                        "superclassifier",
                                        self.elements[ty].id,
                                    ),
                                ));
                            }
                        }
                        continue;
                    }
                    (true, true, _) => ("Subsetting", "subsettingFeature", "subsettedFeature"),
                    (true, false, true) => ("FeatureTyping", "typedFeature", "type"),
                    _ => continue,
                };
                out.push((owner, (edge.0, edge.1, edge.2, self.elements[target].id)));
            }
        }
        Some(out)
    }

    /// The callee an instantiation expression is typed by (KerML 8.3.4.8,
    /// `InstantiationExpression::instantiatedType`), read as the planner
    /// and the audit read it: for an OperatorExpression the library
    /// Function the operator names (`BaseFunctions`, then `DataFunctions`,
    /// then `ControlFunctions`; the chain's dot function; `**` and `^`
    /// each their own), for a TriggerInvocationExpression the `Triggers` function its
    /// kind names, for an InvocationExpression the member of its function
    /// membership (the `fn` member the lowering writes), a Type of the
    /// model. A constructor types its result, not itself (the dynamic
    /// family's row on the canonical graph format), and has no callee
    /// here. `None` when the callee does not resolve to an element of the
    /// model — the operator or trigger function must be a loaded library
    /// Function — so the planner plans nothing and the audit keeps the
    /// expression out.
    pub(super) fn instantiation_callee(
        &mut self,
        e: usize,
        names: &HashMap<String, Uuid>,
    ) -> Option<usize> {
        let ty = self.elements[e].ty;
        if !conforms(ty, "InstantiationExpression") || conforms(ty, "ConstructorExpression") {
            return None;
        }
        if conforms(ty, "OperatorExpression") {
            // The operator as written (`**` and `^` are two library
            // functions, KerML `OperatorExpression::instantiatedType()`).
            let operator = match self.elements[e].props.get("operator") {
                Some(value) => value.as_str()?.to_owned(),
                None if ty == "FeatureChainExpression" => ".".to_owned(),
                None => return None,
            };
            return ["BaseFunctions", "DataFunctions", "ControlFunctions"]
                .iter()
                .find_map(|package| {
                    self.library_function(names, &format!("{package}::{operator}"))
                });
        }
        if ty == "TriggerInvocationExpression" {
            let name = match self.elements[e].props.get("kind").and_then(|v| v.as_str()) {
                Some("when") => "TriggerWhen",
                Some("at") => "TriggerAt",
                _ => "TriggerAfter",
            };
            return self.library_function(names, &format!("Triggers::{name}"));
        }
        let membership = self.elements[e]
            .owned_relationships
            .iter()
            .copied()
            .find(|&r| {
                self.is_authored(r)
                    && is_a!(self.elements[r], "Membership")
                    && !is_a!(self.elements[r], "FeatureMembership")
            })?;
        let id = self.elements[membership]
            .props
            .get("memberElement")?
            .as_reference()?;
        let target = self.element_index_of_uuid(id)?;
        is_a!(self.elements[target], "Type").then_some(target)
    }

    /// The loaded library Function `names` lists under `name`.
    fn library_function(&mut self, names: &HashMap<String, Uuid>, name: &str) -> Option<usize> {
        let id = *names.get(name)?;
        let target = self.element_index_of_uuid(id)?;
        (target < self.lib_boundary && is_a!(self.elements[target], "Function")).then_some(target)
    }

    /// The implied specialization of each instantiation expression of
    /// `rows` by its callee (KerML 8.3.4.8: an invocation, operator or
    /// trigger expression specializes its `instantiatedType` — a typing by
    /// a Type, a subsetting of a Feature), planned as rows beside the kind
    /// roles like the semantic metadata bases, so the checked lists certify
    /// them, the positional planner pairs the arguments with the callee's
    /// parameters, and the full form writes them. A chain's typing by the
    /// dot function is the kind arm's ([`Self::required_implied_plan`]); an
    /// expression whose callee does not resolve plans nothing, and the
    /// library's own expressions are left out (see below).
    fn instantiation_candidates(
        &mut self,
        rows: &[usize],
        names: &HashMap<String, Uuid>,
        steps: &mut Option<&mut usize>,
    ) -> Option<Vec<(usize, PlannedEdge)>> {
        planning_charge(steps, rows.len())?;
        // A duplicate identity makes every callee row unusable, as it does
        // the kind roles' witnesses.
        if self.literal_identities_unique(steps.as_deref_mut()) != Some(true) {
            return Some(Vec::new());
        }
        let mut out = Vec::new();
        for &e in rows {
            // The library's own expressions keep their kind roles alone:
            // pairing their arguments with their callees' parameters costs
            // the cold library plan half a million steps of positional work
            // it does not have under the shared budget, and no read of a
            // model asks for a library expression's callee.
            if self.elements[e].ty == "FeatureChainExpression" || e < self.lib_boundary {
                continue;
            }
            let Some(target) = self.instantiation_callee(e, names) else {
                continue;
            };
            planning_charge(steps, 1)?;
            let edge = if is_a!(self.elements[target], "Feature") {
                ("Subsetting", "subsettingFeature", "subsettedFeature")
            } else {
                ("FeatureTyping", "typedFeature", "type")
            };
            out.push((e, (edge.0, edge.1, edge.2, self.elements[target].id)));
        }
        Some(out)
    }

    fn supported_implied_specializations_with_budget(
        &mut self,
        names: &HashMap<String, Uuid>,
        use_library_cache: bool,
        steps: Option<&mut usize>,
    ) -> Option<Arc<SupportedImpliedSpecializations>> {
        let previous = std::mem::replace(&mut self.implied_planning, true);
        let plan = self.supported_implied_specializations_planning(names, use_library_cache, steps);
        self.implied_planning = previous;
        plan
    }

    /// [`Self::supported_implied_specializations_with_budget`] with the
    /// planner flagged as running.
    fn supported_implied_specializations_planning(
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
        let mut instantiations = Vec::new();
        for (i, element) in self.elements.iter().enumerate() {
            planning_charge(&mut steps, element.owned_relationships.len())?;
            // All kind-based requirements belong to Types. Variant ownership
            // is an independent recipe, so retain even a non-Type variant row.
            // Collect during the already charged complete ownership scan.
            if self.is_authored(i)
                && (is_a!(element, "Type")
                    || element.owning_relationship.is_some_and(|membership| {
                        self.elements
                            .get(membership)
                            .is_some_and(|row| row.ty == "VariantMembership")
                    }))
            {
                requirement_candidates.push(i);
                if is_a!(element, "InstantiationExpression") {
                    instantiations.push(i);
                }
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
        candidates.extend(self.semantic_base_candidates(0, &mut steps)?);
        candidates.extend(self.instantiation_candidates(&instantiations, names, &mut steps)?);
        let chain_bases = self.checked_chain_bases(self.explicit_len(), steps.as_deref_mut())?;
        let (retained, graph) = self.required_specialization_edges_with_chain_bases(
            &candidates,
            0,
            self.explicit_len(),
            &owners,
            &chain_bases,
            steps.as_deref_mut(),
        )?;
        let mut by_owner = RetainedByOwner::default();
        for (i, &(owner, edge)) in candidates.iter().enumerate() {
            planning_charge(&mut steps, 1)?;
            if retained[i] {
                by_owner.push(owner, edge.3);
            }
        }
        let plan = Arc::new(SupportedImpliedSpecializations {
            candidates: Candidates::new(None, candidates, kind_candidates, retained),
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
        let mut instantiations = Vec::new();
        for i in floor..end {
            let element = &self.elements[i];
            planning_charge(&mut steps, element.owned_relationships.len())?;
            if is_a!(element, "Type")
                || element.owning_relationship.is_some_and(|membership| {
                    self.elements
                        .get(membership)
                        .is_some_and(|row| row.ty == "VariantMembership")
                })
            {
                requirement_candidates.push(i);
                if is_a!(element, "InstantiationExpression") {
                    instantiations.push(i);
                }
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
        candidates.extend(self.semantic_base_candidates(floor, &mut steps)?);
        candidates.extend(self.instantiation_candidates(&instantiations, names, &mut steps)?);
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
                by_owner.push(owner, edge.3);
            }
        }
        let mut chain_bases = super::type_relations::FeatureChainBases {
            targets: plan.chain_bases.targets.clone(),
            incomplete: plan.chain_bases.incomplete.clone(),
        };
        chain_bases.targets.extend(&chains.targets);
        chain_bases.incomplete.extend(&chains.incomplete);
        Some(Some(Arc::new(SupportedImpliedSpecializations {
            candidates: Candidates::new(
                Some(Arc::clone(plan)),
                candidates,
                kind_candidates,
                retained,
            ),
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
        library: &crate::id_graph::IdGraph,
        mut steps: Option<&mut usize>,
    ) -> Option<(Vec<bool>, SpecializationGraph)> {
        planning_charge(&mut steps, 1)?;
        let mut graph: IdMap<Uuid, Vec<(Uuid, Option<usize>)>> = IdMap::default();
        for (r, relation) in self
            .elements
            .iter()
            .enumerate()
            .take(explicit_len)
            .skip(floor)
        {
            planning_charge(&mut steps, 1)?;
            if !is_a!(relation, "Specialization") {
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
        let mut visited = IdSet::default();
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
        let rank: IdMap<_, _> = postorder
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
        let mut seen = IdSet::default();
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
        let mut final_graph = SpecializationGraph::default();
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
        let mut bases = library.bases.to_map();
        bases.extend(own);
        let mut incomplete = library.bases_incomplete.clone();
        incomplete.extend(own_incomplete);
        Some((bases, incomplete))
    }

    /// The direct bases `plan` gives, as the static prefix keeps them: a
    /// build that extends its prepared library's plans lays its own rows'
    /// over the library's shared table (what
    /// [`Self::positional_direct_bases_on_library`] joins into one), else
    /// every row's are its own.
    fn planned_direct_bases(
        &mut self,
        plan: &SupportedImpliedSpecializations,
    ) -> Option<PlannedBases> {
        if plan.library_configuration {
            if let Some(library) = self.library_plans(None)? {
                let (own, own_incomplete) =
                    self.own_positional_direct_bases(&library, plan, None)?;
                let mut bases = crate::layered::LayeredMap::over(library.bases_table());
                for (owner, targets) in own {
                    bases.insert(owner, targets);
                }
                let mut incomplete = library.bases_incomplete.clone();
                incomplete.extend(own_incomplete);
                return Some((bases, incomplete));
            }
        }
        let (bases, incomplete) = self.positional_direct_bases_from_static_plan(plan, None)?;
        Some((bases.into(), incomplete))
    }

    /// The specialization graph a materialization starts from: `plan`'s,
    /// with the prepared library's own materialized edges in it. The rows
    /// the edges change in the frozen graph the plan extends are made once,
    /// shared by every build over it, and lie over it (see
    /// [`PrefixImplied::graph_over`]); the plan's own rows lie over those,
    /// each with the edges of its source.
    fn planned_specializations(
        &self,
        plan: &SupportedImpliedSpecializations,
    ) -> crate::id_graph::IdGraph {
        let Some(prefix) = &self.prefix_implied else {
            return plan.graph.clone();
        };
        if !self.elements.base_untouched() {
            // A frozen row written since the freeze (an identity override
            // remaps the rows' ids): the prefix's edges as its rows give
            // them now, merged into a graph of this build's own.
            let mut graph = plan.graph.clone();
            for (source, target) in self.prefix_edges_now() {
                let targets = graph.entry(source).or_default();
                if !targets.contains(&target) {
                    targets.push(target);
                }
            }
            return graph;
        }
        let frozen = plan.graph.frozen_arc();
        let (rows, sources) = prefix.graph_over(frozen);
        let mut graph = crate::id_graph::IdGraph::overlaid(Arc::clone(frozen), rows);
        for (&source, targets) in plan.graph.local_iter() {
            let mut targets = targets.clone();
            if sources.binary_search(&source).is_ok() {
                for target in prefix.targets_from(source) {
                    if !targets.contains(&target) {
                        targets.push(target);
                    }
                }
            }
            graph.insert(source, targets);
        }
        graph
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
        let mut bases = IdMap::default();
        let mut incomplete = IdSet::default();
        let push = |bases: &mut IdMap<usize, Vec<usize>>,
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
                if !is_a!(self.elements[relationship], "Specialization") {
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
        for ((owner, edge), retained) in plan.candidates.own() {
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
                let names = self.implied_names();
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
        let mut typing = RetainedTypings::default();
        for ((owner, edge), retained) in plan.candidates.iter() {
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
        if !is_a!(owner, "Type") {
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
                    .is_some_and(|e| is_a!(e, "Conjugation"))
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
            if !is_a!(relation, "Specialization")
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
                let names = self.implied_names();
                self.supported_implied_specializations_with_budget(
                    &names,
                    library_configuration,
                    budget.as_deref_mut(),
                )?
            }
        };
        for &id in plan.by_owner.get(element).into_iter().flatten() {
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

    pub(super) fn expression_target_names(
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
                [p, t, n] if p == "Occurrences" && t == "Occurrence" && n == "portions" => {
                    Some("Occurrences::Occurrence::portions")
                }
                _ => None,
            };
            let name = if let Some(name) = composite {
                Some(name)
            } else if let [package, member] = segments.as_slice() {
                match (package.as_str(), member.as_str()) {
                    ("Base", "things") => Some(FEATURE_BASE),
                    ("Base", "naturals") => Some(MULTIPLICITY_BASE),
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
                MULTIPLICITY_BASE,
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
            if (matches!(
                name,
                CHAIN_FUNCTION | FEATURE_BASE | MULTIPLICITY_BASE | STEP_BASE
            ) || BINARY_ROLES.iter().any(|(role, _)| *role == name)
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
    pub(super) fn positional_direct_bases(&mut self) -> (IdMap<usize, Vec<usize>>, IdSet<usize>) {
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
        self.charge_implied_names(&mut steps)?;
        let names = self.implied_names();
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
    /// (see [`super::LibraryPlans`]). The plan is taken from this builder;
    /// the names are the table every build on the library shares.
    pub(super) fn library_rows_implied(
        &mut self,
    ) -> (
        Arc<HashMap<String, Uuid>>,
        Arc<SupportedImpliedSpecializations>,
    ) {
        let names = self.implied_names();
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
        // The authored rows by id, a later row winning: this build's own
        // under the frozen rows' shared map (a materialized row's id names
        // no authored row), else every authored row's.
        let own_from = self
            .prefix_ids
            .as_ref()
            .filter(|_| self.elements.base_untouched())
            .map_or(0, |_| self.lib_boundary);
        let own_by_id: HashMap<Uuid, usize> = (own_from..self.explicit_len())
            .map(|i| (self.elements[i].id, i))
            .collect();
        let by_id = |id: &Uuid| {
            own_by_id.get(id).copied().or_else(|| {
                self.prefix_ids
                    .as_ref()
                    .filter(|_| own_from > 0)?
                    .get(id)
                    .copied()
                    .filter(|&i| self.is_authored(i))
            })
        };
        let mut incomplete = IdSet::default();
        let mut bases: IdMap<usize, Vec<usize>> = IdMap::default();
        for owner in self.authored_rows() {
            let element = &self.elements[owner];
            planning_charge(&mut steps, element.owned_relationships.len())?;
            for &relationship in &element.owned_relationships {
                let relation = &self.elements[relationship];
                if is_a!(relation, "Specialization") {
                    if let Some(target) = specialization_target(relation).and_then(|id| by_id(&id))
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
        for ((owner, edge), retained) in plan.candidates.iter() {
            planning_charge(&mut steps, 1)?;
            if retained {
                if let Some(target) = by_id(&edge.3) {
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
            || is_portion(&self.elements[feature])
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
                            && super::type_relations::composite_owner_context(
                                self.elements[owner].ty,
                            )
                        {
                            let owner_types = if is_a!(self.elements[owner], "Feature") {
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
                                self.elements[feature]
                                    .props
                                    .get("isComposite")
                                    .and_then(|v| v.as_bool())
                                    == Some(true),
                                is_portion(&self.elements[feature]),
                                owner_types,
                            ) {
                                // The library's own `portions` is the root of
                                // its role: no feature specializes itself.
                                if let Some(&target) = targets.get(role) {
                                    if target == self.elements[feature].id {
                                        continue;
                                    }
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
            if !self.is_authored(relationship)
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
                *needed |= self.elements[target].conforms(kind);
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
            // An individual definition is a Life
            // (`checkOccurrenceDefinitionIndividualSpecialization`).
            if is_individual(&self.elements[i]) {
                if let Some(&id) = names.get(INDIVIDUAL_BASE) {
                    out.push(("Subclassification", "subclassifier", "superclassifier", id));
                }
            }
        } else if usage_kind_of(ty, Dialect::Sysml)
            .filter(|_| !matches!(ty, "Flow" | "SuccessionFlow"))
            .is_some()
        {
            let owner = self.elements[i]
                .owning_relationship
                .and_then(|m| rel_owner.get(m).copied().flatten().map(|o| (m, o)));
            for name in usage_roles(self, i, owner) {
                if let Some(&id) = names.get(name) {
                    out.push(("Subsetting", "subsettingFeature", "subsettedFeature", id));
                }
            }
            for name in usage_redefinition_roles(self, i, owner) {
                if let Some(&id) = names.get(name) {
                    out.push(("Redefinition", "redefiningFeature", "redefinedFeature", id));
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
        // A transition's guard expression is its transition action's guard
        // (SysML `checkTransitionUsageTransitionFeatureSpecialization`).
        if conforms(ty, "Expression") && is_transition_guard(self, i) {
            if let Some(&id) = names.get(TRANSITION_GUARD) {
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
        // A synthesized default multiplicity subsets the library range it
        // stands for: a usage's `exactlyOne` (SysML 7.6.3), an individual
        // definition's `zeroOrOne`. Both subset `naturals`, so the generic
        // obligation below is reached through this one and minimized away.
        if let Some(role) = self.elements[i]
            .owning_relationship
            .and_then(|rel| Some((rel, rel_owner.get(rel).copied().flatten()?)))
            .and_then(|(rel, owner)| {
                default_multiplicity_role(
                    &self.elements[i],
                    &self.elements[rel],
                    &self.elements[owner],
                )
            })
        {
            if let Some(&id) = names.get(role) {
                out.push(("Subsetting", "subsettingFeature", "subsettedFeature", id));
            }
        }
        // Append the inherited generic obligation independently of narrower
        // roles, then let the shared minimizer preserve only necessary edges.
        // A Multiplicity's generic obligation is `Base::naturals` itself
        // (checkMultiplicitySpecialization): the root of all multiplicities
        // subsets `dataValues` and so `things`, and planning it in place of
        // `things` keeps one obligation per multiplicity, where a second
        // one over every range of the library exhausted the cold planning
        // budget. A library without `naturals` still gets `things`.
        if conforms(ty, "Feature") {
            let base = if conforms(ty, "Multiplicity")
                && expression_targets.contains_key(MULTIPLICITY_BASE)
            {
                MULTIPLICITY_BASE
            } else {
                FEATURE_BASE
            };
            if let Some(&id) = expression_targets.get(base) {
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
        self.implied_deferred = false;
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

    /// Make the implied relationships when a derived read deferred them (see
    /// `implied_deferred`): before an operation that acts on them differently
    /// once they are made, so it finds them as it would have had that read
    /// made them.
    pub(super) fn make_deferred_implied(&mut self) {
        if self.implied_deferred {
            self.ensure_implied();
        }
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
        let mut seen = IdSet::default();
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
        (self
            .b
            .semantic_ownership
            .as_ref()
            .is_some_and(|view| view.contains(e.0))
            || self
                .b
                .prefix_ownership
                .as_ref()
                .is_some_and(|prefix| prefix.contains(e.0)))
            && is_a!(self.b.elements[e.0], "Relationship")
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
            .find(|&&rel| is_a!(r.b.elements[rel], "Specialization"))
            .unwrap();
        r.b.elements[x].owned_relationships.push(specialization);
        assert_eq!(r.b.value_context_bases(x, &mut 0), Some(vec![a]));
        let relation = *r.b.elements[x]
            .owned_relationships
            .iter()
            .find(|&&rel| is_a!(r.b.elements[rel], "Conjugation"))
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
        // The callee typing, then the generated result membership.
        assert_eq!(rows.len(), 2);
        assert_eq!(r.b.elements[rows[0].0].ty, "FeatureTyping");
        assert_eq!(r.b.elements[rows[1].0].ty, "ReturnParameterMembership");
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
            let callee = r.resolve_qualified("F").unwrap();
            let fake =
                HashMap::from([("Performances::evaluations".to_owned(), r.element_id(decoy))]);
            let plan = r.b.supported_implied_specializations(&fake, false);
            // The callee typing is the function membership's, not a role
            // the name table could relabel; no role candidate remains.
            let candidates: Vec<_> = plan
                .candidates
                .iter()
                .filter_map(|((owner, edge), _)| (owner == expression).then_some(edge))
                .collect();
            assert_eq!(
                candidates,
                vec![(
                    "FeatureTyping",
                    "typedFeature",
                    "type",
                    r.element_id(callee)
                )]
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
                .filter_map(|((owner, edge), _)| (owner == expression).then_some(edge.3))
                .collect();
            // Losing the Expression role does not remove the independent
            // Step and Feature requirements, nor the callee typing. Duplicate
            // identity still makes every specialization candidate unusable.
            let callee = r.resolve_qualified("F").unwrap();
            assert_eq!(
                actual,
                if duplicate_uuid {
                    vec![]
                } else {
                    vec![
                        configuration["Performances::performances"],
                        configuration["Base::things"],
                        r.element_id(callee),
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
#[derive(Clone, Copy, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
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
        self.short_name_memo.clear();
        self.redefiner_index = None;
        self.import_truncated.clear();
    }

    /// Whether the result family generates `e`'s result parameter: a
    /// feature reference expression, or an operator, invocation or trigger
    /// expression of the model's own rows that writes no result of its own
    /// (see [`super::owned_results::generated_result_kind`]).
    pub(super) fn generates_owned_result(&self, e: ElementRef) -> bool {
        let ty = self.b.elements[e.0].ty;
        ty == "FeatureReferenceExpression"
            || (super::owned_results::generated_result_kind(ty)
                && e.0 >= self.b.lib_boundary
                && !self.b.elements[e.0].owned_relationships.iter().any(|&r| {
                    self.b
                        .elements
                        .get(r)
                        .is_none_or(|row| is_a!(row, "ReturnParameterMembership"))
                }))
    }

    /// The owned result the checked `Expression::result` answers: the
    /// generated one where the projection is ready, else a written one (a
    /// cast's, an extent's). `None` leaves the read qualified.
    pub(super) fn certified_owned_result(&mut self, e: ElementRef) -> Option<ElementRef> {
        if self.generates_owned_result(e) {
            if !self.owned_result_projection_ready(e) {
                return None;
            }
            let view = self.b.semantic_ownership.as_ref()?;
            return view.result(e.0).map(|result| ElementRef(result.feature));
        }
        let membership = self.b.elements[e.0]
            .owned_relationships
            .iter()
            .copied()
            .find(|&r| {
                self.b.is_authored(r) && is_a!(self.b.elements[r], "ReturnParameterMembership")
            })?;
        match &*self.b.elements[membership].children {
            [feature] if self.b.elements[*feature].owning_relationship == Some(membership) => {
                Some(ElementRef(*feature))
            }
            _ => None,
        }
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
                                is_a!(membership, "ReturnParameterMembership")
                                    && *membership.children == [result.feature]
                            })
                        && self.b.elements.get(result.feature).is_some_and(|feature| {
                            is_a!(feature, "Feature")
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
                    .any(|((owner, _), _)| owner == expression)
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
                .filter_map(|((owner, edge), _)| (owner == expression).then_some(edge.3))
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
                .filter_map(|((owner, edge), _)| (owner == expression.0).then_some(edge.3))
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
                    r.b.elements[target.0].set_ty("Feature");
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
                .filter_map(|((owner, edge), _)| (owner == expression.0).then_some(edge.3))
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
            .filter_map(|((at, edge), retained)| (at == owner && retained).then_some(edge.3))
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
        r.b.elements[i].set_ty("LiteralExpression");
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
                assert!(!plan.candidates.iter().any(|((at, edge), _)| at == owner.0
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
                        r.b.elements[target.0].set_ty("Class");
                    }
                    4 => r.b.elements[target.0].set_ty("Feature"),
                    5 => r.b.elements[target.0].set_ty("Step"),
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
                        .any(|((at, edge), _)| at == owner.0 && edge.3 == r.element_id(target)),
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
        assert!(!plan.candidates.iter().any(|((at, _), _)| at == owner.0));
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
            .filter_map(|((at, edge), _)| (at == owner).then_some(edge.3))
            .collect()
    }
    fn retained(plan: &SupportedImpliedSpecializations, owner: usize) -> Vec<Uuid> {
        plan.candidates
            .iter()
            .filter_map(|((at, edge), retained)| (at == owner && retained).then_some(edge.3))
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
                        r.b.elements[target.0].set_ty("Feature");
                    }
                    4 => {
                        r.b.elements[target.0].set_ty("Class");
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
        self.ensure_ids();
        if self.implied.is_some() {
            self.materialize_owned_results(None);
            return;
        }
        let owners = self.semantic_relationship_owners();
        let from = self.elements.len();
        let lib_by_name = self.implied_names();
        let mut ownership =
            super::semantic_ownership::SemanticOwnership::new(from, self.prefix_ownership.clone());
        // Capture a newly computed positional authority together with the
        // recipes below, rather than certifying an older compatibility cache.
        self.positional_redefinitions = None;
        self.ensure_positional_redefinitions();
        let plan = self.supported_implied_specializations(
            &lib_by_name,
            self.external_implied_names.is_empty(),
        );
        let mut specializations = self.planned_specializations(&plan);
        // A build on a library that carries its own materialized rows
        // materializes its own rows only: the library's lie in the prefix.
        let own_from = self.own_rows_start();
        let mut planned = Vec::new();
        for ((owner, edge), retained) in plan.candidates.iter() {
            if retained && owner >= own_from {
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
        let positional_plan = self.positional_redefinitions.as_ref().unwrap();
        let mut positional: Vec<(usize, &Vec<usize>)> = positional_plan
            .targets
            .iter()
            .filter(|(&source, _)| source >= own_from)
            .map(|(&source, targets)| (source, targets))
            .collect();
        positional.sort_by_key(|(source, _)| *source);
        for (source, targets) in positional {
            for &target in targets {
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
        // A target transition's implicit source as a row of its own: an
        // implied Membership whose member is the source every reader
        // derives (`implicit_transition_source`), after the transition's
        // written relationships and the specializations planned for it.
        // No specialization: no base, nothing to minimize, no legacy slot.
        for (transition, source) in implicit_transition_source_rows(self, own_from, from, &owners) {
            planned.push((
                transition,
                (
                    "Membership",
                    "membershipOwningNamespace",
                    "memberElement",
                    self.elements[source].id,
                ),
                None,
            ));
        }
        // Retain this producer's exact recipes for the immediately following
        // tail transaction. Its positional table was computed from this same
        // current static authority; no second whole-model positional run is
        // needed before checking the rows we are about to append.
        let (planner_bases, planner_incomplete) = self
            .planned_direct_bases(&plan)
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
        let mut static_owners = IdSet::default();
        for row in &static_prefix.rows {
            let i = row.owner;
            static_owners.insert(i);
            let mut props = crate::properties::Properties::new();
            props.insert("isImplied", json!(true));
            props.insert(row.source_key, json!({ "@id": row.owner_id.to_string() }));
            props.insert(row.target_key, json!({ "@id": row.target.to_string() }));
            self.elements.push(Elem {
                ty: row.kind,
                meta: crate::metaclass::meta_of(row.kind),
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
        if self.prefix_static_only {
            self.publication.published();
            return;
        }
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
        let plans = super::owned_results::plan_expression_results(self, &mut result_steps);
        let result_state = if plans.is_some() {
            OwnedResultState::Attempted
        } else {
            OwnedResultState::WorkLimited
        };
        let plans = plans.unwrap_or_default();
        let mut dynamic_steps = plans.len().saturating_mul(11);
        let mut reserved: IdSet<_> = if dynamic_steps <= crate::eval::MAX_STEPS {
            plans.iter().flat_map(|plan| plan.ids()).collect()
        } else {
            IdSet::default()
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
        // The result redefinitions below add their edges to this graph too,
        // so a result without a subsetting of its own still needs it.
        if !result_edges.is_empty() || !result_roles.is_empty() {
            let graph =
                graph.get_or_insert_with(|| self.implied.as_ref().unwrap().specializations.clone());
            for (specific, general) in result_edges {
                graph.entry(specific).or_default().push(general);
            }
        }
        let local = if local_steps > crate::eval::MAX_STEPS {
            Err(super::dynamic_invocations::Refusal::WorkLimit)
        } else if local_roles.is_empty() {
            Ok(IdSet::default())
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
            table.specializations = graph.into();
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
        r.redefiner_index = Some(IdMap::default());
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
        let mut graph: IdMap<Uuid, Vec<(Uuid, Option<usize>)>> = IdMap::default();
        // A planner reads the source rows' edges: a prepared library's own
        // materialized rows are the plan's output, not its input (the dynamic
        // planner takes them as fixed recipes, see
        // `Builder::prefix_static_candidates`). A caller outside planning
        // that asks for every row (a recertification, a refresh) reads the
        // materialized rows' edges, the library's among them, as a build
        // from source would.
        let every_row = explicit_len == self.elements.len() && !self.planning();
        for (r, relation) in self.elements.iter().take(explicit_len).enumerate() {
            planning_charge(&mut steps, 1)?;
            if !is_a!(relation, "Specialization") || (!every_row && !self.is_authored(r)) {
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
        let mut visited = IdSet::default();
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
        let rank: IdMap<_, _> = postorder
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
        let mut seen = IdSet::default();
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
        let mut final_graph = SpecializationGraph::default();
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
        self.ensure_ids();
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
        // A build on a library that carries its own materialized rows has
        // its own rows' recipes only, as it materializes them.
        let own_from = self.own_rows_start();
        let mut rows = Vec::new();
        for ((owner, edge), retained) in required.candidates.iter() {
            planning_charge(&mut steps, 1)?;
            if !retained || owner < own_from {
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
        let mut sources: Vec<_> = positional
            .targets
            .keys()
            .copied()
            .filter(|&source| source >= own_from)
            .collect();
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
        // The plan's own rows over its frozen graph: the own rows are
        // charged, the frozen graph is shared.
        let mut specializations = required.graph.clone();
        for (_, targets) in specializations.local_iter() {
            planning_charge(&mut steps, targets.len().saturating_add(1))?;
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
            planner_bases: direct_bases.into(),
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
            let mut bases = implicit_def_bases(kind).to_vec();
            if is_individual(&self.elements[i]) {
                bases.push(INDIVIDUAL_BASE);
            }
            Some((
                bases,
                "Subclassification",
                "subclassifier",
                "superclassifier",
                &["Subclassification", "Specialization"],
            ))
        } else if usage_kind_of(t, Dialect::Sysml).is_some() {
            let owner = self.elements[i]
                .owning_relationship
                .and_then(|m| rel_owner.get(m).copied().flatten().map(|o| (m, o)));
            Some((
                usage_roles(self, i, owner),
                "Subsetting",
                "subsettingFeature",
                "subsettedFeature",
                &["Subsetting", "Redefinition", "ReferenceSubsetting"] as &[&str],
            ))
        } else {
            None
        };
        if let Some((bases, rel_ty, src, tgt, covering)) = bases {
            planning_charge(&mut steps, bases.len())?;
            let covered = explicit
                .iter()
                .any(|&r| covering.contains(&self.elements[r].ty));
            if !covered {
                for base in bases {
                    if let Some(&id) = lib_by_name.get(base) {
                        plan.push((rel_ty, src, tgt, id));
                    }
                }
                if usage_kind_of(t, Dialect::Sysml).is_some() {
                    let owner = self.elements[i]
                        .owning_relationship
                        .and_then(|m| rel_owner.get(m).copied().flatten().map(|o| (m, o)));
                    for base in usage_redefinition_roles(self, i, owner) {
                        if let Some(&id) = lib_by_name.get(base) {
                            plan.push((
                                "Redefinition",
                                "redefiningFeature",
                                "redefinedFeature",
                                id,
                            ));
                        }
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
            .filter_map(|((at, edge), retained)| (at == owner && retained).then_some(edge.3))
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
            r.b.elements[owner.0].set_ty(ty);
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
                .filter_map(|((at, edge), _)| (at == owner.0).then_some(edge.3))
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
                        r.b.elements[target.0].set_ty("Class");
                    }
                    2 => {
                        r.b.elements[target.0].set_ty("Feature");
                    }
                    3 => {
                        r.b.elements[target.0].set_ty("Step");
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
                        .any(|((at, edge), _)| at == owner.0 && edge.3 == r.element_id(target))
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
            .filter_map(|((e, edge), _)| (e == owner).then_some(edge.3))
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
                1 => r.b.elements[target.0].set_ty("Class"),
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
            assert!(!plan.candidates.iter().any(|((owner, _), _)| owner == e.0));
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
        assert!(prefix.planner_bases.get(&chain).unwrap().contains(&last));
        assert!(
            prefix
                .specializations
                .get(&r.b.elements[chain].id)
                .unwrap()
                .contains(&r.b.elements[last].id)
        );
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
                &IdSet::default(),
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
            .filter_map(|((source, edge), _)| (source == owner).then_some(edge.3))
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
                    1 => r.b.elements[role.0].set_ty("Class"),
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
                .any(|((source, edge), _)| source == object.0 && edge.3 == r.element_id(role))
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

    /// Attribute and enumeration definitions specialize `Base::DataValue` and
    /// their usages subset `Base::dataValues` — the elements the SysML
    /// `Attributes` aliases name — as a usage written against the alias does;
    /// a base named by its alias would not be found among the library's
    /// element names, and the usages would fall back to `Base::things`.
    #[test]
    fn attribute_and_enumeration_kinds_specialize_the_data_value_bases() {
        const BASE: &str = "standard library package Base { abstract classifier Anything; abstract datatype DataValue :> Anything; abstract feature things : Anything; abstract feature dataValues : DataValue :> things; }";
        const ATTRIBUTES: &str = "standard library package Attributes { alias AttributeValue for Base::DataValue; alias attributeValues for Base::dataValues; }";
        const USER: &str = "package P { attribute def AD; enum def Color { enum red; } attribute a; part def D { attribute b : AD; } attribute w :> Attributes::attributeValues; }";
        for format in [GraphFormat::LegacyV2, GraphFormat::CanonicalV3] {
            let mut model = Model::with_graph_format(format);
            model.add_library_source("Base.kerml", BASE);
            model.add_library_source("Attributes.sysml", ATTRIBUTES);
            model.add_source("user.sysml", USER);
            assert!(!model.has_errors());
            let mut r = ResolvedModel::build(&model);
            let id_of = |r: &mut ResolvedModel, name: &str| {
                let e = r.resolve_qualified(name).unwrap();
                r.element_id(e)
            };
            let data_value = id_of(&mut r, "Base::DataValue");
            let data_values = id_of(&mut r, "Base::dataValues");
            let things = id_of(&mut r, "Base::things");
            let targets = |r: &mut ResolvedModel, name: &str, kind: &str, key: &str| -> Vec<Uuid> {
                let e = r.resolve_qualified(name).unwrap();
                r.implied_relationships(e)
                    .into_iter()
                    .filter(|&rel| r.element_type(rel) == kind)
                    .filter_map(|rel| {
                        r.element_properties(rel)
                            .get(key)?
                            .get("@id")?
                            .as_str()?
                            .parse()
                            .ok()
                    })
                    .collect()
            };
            for name in ["P::AD", "P::Color"] {
                let bases = targets(&mut r, name, "Subclassification", "superclassifier");
                assert_eq!(
                    bases,
                    vec![data_value],
                    "{name} specializes Base::DataValue"
                );
            }
            for name in ["P::Color::red", "P::a", "P::D::b"] {
                let bases = targets(&mut r, name, "Subsetting", "subsettedFeature");
                assert!(
                    bases.contains(&data_values),
                    "{name} subsets Base::dataValues: {bases:?}"
                );
                assert!(
                    !bases.contains(&things),
                    "{name} does not fall back to Base::things"
                );
            }
            // A usage written against the alias reaches the same element.
            let w = r.resolve_qualified("P::w").unwrap();
            let explicit: Vec<Uuid> = r
                .d_owned_relationships(w)
                .into_iter()
                .filter(|&rel| !r.is_implied(rel) && r.element_type(rel) == "Subsetting")
                .filter_map(|rel| {
                    r.element_properties(rel)
                        .get("subsettedFeature")?
                        .get("@id")?
                        .as_str()?
                        .parse()
                        .ok()
                })
                .collect();
            assert_eq!(explicit, vec![data_values]);
            assert!(
                targets(&mut r, "P::w", "Subsetting", "subsettedFeature").is_empty(),
                "the explicit subsetting through the alias needs no implied one"
            );
        }
    }
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
                            r.b.elements[target.0].set_ty("Feature");
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
                            .any(|((source, edge), _)| source == receiver.0 && edge.3 == target_id),
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

/// Timings of what the specialization graph and the retained targets by
/// owner serve, over a 28-unit model on the standard library's snapshot read
/// back: the plan a build makes on the library's, the materialization, and
/// the reads themselves. Printed, not asserted: run with
/// `cargo test --release -p sysmlv2-model --lib graph_reads_timing -- --ignored --nocapture --test-threads=1`.
#[cfg(test)]
mod graph_reads_timing {
    use super::*;
    use crate::{json::ElementRef, model::Model, prepared::PreparedLibrary};
    use std::{path::Path, time::Instant};

    /// Run `step` `reps` times, printing the median and the range in ms.
    fn time(label: &str, reps: usize, mut step: impl FnMut() -> usize) {
        let mut took = Vec::with_capacity(reps);
        let mut out = 0;
        for _ in 0..reps {
            let clock = Instant::now();
            out = std::hint::black_box(step());
            took.push(clock.elapsed().as_secs_f64() * 1e3);
        }
        took.sort_by(f64::total_cmp);
        println!(
            "{label:<32} {:>9.3} ms  [{:.3}..{:.3}]  ({out})",
            took[reps / 2],
            took[0],
            took[reps - 1]
        );
    }

    fn collect(dir: &Path, out: &mut Vec<std::path::PathBuf>) {
        let Ok(entries) = std::fs::read_dir(dir) else {
            return;
        };
        for entry in entries.flatten() {
            let path = entry.path();
            if path.is_dir() {
                collect(&path, out);
            } else if path.extension().is_some_and(|e| e == "sysml") {
                out.push(path);
            }
        }
    }

    #[test]
    #[ignore = "prints timings over the standard library and a 28-unit model"]
    fn graph_reads_timing() {
        let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../spec-refs");
        let mut files = Vec::new();
        collect(&root.join("apollo-11-sysml-v2"), &mut files);
        let library = root.join("SysML-v2-Release/sysml.library");
        if files.is_empty() || !library.exists() {
            return;
        }
        files.sort();
        let bytes = {
            let mut model = Model::new();
            model.load_library_dir(&library).unwrap();
            let prepared = model.prepare_library().unwrap();
            prepared.make_plans();
            prepared.to_bytes(7).unwrap()
        };
        let decoded = Arc::new(PreparedLibrary::from_bytes(&bytes, 7).unwrap());
        let mut model = Model::new();
        Arc::clone(&decoded).install(&mut model).unwrap();
        for file in &files {
            let text = std::fs::read_to_string(file).unwrap();
            model.add_source(file.display().to_string(), &text);
        }
        println!("{} units", files.len());
        time("build", 5, || ResolvedModel::build(&model).b.elements.len());
        time("build + materialize", 5, || {
            let mut r = ResolvedModel::build(&model);
            r.ensure_implied();
            r.b.elements.len()
        });
        let mut r = ResolvedModel::build(&model);
        let names = r.b.implied_names();
        time("plan on the library's", 9, || {
            r.b.supported_implied = None;
            r.b.supported_implied_specializations(&names, true)
                .candidates
                .len()
        });
        let mut r = ResolvedModel::build(&model);
        r.ensure_implied();
        let ids: Vec<Uuid> = r.b.elements.iter().map(|e| e.id).collect();
        let rows = r.b.elements.len();
        let plan = Arc::clone(r.b.supported_implied.as_ref().unwrap());
        let graph = &r.b.implied.as_ref().unwrap().specializations;
        time("materialized graph reads x20", 9, || {
            let mut n = 0;
            for _ in 0..20 {
                for id in &ids {
                    n += graph.get(id).map_or(0, <[Uuid]>::len);
                }
            }
            n
        });
        time("planned graph reads x20", 9, || {
            let mut n = 0;
            for _ in 0..20 {
                for id in &ids {
                    n += plan.graph.get(id).map_or(0, <[Uuid]>::len);
                }
            }
            n
        });
        time("by-owner reads x20", 9, || {
            let mut n = 0;
            for _ in 0..20 {
                for owner in 0..rows {
                    n += plan.by_owner.get(owner).map_or(0, |targets| targets.len());
                }
            }
            n
        });
        let ancestors: Vec<ElementRef> = [
            "Base::Anything",
            "Occurrences::Occurrence",
            "Items::Item",
            "Parts::Part",
            "Ports::Port",
            "Actions::Action",
            "Performances::Performance",
            "Base::DataValue",
        ]
        .iter()
        .filter_map(|name| r.resolve_qualified(name))
        .collect();
        let types: Vec<usize> = (r.b.lib_boundary..r.b.explicit_len())
            .filter(|&e| is_a!(r.b.elements[e], "Type"))
            .collect();
        time("conformance with implied", 5, || {
            let mut n = 0;
            for &e in &types {
                for &ancestor in &ancestors {
                    n += usize::from(r.conforms_with_implied(ElementRef(e), ancestor));
                }
            }
            n
        });
    }
}

#[cfg(test)]
mod prefix_overlay_tests {
    use super::*;
    use crate::{model::Model, prepared::PreparedLibrary};
    use std::path::Path;

    fn collect(dir: &Path, out: &mut Vec<std::path::PathBuf>) {
        let Ok(entries) = std::fs::read_dir(dir) else {
            return;
        };
        for entry in entries.flatten() {
            let path = entry.path();
            if path.is_dir() {
                collect(&path, out);
            } else if path.extension().is_some_and(|e| e == "sysml") {
                out.push(path);
            }
        }
    }

    /// A build on the standard library's snapshot read back reads, for every
    /// row of the plans' frozen graph and every source of the library's own
    /// materialized edges, the frozen row with those edges' targets after
    /// it in order, each once: the rows the edges change lie over the
    /// frozen graph and every other row reads through to it.
    #[test]
    fn a_build_on_a_decoded_library_reads_the_librarys_materialized_edges_over_its_plans_graph() {
        let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../spec-refs");
        let library = root.join("SysML-v2-Release/sysml.library");
        if !library.exists() {
            return;
        }
        let bytes = {
            let mut model = Model::new();
            model.load_library_dir(&library).unwrap();
            let prepared = model.prepare_library().unwrap();
            prepared.make_plans();
            prepared.to_bytes(7).unwrap()
        };
        let decoded = Arc::new(PreparedLibrary::from_bytes(&bytes, 7).unwrap());
        let mut model = Model::new();
        Arc::clone(&decoded).install(&mut model).unwrap();
        // the 28-unit model where the corpus is checked out, else a small one
        let mut files = Vec::new();
        collect(&root.join("apollo-11-sysml-v2"), &mut files);
        files.sort();
        if files.is_empty() {
            model.add_source("v.sysml", "package V { part def A; part a : A; }");
        }
        for file in &files {
            let text = std::fs::read_to_string(file).unwrap();
            model.add_source(file.display().to_string(), &text);
        }
        let mut r = ResolvedModel::build(&model);
        r.ensure_implied();
        let prefix = Arc::clone(r.b.prefix_implied.as_ref().expect("a library's own rows"));
        let plan = Arc::clone(r.b.supported_implied.as_ref().unwrap());
        let frozen = plan.graph.frozen_arc();
        let table = r.b.implied.as_ref().unwrap();
        let own: IdSet<Uuid> = table
            .specializations
            .local_iter()
            .map(|(k, _)| *k)
            .collect();
        let mut keys: Vec<Uuid> = frozen.iter().map(|(k, _)| *k).collect();
        keys.extend(prefix.edges.iter().map(|&(source, _)| source));
        keys.sort_unstable();
        keys.dedup();
        // (no row of the build's own is a library row's: every library row
        // is read through the shared layers)
        assert!(keys.iter().all(|k| !own.contains(k)));
        let mut changed = 0;
        for key in &keys {
            let mut expected: Vec<Uuid> = frozen.get(key).map(<[Uuid]>::to_vec).unwrap_or_default();
            for &(source, target) in &prefix.edges {
                if source == *key && !expected.contains(&target) {
                    expected.push(target);
                }
            }
            changed += usize::from(frozen.get(key) != Some(expected.as_slice()));
            let read = table.specializations.get(key);
            assert_eq!(read.unwrap_or_default(), expected.as_slice(), "row {key}");
            assert_eq!(
                read.is_some(),
                frozen.get(key).is_some() || !expected.is_empty()
            );
        }
        assert!(
            changed > 1000,
            "{changed} rows changed by the library's edges"
        );
    }

    /// A wire plan's retained targets lie on the direct bases' rows, sharing
    /// their ranks, when every owner has bases; an owner without them lays
    /// the targets out over the rows alone, and they read the same.
    #[test]
    fn a_wire_owner_without_bases_lays_the_retained_targets_over_the_rows() {
        let target = Uuid::from_u128(9);
        let wire = |owner: usize| ImpliedWire {
            candidates: CandidateColumns {
                owners: crate::bulk::Ints(Vec::new()),
                spelled: crate::bulk::Bytes(Vec::new()),
                ids: crate::bulk::Ids(Vec::new()),
            },
            kinds: 0,
            retained: Vec::<bool>::new().into(),
            graph: Vec::<(Uuid, Vec<Uuid>)>::new().into(),
            by_owner: vec![(owner, vec![target])].into(),
            library_configuration: true,
            chain_targets: Vec::<(usize, usize)>::new().into(),
            chain_incomplete: crate::bulk::Ints(Vec::new()),
        };
        let bases = ListsByRow::from_sorted(5, &[1, 3], &[1, 1], vec![0usize, 0]).unwrap();
        let read = |owner: usize| {
            SupportedImpliedSpecializations::from_wire(
                wire(owner),
                5,
                crate::layered::Revision::default(),
                crate::layered::Revision::default(),
                HashMap::new(),
                &bases,
            )
            .unwrap()
        };
        let laid = read(3);
        assert_eq!(laid.by_owner.get(3), Some(&[target][..]));
        assert_eq!(laid.by_owner.get(1), None, "a bases row with no target");
        assert_eq!(laid.by_owner.frozen.rows(), 5);
        assert!(
            ListsByRow::from_sorted(5, &[1, 3], &[0, 1], vec![target])
                .unwrap()
                .laid_on(&bases)
                .is_some_and(|shared| shared == *laid.by_owner.frozen)
        );
        let alone = read(2);
        assert_eq!(alone.by_owner.get(2), Some(&[target][..]));
        assert_eq!(alone.by_owner.get(1), None);
        assert_eq!(alone.by_owner.get(3), None);
        assert_eq!(
            *alone.by_owner.frozen,
            ListsByRow::from_sorted(5, &[2], &[1], vec![target]).unwrap(),
            "laid out over the rows alone"
        );
        assert!(
            SupportedImpliedSpecializations::from_wire(
                wire(5),
                5,
                crate::layered::Revision::default(),
                crate::layered::Revision::default(),
                HashMap::new(),
                &bases,
            )
            .is_none(),
            "an owner past the rows"
        );
    }
}

/// What a transition's source is, as far as the caller knows.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(super) enum TransitionSource {
    /// No source written and no action before the transition in its
    /// owner's body to stand as its implicit source.
    None,
    /// The written source resolved to a state.
    State,
    /// The written source resolved to a feature that is no state.
    Other,
    /// A source is written but not resolved (the lowering decides the
    /// heritage before resolution): the owner's kind stands in, a state's
    /// transitions leaving states and an action's leaving actions.
    Unresolved,
}

/// The owning feature membership a usage's owner roles turn on.
pub(super) struct OwnerFacts<'a> {
    /// The owning membership's metaclass.
    pub membership_kind: &'static str,
    /// Its `kind` (`entry`, `do`, `exit`; `trigger`, `effect`, `guard`).
    pub membership_role: Option<&'a str>,
    /// The owner's metaclass.
    pub owner_kind: &'static str,
    /// Whether the owner is a parallel state.
    pub parallel: bool,
}

/// What a usage's roles turn on besides its kind: read off the syntax tree
/// by the lowering, off the rows by the planner and the checked audit.
pub(super) struct RoleFacts<'a> {
    pub ty: &'static str,
    pub composite: bool,
    /// An if action with an else branch.
    pub if_else: bool,
    /// An occurrence usage's `portionKind` (`snapshot` or `timeslice`).
    pub portion_kind: Option<&'a str>,
    pub owner: Option<OwnerFacts<'a>>,
    pub source: TransitionSource,
}

/// The role a transition's guard expression takes: the specification spells
/// it `Actions::TransitionAction::guard`, which the library declares on the
/// kernel's `TransitionPerformance` and the transition action inherits.
pub(super) const TRANSITION_GUARD: &str = "TransitionPerformances::TransitionPerformance::guard";

/// Whether `e` is a transition's guard expression: owned by a
/// `TransitionFeatureMembership` of kind `guard`.
pub(super) fn is_transition_guard(b: &Builder, e: usize) -> bool {
    b.elements[e].owning_relationship.is_some_and(|membership| {
        let relation = &b.elements[membership];
        relation.ty == "TransitionFeatureMembership"
            && relation.props.get("kind").and_then(|v| v.as_str()) == Some("guard")
    })
}

/// The library class an individual definition specializes
/// (`checkOccurrenceDefinitionIndividualSpecialization`).
pub(super) const INDIVIDUAL_BASE: &str = "Occurrences::Life";

/// Whether a feature is declared a portion (`isPortion`), composite by
/// the KerML rule and a portion of its featuring type.
pub(super) fn is_portion(element: &Elem) -> bool {
    element.props.get("isPortion").and_then(|v| v.as_bool()) == Some(true)
}

/// Whether a definition is declared `individual`.
pub(super) fn is_individual(element: &Elem) -> bool {
    element.props.get("isIndividual").and_then(|v| v.as_bool()) == Some(true)
}

/// The library range a usage's default multiplicity subsets (SysML 7.6.3:
/// an end feature, or an attribute, item or port usage its owning type
/// features, with no written multiplicity, subsetting or redefinition, is
/// `[1..1]`).
pub(crate) const DEFAULT_MULTIPLICITY_BASE: &str = "Base::exactlyOne";
/// The library range an individual definition's multiplicity subsets: an
/// `individual` definition classifies at most one individual.
pub(crate) const INDIVIDUAL_MULTIPLICITY_BASE: &str = "Base::zeroOrOne";

/// The library range a default multiplicity member subsets
/// (`Builder::emit_default_multiplicity`, and the same shape in a
/// payload, as the pilot implementation exports it under every usage): an
/// unnamed, bound-less `Multiplicity` owning no relationship of its own,
/// under an OwningMembership of a SysML usage, subsets
/// [`DEFAULT_MULTIPLICITY_BASE`]; of an individual definition,
/// [`INDIVIDUAL_MULTIPLICITY_BASE`]. The metaclass gates the dialect: the
/// KerML lowering never writes the shape, so the same shape under a plain
/// KerML `Feature` in a payload gets nothing here, as a range, a named
/// multiplicity and one that subsets something itself get nothing; their
/// `naturals` obligation is the generic one.
pub(crate) fn default_multiplicity_role(
    multiplicity: &Elem,
    membership: &Elem,
    owner: &Elem,
) -> Option<&'static str> {
    if multiplicity.ty != "Multiplicity"
        || !multiplicity.owned_relationships.is_empty()
        || multiplicity
            .props
            .get("declaredName")
            .is_some_and(|v| !v.is_null())
        || multiplicity
            .props
            .get("declaredShortName")
            .is_some_and(|v| !v.is_null())
        || membership.ty != "OwningMembership"
    {
        return None;
    }
    if conforms(owner.ty, "Usage") {
        Some(DEFAULT_MULTIPLICITY_BASE)
    } else if conforms(owner.ty, "Definition") && is_individual(owner) {
        Some(INDIVIDUAL_MULTIPLICITY_BASE)
    } else {
        None
    }
}

/// The bounds of the library range [`default_multiplicity_role`] names:
/// what the evaluator reads for a synthesized default multiplicity
/// without materializing its implied Subsetting.
pub(crate) fn default_multiplicity_bounds(role: &'static str) -> (i128, Option<i128>) {
    if role == INDIVIDUAL_MULTIPLICITY_BASE {
        (0, Some(1))
    } else {
        (1, Some(1))
    }
}

/// The owner roles [`roles_of`] gives, beside the kind roles of
/// [`implicit_usage_bases`].
#[cfg(test)]
pub(super) const OWNER_ROLES: &[&str] = &[
    "Actions::ifThenElseActions",
    "Occurrences::Occurrence::timeEnclosedOccurrences",
    "Actions::TransitionAction::accepter",
    "Actions::TransitionAction::effect",
    "Actions::Action::subactions",
    "Actions::Action::whileLoops",
    "Actions::Action::forLoops",
    "Actions::Action::ifSubactions",
    "Actions::Action::assignments",
    "Actions::Action::sendSubactions",
    "Actions::Action::terminateSubactions",
    "Actions::Action::acceptSubactions",
    "Actions::Action::decisionTransitions",
    "Parts::Part::ownedActions",
    "Parts::Part::performedActions",
    "Parts::Part::ownedStates",
    "Parts::Part::exhibitedStates",
    "Parts::Part::ownedPorts",
    "States::StateAction::substates",
    "States::StateAction::exclusiveStates",
    "States::StateAction::stateTransitions",
    "Ports::Port::subports",
    "Requirements::RequirementCheck::subrequirements",
    "Requirements::RequirementCheck::concerns",
    "Requirements::RequirementCheck::assumptions",
    "Requirements::RequirementCheck::constraints",
    "Requirements::RequirementCheck::actors",
    "Requirements::RequirementCheck::stakeholders",
    "VerificationCases::VerificationCase::obj::requirementVerifications",
    "Items::Item::checkedConstraints",
    "Calculations::Calculation::subcalculations",
    "Cases::Case::subcases",
    "Cases::Case::actors",
    "AnalysisCases::AnalysisCase::subAnalysisCases",
    "VerificationCases::VerificationCase::subVerificationCases",
    "UseCases::UseCase::subUseCases",
    "UseCases::UseCase::includedUseCases",
    "Views::View::subviews",
    "Views::View::viewRendering",
    "Views::View::viewpointSatisfactions",
    "Views::Rendering::subrenderings",
    "States::StateAction::entryAction",
    "States::StateAction::doAction",
    "States::StateAction::exitAction",
];

/// The library roles a SysML usage takes by its kind (Table 32) and by its
/// place in its owner (SysML 8.3.16–8.3.18): the kind roles of
/// [`implicit_usage_bases`], with an if-else taking `ifThenElseActions` and
/// a transition's trigger taking `Actions::TransitionAction::accepter` in
/// place of `acceptActions`; then, under an owning feature membership of
/// `owner`, a composite action's `Actions::Action::subactions` (not a
/// state's entry or exit action) with its kind's `whileLoops`, `forLoops`,
/// `ifSubactions`, `assignments`, `sendSubactions`, `terminateSubactions`
/// or `acceptSubactions`, a transition effect's `TransitionAction::effect`,
/// a part's `ownedActions`, `performedActions`, `ownedStates`,
/// `exhibitedStates` and `ownedPorts`, a state's `substates` or
/// `exclusiveStates` by the owner's parallelism, a sourced transition's
/// `stateTransitions` (a state's, leaving a state) or `decisionTransitions`
/// (an action's, leaving no state), and a port's `subports`. The lowering
/// gives every usage's heritage these roles, the planner plans them and the
/// checked audit requires them, from this one list; a transition's source
/// is unresolved when the lowering decides, so a state's sourced transitions
/// are its state transitions and an action's its decision transitions
/// there (the spec's rules read the source's kind, which the planner and
/// the audit do).
pub(super) fn roles_of(kind: UsageKind, facts: &RoleFacts) -> Vec<&'static str> {
    let ty = facts.ty;
    let mut roles: Vec<&'static str> = implicit_usage_bases(kind).to_vec();
    if ty == "IfActionUsage" && facts.if_else {
        roles.retain(|role| *role != "Actions::ifThenActions");
        roles.push("Actions::ifThenElseActions");
    }
    // A snapshot or time slice (SysML `checkOccurrenceUsageSnapshotSpecialization`,
    // `checkOccurrenceUsageTimeSliceSpecialization`).
    match facts.portion_kind {
        Some("snapshot") => roles.push("Occurrences::Occurrence::snapshots"),
        Some("timeslice") => roles.push("Occurrences::Occurrence::timeSlices"),
        _ => {}
    }
    let Some(owner) = &facts.owner else {
        return roles;
    };
    if !conforms(owner.membership_kind, "FeatureMembership") {
        return roles;
    }
    let composite = facts.composite;
    let membership_role = owner.membership_role;
    let state_subaction = owner.membership_kind == "StateSubactionMembership";
    let trigger = conforms(ty, "AcceptActionUsage")
        && owner.membership_kind == "TransitionFeatureMembership"
        && membership_role == Some("trigger");
    let effect = conforms(ty, "ActionUsage")
        && owner.membership_kind == "TransitionFeatureMembership"
        && membership_role == Some("effect");
    let owner_kind = owner.owner_kind;
    let in_action = conforms(owner_kind, "ActionDefinition") || conforms(owner_kind, "ActionUsage");
    let in_state = conforms(owner_kind, "StateDefinition") || conforms(owner_kind, "StateUsage");
    let in_part = conforms(owner_kind, "PartDefinition") || conforms(owner_kind, "PartUsage");
    let in_port = conforms(owner_kind, "PortDefinition") || conforms(owner_kind, "PortUsage");
    let in_item = conforms(owner_kind, "ItemDefinition") || conforms(owner_kind, "ItemUsage");
    let in_requirement =
        conforms(owner_kind, "RequirementDefinition") || conforms(owner_kind, "RequirementUsage");
    let in_calculation =
        conforms(owner_kind, "CalculationDefinition") || conforms(owner_kind, "CalculationUsage");
    let in_case = conforms(owner_kind, "CaseDefinition") || conforms(owner_kind, "CaseUsage");
    let in_analysis =
        conforms(owner_kind, "AnalysisCaseDefinition") || conforms(owner_kind, "AnalysisCaseUsage");
    let in_verification = conforms(owner_kind, "VerificationCaseDefinition")
        || conforms(owner_kind, "VerificationCaseUsage");
    let in_use_case =
        conforms(owner_kind, "UseCaseDefinition") || conforms(owner_kind, "UseCaseUsage");
    let in_view = conforms(owner_kind, "ViewDefinition") || conforms(owner_kind, "ViewUsage");
    let in_rendering =
        conforms(owner_kind, "RenderingDefinition") || conforms(owner_kind, "RenderingUsage");
    // An event occurrence in an occurrence (SysML
    // `checkEventOccurrenceUsageSpecialization`).
    if ty == "EventOccurrenceUsage"
        && (conforms(owner_kind, "OccurrenceDefinition") || conforms(owner_kind, "OccurrenceUsage"))
    {
        roles.push("Occurrences::Occurrence::timeEnclosedOccurrences");
    }
    if trigger {
        roles.retain(|role| *role != "Actions::acceptActions");
        roles.push("Actions::TransitionAction::accepter");
    }
    if effect {
        roles.push("Actions::TransitionAction::effect");
    }
    if conforms(ty, "ActionUsage") {
        let subaction =
            composite && in_action && (!state_subaction || membership_role == Some("do"));
        if subaction {
            roles.push("Actions::Action::subactions");
            match ty {
                "WhileLoopActionUsage" => roles.push("Actions::Action::whileLoops"),
                "ForLoopActionUsage" => roles.push("Actions::Action::forLoops"),
                "IfActionUsage" => roles.push("Actions::Action::ifSubactions"),
                "AssignmentActionUsage" => roles.push("Actions::Action::assignments"),
                "SendActionUsage" => roles.push("Actions::Action::sendSubactions"),
                "TerminateActionUsage" => roles.push("Actions::Action::terminateSubactions"),
                "AcceptActionUsage" if !trigger => roles.push("Actions::Action::acceptSubactions"),
                _ => {}
            }
        }
        if composite && in_part {
            roles.push("Parts::Part::ownedActions");
        }
        if conforms(ty, "PerformActionUsage") && in_part {
            roles.push("Parts::Part::performedActions");
        }
    }
    if conforms(ty, "StateUsage") {
        if composite && in_state && !state_subaction {
            roles.push(if owner.parallel {
                "States::StateAction::substates"
            } else {
                "States::StateAction::exclusiveStates"
            });
        }
        if composite && in_part {
            roles.push("Parts::Part::ownedStates");
        }
        if conforms(ty, "ExhibitStateUsage") && in_part {
            roles.push("Parts::Part::exhibitedStates");
        }
    }
    if ty == "TransitionUsage" && composite {
        let state = match facts.source {
            TransitionSource::None => None,
            TransitionSource::State => Some(true),
            TransitionSource::Other => Some(false),
            TransitionSource::Unresolved => Some(in_state),
        };
        match state {
            Some(true) if in_state => roles.push("States::StateAction::stateTransitions"),
            Some(false) if in_action => roles.push("Actions::Action::decisionTransitions"),
            _ => {}
        }
    }
    if conforms(ty, "PortUsage") {
        if in_part {
            roles.push("Parts::Part::ownedPorts");
        }
        if composite && in_port {
            roles.push("Ports::Port::subports");
        }
    }
    // Requirements, constraints and concerns (SysML 8.3.19).
    if conforms(ty, "RequirementUsage") {
        if composite && in_requirement {
            roles.push("Requirements::RequirementCheck::subrequirements");
        }
        if owner.membership_kind == "RequirementVerificationMembership" {
            roles.push("VerificationCases::VerificationCase::obj::requirementVerifications");
        }
    }
    if conforms(ty, "ConcernUsage") && owner.membership_kind == "FramedConcernMembership" {
        roles.push("Requirements::RequirementCheck::concerns");
    }
    if conforms(ty, "ConstraintUsage") {
        if in_item {
            roles.push("Items::Item::checkedConstraints");
        }
        if owner.membership_kind == "RequirementConstraintMembership" {
            roles.push(if membership_role == Some("assumption") {
                "Requirements::RequirementCheck::assumptions"
            } else {
                "Requirements::RequirementCheck::constraints"
            });
        }
    }
    // Calculations and cases (SysML 8.3.20–8.3.24).
    if conforms(ty, "CalculationUsage") && in_calculation {
        roles.push("Calculations::Calculation::subcalculations");
    }
    if conforms(ty, "CaseUsage") && composite && in_case {
        roles.push("Cases::Case::subcases");
    }
    if conforms(ty, "AnalysisCaseUsage") && composite && in_analysis {
        roles.push("AnalysisCases::AnalysisCase::subAnalysisCases");
    }
    if conforms(ty, "VerificationCaseUsage") && composite && in_verification {
        roles.push("VerificationCases::VerificationCase::subVerificationCases");
    }
    if conforms(ty, "UseCaseUsage") {
        if composite && in_use_case {
            roles.push("UseCases::UseCase::subUseCases");
        }
        if conforms(ty, "IncludeUseCaseUsage") && in_use_case {
            roles.push("UseCases::UseCase::includedUseCases");
        }
    }
    if conforms(ty, "PartUsage") {
        if owner.membership_kind == "ActorMembership" {
            roles.push(if in_requirement {
                "Requirements::RequirementCheck::actors"
            } else {
                "Cases::Case::actors"
            });
        }
        if owner.membership_kind == "StakeholderMembership" {
            roles.push("Requirements::RequirementCheck::stakeholders");
        }
    }
    // Views (SysML 8.3.25).
    if conforms(ty, "ViewUsage") && in_view {
        roles.push("Views::View::subviews");
    }
    if conforms(ty, "RenderingUsage") && in_rendering {
        roles.push("Views::Rendering::subrenderings");
    }
    if conforms(ty, "ViewpointUsage") && composite && in_view {
        roles.push("Views::View::viewpointSatisfactions");
    }
    roles
}

/// The library features a usage redefines by its place in its owner (the
/// specification's `redefinesFromLibrary` owner rules): a state's entry,
/// do and exit actions redefine `States::StateAction::entryAction`,
/// `doAction` and `exitAction`
/// (`ActionUsage.checkActionUsageStateActionRedefinition`), and a view's
/// rendering (`render rendering r;`, under a `ViewRenderingMembership`)
/// `Views::View::viewRendering`. The lowering, the planner and the checked
/// audit read this list as they read [`roles_of`]; an unnamed such action
/// is named by what it redefines (`naming::membership_implied_name_of`).
pub(super) fn redefinition_roles_of(facts: &RoleFacts) -> Vec<&'static str> {
    let mut roles = Vec::new();
    let Some(owner) = &facts.owner else {
        return roles;
    };
    if conforms(facts.ty, "ActionUsage") && owner.membership_kind == "StateSubactionMembership" {
        match owner.membership_role {
            Some("entry") => roles.push("States::StateAction::entryAction"),
            Some("do") => roles.push("States::StateAction::doAction"),
            Some("exit") => roles.push("States::StateAction::exitAction"),
            _ => {}
        }
    }
    if conforms(facts.ty, "RenderingUsage") && owner.membership_kind == "ViewRenderingMembership" {
        roles.push("Views::View::viewRendering");
    }
    roles
}

/// The facts [`roles_of`] and [`redefinition_roles_of`] read off the rows
/// for `feature`, under its owning membership and the owner carrying it
/// (`owner`), none of the owner's for a usage owned otherwise; `None` for
/// an element that is no SysML usage, or a flow, whose roles are planned
/// elsewhere.
fn role_facts(
    b: &Builder,
    feature: usize,
    owner: Option<(usize, usize)>,
) -> Option<(UsageKind, RoleFacts<'_>)> {
    let ty = b.elements[feature].ty;
    let kind =
        usage_kind_of(ty, Dialect::Sysml).filter(|_| !matches!(ty, "Flow" | "SuccessionFlow"))?;
    let flag = |b: &Builder, e: usize, key: &str| {
        b.elements[e].props.get(key).and_then(|v| v.as_bool()) == Some(true)
    };
    let source = if ty == "TransitionUsage" {
        transition_source(b, feature, owner.map(|(_, carrier)| carrier))
    } else {
        TransitionSource::None
    };
    let parameters = b.elements[feature]
        .owned_relationships
        .iter()
        .filter(|&&r| b.elements[r].ty == "ParameterMembership")
        .count();
    let owner = owner.map(|(membership, owner)| OwnerFacts {
        membership_kind: b.elements[membership].ty,
        membership_role: b.elements[membership]
            .props
            .get("kind")
            .and_then(|v| v.as_str()),
        owner_kind: b.elements[owner].ty,
        parallel: flag(b, owner, "isParallel"),
    });
    Some((
        kind,
        RoleFacts {
            ty,
            composite: flag(b, feature, "isComposite"),
            if_else: ty == "IfActionUsage" && parameters >= 3,
            portion_kind: b.elements[feature]
                .props
                .get("portionKind")
                .and_then(|v| v.as_str()),
            owner,
            source,
        },
    ))
}

/// [`roles_of`] read off the rows ([`role_facts`]): the library features
/// `feature` subsets by its kind and its place in its owner.
pub(super) fn usage_roles(
    b: &Builder,
    feature: usize,
    owner: Option<(usize, usize)>,
) -> Vec<&'static str> {
    match role_facts(b, feature, owner) {
        Some((kind, facts)) => roles_of(kind, &facts),
        None => Vec::new(),
    }
}

/// [`redefinition_roles_of`] read off the rows ([`role_facts`]): the
/// library features `feature` redefines by its place in its owner.
pub(super) fn usage_redefinition_roles(
    b: &Builder,
    feature: usize,
    owner: Option<(usize, usize)>,
) -> Vec<&'static str> {
    match role_facts(b, feature, owner) {
        Some((_, facts)) => redefinition_roles_of(&facts),
        None => Vec::new(),
    }
}

/// A transition's source, by kind: the one written (`first s`), the member
/// of its first owned membership (the spec's `TransitionUsage::source`), a
/// chain's last link, when that member is an action; else the implicit
/// source of a target transition ([`implicit_transition_source`] among its
/// `carrier`'s members). Resolved through the element-id index when built
/// ([`Builder::ensure_ids`]); unresolved otherwise, or while a reference is
/// pending.
fn transition_source(b: &Builder, transition: usize, carrier: Option<usize>) -> TransitionSource {
    let written = written_transition_source(b, transition);
    if written != TransitionSource::None {
        return written;
    }
    match carrier.map(|carrier| implicit_transition_anchor(b, transition, carrier)) {
        Some(Anchor::Element(source)) if is_a!(b.elements[source], "StateUsage") => {
            TransitionSource::State
        }
        Some(Anchor::Element(_)) => TransitionSource::Other,
        Some(Anchor::Unresolved) => TransitionSource::Unresolved,
        Some(Anchor::None) | None => TransitionSource::None,
    }
}

/// What a target transition's implicit source is at a point of its owner's
/// body (SysML 8.2.2.21): the last action before it that can stand as a
/// predecessor ([`is_previous_candidate`]: no parameter, no transition, no
/// connector but a flow or message), or the written source of the last
/// transition before it, whichever comes later (`if g then a; else b;`
/// after `first x` both leave `x`, after `decide d` both leave `d`).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(super) enum Anchor {
    /// No action and no sourced transition before it.
    None,
    /// The source.
    Element(usize),
    /// The last transition before it writes a source that is not resolved.
    Unresolved,
}

/// The implicit source of `transition`, a target transition (`then t;`,
/// `if g then t;`, `accept … then t;`, `else t;`), among `carrier`'s owned
/// members before it: see [`Anchor`].
pub(super) fn implicit_transition_anchor(b: &Builder, transition: usize, carrier: usize) -> Anchor {
    let mut anchor = Anchor::None;
    for &rel in b.elements[carrier].owned_relationships.iter() {
        if !is_a!(b.elements[rel], "FeatureMembership") {
            continue;
        }
        let Some(&member) = b.elements[rel].children.first() else {
            continue;
        };
        if member == transition {
            return anchor;
        }
        if b.elements[member].ty == "TransitionUsage" {
            match written_transition_source_element(b, member) {
                Ok(Some(source)) => anchor = Anchor::Element(source),
                Ok(None) => {}
                Err(()) => anchor = Anchor::Unresolved,
            }
        } else if is_a!(b.elements[member], "ActionUsage")
            && is_previous_candidate(b, carrier, rel, member)
        {
            anchor = Anchor::Element(member);
        }
    }
    Anchor::None
}

/// Whether `member`, the element `membership` owns in `owner`'s body,
/// stands as the lexical predecessor of what follows it there — the source
/// of a `then` succession, the implicit source of a target transition — as
/// the Pilot Implementation's `UsageUtil.getPreviousFeature` reads one: no
/// parameter (a directed feature of a behavior or step, or a parameter
/// membership's member), no transition, and no connector unless a message.
/// So `decide d; if g then b; then c;` leaves `c`'s source at `d`, past the
/// guarded transition. The Pilot tells a message from a flow by its ends (a
/// message's events are parameter members, a flow's ends end features);
/// this lowering gives both end features and the lift prints both as flows,
/// so every flow usage stands as a predecessor here, a `flow` with ends
/// included (the Pilot skips that one), which keeps `then message` chains
/// leaving the message before them.
pub(super) fn is_previous_candidate(
    b: &Builder,
    owner: usize,
    membership: usize,
    member: usize,
) -> bool {
    let row = &b.elements[member];
    let parameter = is_a!(b.elements[membership], "ParameterMembership")
        || ((is_a!(b.elements[owner], "Behavior") || is_a!(b.elements[owner], "Step"))
            && row
                .props
                .get("direction")
                .is_some_and(|direction| direction.as_str().is_some()));
    !parameter
        && row.ty != "TransitionUsage"
        && (!is_a!(row, "Connector") || is_a!(row, "FlowUsage"))
}

/// The target transitions among the authored rows `from..to` with an
/// implicit source ([`implicit_transition_source`] among the members of
/// the owner `owners` gives their owning membership), each with it: the
/// implied Membership rows the materializer appends after the transition's
/// written relationships, so the source is a member of the transition as
/// the specification's `TransitionUsage::source` reads it.
pub(super) fn implicit_transition_source_rows(
    b: &Builder,
    from: usize,
    to: usize,
    owners: &[Option<usize>],
) -> Vec<(usize, usize)> {
    let mut rows = Vec::new();
    for transition in from..to {
        if b.elements[transition].ty != "TransitionUsage"
            || !b.is_authored(transition)
            || written_transition_source(b, transition) != TransitionSource::None
        {
            continue;
        }
        let Some(membership) = b.elements[transition].owning_relationship else {
            continue;
        };
        let Some(Some(carrier)) = owners.get(membership).copied() else {
            continue;
        };
        if let Some(source) = implicit_transition_source(b, transition, carrier) {
            rows.push((transition, source));
        }
    }
    rows
}

/// [`implicit_transition_anchor`]'s source when it is one.
pub(super) fn implicit_transition_source(
    b: &Builder,
    transition: usize,
    carrier: usize,
) -> Option<usize> {
    match implicit_transition_anchor(b, transition, carrier) {
        Anchor::Element(source) => Some(source),
        Anchor::None | Anchor::Unresolved => None,
    }
}

/// The source a transition writes (`first s`), by kind, from
/// [`written_transition_source_element`].
pub(super) fn written_transition_source(b: &Builder, transition: usize) -> TransitionSource {
    match written_transition_source_element(b, transition) {
        Ok(Some(source)) if is_a!(b.elements[source], "StateUsage") => TransitionSource::State,
        Ok(Some(_)) => TransitionSource::Other,
        Ok(None) => TransitionSource::None,
        Err(()) => TransitionSource::Unresolved,
    }
}

/// The source a transition writes (`first s`): the member of its first
/// owned membership, a chain's last link, when that member is an action
/// (`Ok(None)` otherwise: the link source's empty parameter is first where
/// no source is written); `Err` while the reference is pending or the
/// element-id index is not built ([`Builder::ensure_ids`]).
fn written_transition_source_element(b: &Builder, transition: usize) -> Result<Option<usize>, ()> {
    let Some(&membership) = b.elements[transition]
        .owned_relationships
        .iter()
        .find(|&&r| is_a!(b.elements[r], "Membership"))
    else {
        return Ok(None);
    };
    let ids = b.built_ids();
    // `Some(None)`: a reference the index would resolve, without the index.
    let resolve = |relation: &Elem, key: &str| {
        let id = relation.props.get(key).and_then(|v| v.as_reference())?;
        Some(ids.and_then(|ids| ids.get(&id).copied()))
    };
    let relation = &b.elements[membership];
    let mut source = match resolve(relation, "memberElement") {
        Some(Some(member)) => member,
        Some(None) => return Err(()),
        None => match relation.children.first() {
            Some(&child) => child,
            None => return Err(()),
        },
    };
    for &chaining in b.elements[source].owned_relationships.iter() {
        if b.elements[chaining].ty != "FeatureChaining" {
            continue;
        }
        match resolve(&b.elements[chaining], "chainingFeature") {
            Some(Some(link)) => source = link,
            _ => return Err(()),
        }
    }
    Ok(is_a!(b.elements[source], "ActionUsage").then_some(source))
}

#[cfg(test)]
mod owner_role_heritage_tests {
    use super::*;
    use crate::json::{ResolvedModel, relationship_owners};
    use crate::model::Model;
    use std::path::Path;
    use sysmlv2_syntax::ast::QualifiedName;

    /// Every owner role, with transition sources the lowering reads (a
    /// member declared before the transition, a target transition's last
    /// action before it) and ones it cannot (`v`'s, declared after it: its
    /// owner's kind stands in, as the planner then finds).
    const SOURCE: &str = "package Ro {
        attribute def Sig;
        port def P { in attribute a : ScalarValues::Real; }
        part def Veh {
            port p : P;
            port q : P { port sub : P; }
            action go;
            perform action run;
            state st;
            exhibit state ex;
        }
        action def A {
            action a1;
            action a2;
            attribute x;
            assign x := 1;
            accept sig : Sig;
            if true { action t1; } else { action e1; }
            if false { action t2; }
            while true { action w1; }
            for i in 1..2 { action f1; }
            decide d;
            if true then a1;
            else a2;
            transition first a1 if true then a2;
        }
        state def S parallel { state p1; state p2; }
        state def T {
            entry; then s1;
            state s1 { entry action e1; do action d1; do assign y := 2; attribute y; }
            state s2;
            transition t first s1 accept sig : Sig do action eff then s2;
            transition u first s2 then s1;
            transition v first s3 then s1;
            state s3;
            if true then s1;
            else s2;
        }
        state def W { entry action e0; state s; transition w first e0 then s; }
        action top;
        item def I { part p; item j; constraint c; }
        concern def Cn;
        requirement def RD {
            subject s; actor act; stakeholder sh;
            assume constraint asm; require constraint req;
            requirement sub; frame concern fc : Cn;
        }
        requirement r : RD;
        case def CD { actor act; case sub; }
        analysis def AD { analysis sub; }
        verification def VD { objective { verify r; } verification sub; }
        use case def UD { use case sub; include use case inc : UD; }
        calc def CalcD { calc sub; }
        rendering def RenD { rendering sub; }
        view def ViewD { view sub; render rendering rend : RenD; viewpoint vp; }
        part def Occ { snapshot part snap : Occ; timeslice part slice : Occ; event occurrence ev; }
    }";

    /// The lowering gives a usage's heritage the roles the planner plans
    /// for it, from the one list ([`roles_of`]): every planned role is
    /// among its scope's implied bases, and every owner role there is
    /// planned.
    #[test]
    fn the_heritage_carries_the_planned_owner_roles() {
        let library = Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../../spec-refs/SysML-v2-Release/sysml.library");
        assert!(
            library.exists(),
            "corpus not found at {}: initialize the submodule (see spec-refs/README.md)",
            library.display()
        );
        let mut model = Model::new();
        model.load_library_dir(&library).unwrap();
        let unit = model.add_source("roles.sysml", SOURCE);
        assert!(unit.diagnostics.is_empty(), "{:?}", unit.diagnostics);
        let mut r = ResolvedModel::build(&model);
        r.b.ensure_ids();
        let owners = relationship_owners(&r.b);
        let spell = |qn: &QualifiedName| {
            qn.segments
                .iter()
                .map(|s| s.value.as_str())
                .collect::<Vec<_>>()
                .join("::")
        };
        let mut checked = 0;
        let mut with_owner_roles = 0;
        let elements: Vec<usize> = r.user_elements().map(|e| e.0).collect();
        for e in elements {
            let ty = r.b.elements[e].ty;
            if usage_kind_of(ty, Dialect::Sysml).is_none()
                || matches!(ty, "Flow" | "SuccessionFlow")
            {
                continue;
            }
            let Some(&scope) = r.b.elem_scope.get(&e) else {
                continue;
            };
            let owner = r.b.elements[e]
                .owning_relationship
                .and_then(|m| owners[m].map(|o| (m, o)));
            let mut planned = usage_roles(&r.b, e, owner);
            planned.extend(usage_redefinition_roles(&r.b, e, owner));
            let lowered: Vec<String> = r.b.scopes[scope].implied_bases.iter().map(spell).collect();
            let name = r
                .element_qualified_name(ElementRef(e))
                .unwrap_or_else(|| format!("<{ty}>"));
            for role in &planned {
                assert!(
                    lowered.iter().any(|n| n == role),
                    "{name}: planned {role}, heritage {lowered:?}"
                );
            }
            for base in lowered.iter().filter(|n| OWNER_ROLES.contains(&n.as_str())) {
                assert!(
                    planned.contains(&base.as_str()),
                    "{name}: heritage {base}, planned {planned:?}"
                );
            }
            checked += 1;
            if planned.iter().any(|role| OWNER_ROLES.contains(role)) {
                with_owner_roles += 1;
            }
        }
        assert!(checked >= 30, "{checked} usages");
        assert!(
            with_owner_roles >= 36,
            "{with_owner_roles} with owner roles"
        );
    }
}
