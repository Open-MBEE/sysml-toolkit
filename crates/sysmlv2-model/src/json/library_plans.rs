//! The implied-specialization and positional plans of a prepared library's
//! own rows, made once per prepared library and extended by every build on
//! it with the build's own rows.
//!
//! The planners derive, for every type of a model, the library bases its kind
//! requires and the features its ends and parameters redefine by position.
//! What they derive for a library type reads the library's rows: the type's
//! relationships, its generals', the library's names. It also reads a few
//! facts every row contributes to: whether ids are unique, whether every
//! specialization, typing and featuring names its source, and whether every
//! membership claim names a row. A build whose own rows name no library
//! element as the source of a relationship or the target of an annotation,
//! claim no library row, and leave those facts as the library's rows give
//! them therefore derives for the library's types what the library derives
//! alone. Such a build plans only its own rows on top of the library's plans;
//! any other build plans every row. The plans are the library's in its own
//! graph format: a canonical library's builds extend canonical plans (its
//! positional planning reads the checked import algebra over the library's
//! rows, which a build that claims none of them leaves as they are; pinned by
//! the equality tests under both formats).
//!
//! The plans are made by the first build that plans on the library, on a
//! build of the library with no units of its own, and are not charged to that
//! build's budget: every build on the library then charges the planning of
//! its own rows only.

use super::{
    Builder, ResolvedModel,
    implied::{self, SupportedImpliedSpecializations},
    positional::{
        PlannedLibraryTypes, PlannedTypesWire, PositionalRedefinitions, PositionalRedefinitionsWire,
    },
    structural_index::StoredStructure,
};
use crate::flat::ListsByRow;
use crate::layered::IdSet;
use crate::metaclass::is_a;
use crate::{layered::Revision, prepared::PreparedLibrary};
use std::collections::HashMap;
use std::sync::Arc;

/// A prepared library's own plans (see the module documentation).
pub(crate) struct LibraryPlans {
    /// The library's rows: the plans are those of the rows below this.
    pub(super) rows: usize,
    /// The library's qualified names by name, as the implied planning reads
    /// them: the table every build on the library shares
    /// (see [`Builder::implied_names`]).
    pub(super) names: Arc<HashMap<String, uuid::Uuid>>,
    pub(super) implied: Arc<SupportedImpliedSpecializations>,
    /// Whether a library row is a feature chaining: chain bases are planned
    /// only for a model holding one.
    pub(super) chained: bool,
    /// The direct bases the positional planning starts from, by row, and
    /// the types whose bases are incomplete.
    pub(super) bases: ListsByRow<usize>,
    /// The bases as a table, made on first use and shared: a build's own
    /// rows' lie over it in the static prefix (see
    /// `Builder::planned_direct_bases`).
    bases_table: std::sync::OnceLock<Arc<crate::layered::IdMap<usize, Vec<usize>>>>,
    pub(super) bases_incomplete: IdSet<usize>,
    pub(super) positional: PositionalRedefinitions,
    /// The types the positional planning reached, and what it derived for
    /// each it completed, by row: a build's planning reads these instead of
    /// planning them again.
    pub(super) reached: IdSet<usize>,
    pub(super) planned: PlannedLibraryTypes,
    /// The library's specialization rows: a build's own rows follow them.
    pub(super) spec_rows: usize,
    /// The facts every row contributes to, as the library's rows give them.
    facts: RowFacts,
    /// The build these plans were made on, its plans published: it answers
    /// the inherited memberships of the library's scopes for every build
    /// that sees the library as the library does (see
    /// [`Builder::library_inherited_bindings`]), keeping each answer.
    build: std::sync::Mutex<Builder>,
}

/// The facts the planners read across every row.
#[derive(Clone, Copy, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
struct RowFacts {
    /// No two rows share an id.
    ids_unique: bool,
    /// Some relationship's or featuring's source is missing or not a row.
    sources_incomplete: bool,
    /// Some typing's or subsetting's source is missing or contradictory.
    typing_incomplete: bool,
    /// Some membership claim names nothing (with unique ids only).
    unlocalized: Option<bool>,
}

impl RowFacts {
    /// The facts of `b`'s rows; `None` past the budget.
    fn of(b: &mut Builder, steps: &mut usize) -> Option<(Self, Arc<StoredStructure>)> {
        let ids_unique = b.literal_identities_unique(Some(&mut *steps))?;
        let raw = StoredStructure::for_query(b, steps)?;
        let typing = raw.typing(b, steps)?;
        let unlocalized = if raw.ids_unique {
            Some(!raw.membership_domains(b, steps)?.localized())
        } else {
            None
        };
        let facts = Self {
            ids_unique: ids_unique && raw.ids_unique,
            sources_incomplete: raw.incomplete(),
            typing_incomplete: typing.sources_incomplete,
            unlocalized,
        };
        Some((facts, raw))
    }
}

impl LibraryPlans {
    /// Plan the library's own rows, on a build of it with no units of its
    /// own, in the library's graph format.
    pub(crate) fn plan(library: &Arc<PreparedLibrary>) -> Option<Self> {
        #[cfg(test)]
        PLANNINGS.with(|count| count.set(count.get() + 1));
        let mut model = crate::model::Model::with_graph_format(library.graph_format());
        Arc::clone(library).install(&mut model).ok()?;
        let mut r = ResolvedModel::build(&model);
        let b = &mut r.b;
        // Plan every source row here: these are the plans the library's
        // builds extend. The rows the library materialized are left out of
        // this build, as the planners never read materialized rows.
        b.prepared_from = None;
        b.truncate_prefix_to_source_rows();
        let rows = b.elements.len();
        if b.lib_boundary != rows || b.explicit_len() != rows {
            return None;
        }
        let (facts, _) = RowFacts::of(b, &mut 0)?;
        let (names, mut implied) = b.library_rows_implied();
        let (bases, bases_incomplete) =
            b.positional_direct_bases_from_static_plan(&implied, None)?;
        let bases_map = bases;
        let bases = ListsByRow::from_map(rows, &bases_map);
        if let Some(plan) = Arc::get_mut(&mut implied) {
            plan.lay_owners_on(&bases);
        }
        let (positional, reached, planned) =
            b.plan_positional_reaching(&bases_map, &bases_incomplete);
        let chained = b.elements.iter().any(|e| is_a!(e, "FeatureChaining"));
        let spec_rows = b.spec_targets.len();
        b.supported_implied = Some(Arc::clone(&implied));
        b.positional_redefinitions = Some(positional.clone());
        // The structural scan the facts and the planning read, a copy of
        // the library's rows' own over its source rows alone, is theirs: the
        // inherited memberships the build answers afterwards read none of
        // it (a build reading the plans back from a snapshot never makes
        // one), and a read that did would scan again.
        b.stored_structure = None;
        b.prefix_structure = None;
        // The rows by id the scan tabled go with it: the index the build
        // keeps for its reads lies over the library's table instead (see
        // [`Builder::element_index_of_uuid`]).
        b.id_index = None;
        let build = std::sync::Mutex::new(std::mem::take(&mut r.b));
        Some(Self {
            // A build's own rows start past every row of the library's
            // prefix, the materialized ones included.
            rows: library.builder.lib_boundary,
            names,
            implied,
            chained,
            bases,
            bases_table: std::sync::OnceLock::new(),
            bases_incomplete,
            positional,
            reached,
            planned: PlannedLibraryTypes::from_planned(rows, &planned),
            spec_rows,
            facts,
            build,
        })
    }

    /// The direct bases as a table, shared by every build on the library:
    /// the static prefix's bases lie over it.
    pub(super) fn bases_table(&self) -> Arc<crate::layered::IdMap<usize, Vec<usize>>> {
        Arc::clone(
            self.bases_table
                .get_or_init(|| Arc::new(self.bases.to_map())),
        )
    }

    /// The inherited memberships of the library's scope `s` (see
    /// [`Builder::inherited_bindings`]), as the library's own build gives
    /// them; `None` when that walk is cut short or incomplete.
    fn inherited_bindings(
        &self,
        s: usize,
        include_implied: bool,
    ) -> Option<Arc<super::InheritedBindings>> {
        let mut build = self.build.lock().ok()?;
        let bindings = build.inherited_bindings(s, include_implied);
        (!bindings.truncated && !bindings.incomplete).then_some(bindings)
    }
}

/// The enumeration and variation definitions of a prepared library's own
/// rows with their literals and variants (see [`super::ResolvedModel::enum_types`]),
/// and the body scopes of its elements: a build that has written none of
/// those scopes reads the library's entries from here.
pub(crate) struct LibraryEnumTypes {
    pub(super) entries: Vec<(usize, Vec<usize>)>,
    pub(super) scopes: IdSet<usize>,
}

impl LibraryEnumTypes {
    pub(crate) fn of(library: &Builder) -> Self {
        Self {
            entries: super::enum_entries(library, library.elem_scope.iter()),
            scopes: library.elem_scope.iter().map(|(_, &scope)| scope).collect(),
        }
    }
}

// How many times the library's rows were planned in this thread, for the
// tests that tell a read-back from a planning.
#[cfg(test)]
thread_local!(static PLANNINGS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) });

/// How many times [`LibraryPlans::plan`] ran in this thread.
#[cfg(test)]
pub(crate) fn plannings() -> usize {
    PLANNINGS.with(std::cell::Cell::get)
}

/// A prepared library's own plans as its snapshot carries them, so that a
/// process reading the snapshot does not plan the library again (see
/// [`LibraryPlans::to_wire`] and [`LibraryPlans::from_wire`]). The maps are
/// written sorted by key, so the same plans are written the same way every
/// time.
#[derive(serde::Serialize, serde::Deserialize)]
pub(crate) struct LibraryPlansWire {
    rows: usize,
    spec_rows: usize,
    chained: bool,
    facts: RowFacts,
    implied: implied::ImpliedWire,
    bases: crate::bulk::IndexLists,
    bases_incomplete: crate::bulk::Ints,
    positional: PositionalRedefinitionsWire,
    reached: crate::bulk::Ints,
    planned: PlannedTypesWire,
}

impl LibraryPlans {
    /// These plans as a snapshot carries them; `None` for plans a snapshot
    /// cannot carry (see [`SupportedImpliedSpecializations::to_wire`]).
    pub(crate) fn to_wire(&self) -> Option<LibraryPlansWire> {
        Some(LibraryPlansWire {
            rows: self.rows,
            spec_rows: self.spec_rows,
            chained: self.chained,
            facts: self.facts,
            implied: self.implied.to_wire()?,
            bases: (&self.bases).into(),
            bases_incomplete: crate::bulk::Ints(implied::sorted(
                self.bases_incomplete.iter().copied(),
            )),
            positional: self.positional.to_wire(),
            reached: crate::bulk::Ints(implied::sorted(self.reached.iter().copied())),
            planned: self.planned.to_wire(),
        })
    }

    /// The plans a snapshot carries, read back for the library it was made
    /// of: the library's build is made as [`Self::plan`] makes it, with the
    /// carried plans published instead of planned. `None` when the wire does
    /// not fit the library's rows — a count, a row index or an edge the
    /// planner would not have written — in which case the caller plans.
    pub(crate) fn from_wire(
        library: &Arc<PreparedLibrary>,
        wire: LibraryPlansWire,
    ) -> Option<Self> {
        let mut model = crate::model::Model::with_graph_format(library.graph_format());
        Arc::clone(library).install(&mut model).ok()?;
        let mut r = ResolvedModel::build(&model);
        let b = &mut r.b;
        b.prepared_from = None;
        // Read as the plans were planned: the library's source rows alone.
        b.truncate_prefix_to_source_rows();
        let rows = b.elements.len();
        if wire.rows != library.builder.lib_boundary
            || b.lib_boundary != rows
            || b.explicit_len() != rows
            || wire.spec_rows != b.spec_targets.len()
        {
            return None;
        }
        let in_range = |i: usize| i < rows;
        // (the keys are checked ascending below the rows by the layout)
        let bases = wire.bases.into_rows(rows)?;
        let bases_incomplete = wire.bases_incomplete.0;
        let reached = wire.reached.0;
        let rows_ok = bases.values().iter().all(|&e| in_range(e))
            && bases_incomplete.iter().all(|&e| in_range(e))
            && reached.iter().all(|&e| in_range(e));
        if !rows_ok {
            return None;
        }
        let positional = PositionalRedefinitions::from_wire(wire.positional, rows)?;
        let planned = PlannedLibraryTypes::from_wire(wire.planned, rows)?;
        // The names are the library's own, read as the planning read them:
        // the shared table, which this build fills for every build after it.
        let names = b.implied_names();
        let expression_targets = b.expression_target_names(&names, &mut None)?;
        let implied = SupportedImpliedSpecializations::from_wire(
            wire.implied,
            rows,
            b.elements.observe_revision(),
            b.lib_qnames.observe_revision(),
            expression_targets,
            &bases,
        )?;
        let implied = Arc::new(implied);
        b.supported_implied = Some(Arc::clone(&implied));
        b.positional_redefinitions = Some(positional.clone());
        let build = std::sync::Mutex::new(std::mem::take(&mut r.b));
        Some(Self {
            rows: library.builder.lib_boundary,
            names,
            implied,
            chained: wire.chained,
            bases,
            bases_table: std::sync::OnceLock::new(),
            bases_incomplete: bases_incomplete.into_iter().collect(),
            positional,
            reached: reached.into_iter().collect(),
            planned,
            spec_rows: wire.spec_rows,
            facts: wire.facts,
            build,
        })
    }
}

impl Builder {
    /// The plans of the prepared library this build stands on, when the
    /// planners may extend them with this build's own rows (see the module
    /// documentation): `Some(None)` when they may not, `None` past the budget.
    /// Decided once per state of the rows.
    pub(super) fn library_plans(
        &mut self,
        steps: Option<&mut usize>,
    ) -> Option<Option<Arc<LibraryPlans>>> {
        let Some(prepared) = self.prepared_from.clone() else {
            return Some(None);
        };
        // A name table set since (`ResolvedModel::set_library_names`) plans
        // in another configuration.
        if !self.external_implied_names.is_empty() {
            return Some(None);
        }
        let rows = self.elements.observe_revision();
        let names = self.lib_qnames.observe_revision();
        if let Some((at, names_at, plans)) = &self.library_plans_decided {
            if at.same_as(&rows) && names_at.same_as(&names) {
                return Some(plans.clone());
            }
        }
        let decided = self.decide_library_plans(&prepared, steps)?;
        self.library_plans_decided = Some((rows, names, decided.clone()));
        Some(decided)
    }

    fn decide_library_plans(
        &mut self,
        prepared: &Arc<PreparedLibrary>,
        steps: Option<&mut usize>,
    ) -> Option<Option<Arc<LibraryPlans>>> {
        if self.graph_format != prepared.graph_format()
            || !self.external_implied_names.is_empty()
            || self.library_refs_to_users
            || !self.elements.base_untouched()
            || !Arc::ptr_eq(
                self.elements.base_arc(),
                prepared.builder.elements.base_arc(),
            )
            || self.lib_boundary != self.elements.base_len()
            // A build's own root declarations join the root scope, which
            // the planners do not read.
            || self.scopes.written_rows().any(|scope| scope != 0)
            || !self.spec_targets.base_untouched()
            || !self.spec_resolved.base_untouched()
            || !self.lib_qnames.base_untouched()
        {
            return Some(None);
        }
        let Some(plans) = prepared.library_plans() else {
            return Some(None);
        };
        if plans.rows != self.lib_boundary || self.names_library_sources(plans.rows) {
            return Some(None);
        }
        let mut local = 0;
        let steps = steps.unwrap_or(&mut local);
        let (facts, raw) = RowFacts::of(self, steps)?;
        if facts != plans.facts || !raw.extends_frozen_rows(self, plans.rows, steps)? {
            return Some(None);
        }
        Some(Some(plans))
    }

    /// The inherited memberships of the library's scope `s` as the library's
    /// own build gives them, while this build sees the library as the
    /// library does: it extends the library's plans, its positional plan (for
    /// `include_implied`) is the library's extended, it accepted no dynamic
    /// heritage, and it is not planning. A library scope's enumeration reads
    /// the library's scopes, rows and names, its bases (the implied ones from
    /// the implied plan) and its features' redefinitions (the positional ones
    /// from the positional plan), all of which the build then has as the
    /// library's.
    pub(super) fn library_inherited_bindings(
        &mut self,
        s: usize,
        include_implied: bool,
    ) -> Option<Arc<super::InheritedBindings>> {
        if s >= self.scope_floor
            || !self.semantic_ready
            || self.positional_planning
            || self.static_planning
            || self.dynamic_graph.is_some()
            || (include_implied
                && !(self.positional_from_library && self.positional_redefinitions.is_some()))
        {
            return None;
        }
        let plans = self.library_plans(None)??;
        plans.inherited_bindings(s, include_implied)
    }

    /// Whether an authored row from `floor` on names a row below it as the
    /// source of a relationship (which the derivations of that row read) or
    /// as an annotated element. Materialized implied relationships, which the
    /// planners do not read, name library types as their sources by design.
    fn names_library_sources(&mut self, floor: usize) -> bool {
        const SOURCES: [&str; 16] = [
            "specific",
            "subclassifier",
            "typedFeature",
            "subsettingFeature",
            "redefiningFeature",
            "referencingFeature",
            "crossingFeature",
            "conjugatedType",
            "featureOfType",
            "featureChained",
            "featureInverted",
            "typeDisjoined",
            "typeDifferenced",
            "typeIntersected",
            "typeUnioned",
            "annotatedElement",
        ];
        let mut named = Vec::new();
        for row in (floor..self.explicit_len()).filter(|&row| self.is_authored(row)) {
            // One pass over the row's entries rather than a search per key:
            // a row holds few entries, and the sources are boolean-free.
            for (key, value) in self.elements[row].props.entries.iter() {
                if !SOURCES.contains(&key.name()) {
                    continue;
                }
                if let Some(id) = value.as_reference() {
                    named.push(id);
                } else if let Some(values) = value.as_array() {
                    named.extend(values.iter().filter_map(|v| v.as_reference()));
                }
            }
        }
        named
            .into_iter()
            .any(|id| self.element_index_of_uuid(id).is_some_and(|e| e < floor))
    }
}

/// The library plans a build decided on, with the state of the rows and of
/// the library names it decided for.
pub(super) type LibraryPlansDecided = (Revision, Revision, Option<Arc<LibraryPlans>>);

#[cfg(test)]
mod tests {
    use super::super::positional::PlannedTypes;
    use super::*;
    use crate::layered::IdMap;
    use crate::model::{GraphFormat, Model};
    use std::path::Path;

    /// The plans of every row of `r`'s build, as the planners make them now:
    /// the implied plan, the positional direct bases, and the positional plan
    /// (through the unbounded and the bounded entry).
    struct Planned {
        implied: Arc<SupportedImpliedSpecializations>,
        bases: (IdMap<usize, Vec<usize>>, IdSet<usize>),
        positional: PositionalRedefinitions,
        bounded: Option<PositionalRedefinitions>,
        extended: bool,
    }

    fn reset(b: &mut Builder) {
        b.supported_implied = None;
        b.positional_redefinitions = None;
        b.library_plans_decided = None;
        b.drop_inherited_memos();
    }

    fn planned(r: &mut ResolvedModel) -> Planned {
        reset(&mut r.b);
        let extended = matches!(r.b.library_plans(None), Some(Some(_)));
        let bases = r.b.positional_direct_bases();
        let implied = Arc::clone(r.b.supported_implied.as_ref().unwrap());
        r.b.ensure_positional_redefinitions();
        let positional = r.b.positional_redefinitions.clone().unwrap();
        reset(&mut r.b);
        let mut steps = 0;
        let bounded =
            r.b.ensure_positional_redefinitions_with_budget(&mut steps)
                .then(|| r.b.positional_redefinitions.clone().unwrap());
        Planned {
            implied,
            bases,
            positional,
            bounded,
            extended,
        }
    }

    /// Build `model` on its prepared library and plan it extending the
    /// library's plans, then plan every row of the same build: equal plans.
    /// Returns whether the build extended the library's plans.
    fn assert_extended_plans_equal_whole(model: &Model, label: &str) -> bool {
        let mut r = ResolvedModel::build(model);
        if r.b.prepared_from.is_none() {
            return false;
        }
        let extended = planned(&mut r);
        let prepared = r.b.prepared_from.take();
        let whole = planned(&mut r);
        r.b.prepared_from = prepared;
        assert!(!whole.extended);
        if let Some(difference) = extended.implied.difference(&whole.implied) {
            panic!("{label}: implied plans differ: {difference}");
        }
        assert!(
            extended.bases == whole.bases,
            "{label}: direct bases differ"
        );
        assert!(
            extended.positional.targets == whole.positional.targets
                && extended.positional.incomplete == whole.positional.incomplete,
            "{label}: positional plans differ"
        );
        match (&extended.bounded, &whole.bounded) {
            (Some(a), Some(b)) => assert!(
                a.targets == b.targets && a.incomplete == b.incomplete,
                "{label}: bounded positional plans differ"
            ),
            // The extended planning charges this build's rows only.
            (Some(_), None) => {}
            (None, _) => panic!("{label}: the bounded extended planning ran out"),
        }
        extended.extended
    }

    /// The enumeration entries a build reads from its prepared library equal
    /// a walk of every body scope, and the constraints of the user units built
    /// alone equal every constraint filtered to them.
    fn assert_verify_inputs_equal_whole(model: &Model, label: &str) {
        let mut r = ResolvedModel::build(model);
        let shared = r.enum_types();
        let prepared = r.b.prepared_from.take();
        let whole = r.enum_types();
        r.b.prepared_from = prepared;
        assert_eq!(shared, whole, "{label}: enumeration entries differ");
        let user = |unit: usize| !model.is_library_unit(unit);
        let render = |cs: Vec<super::super::ConstraintInfo>| -> Vec<String> {
            cs.into_iter().map(|c| format!("{c:?}")).collect()
        };
        let kept = render(r.constraints_where(user));
        let filtered = render(
            r.constraints()
                .into_iter()
                .filter(|c| user(c.unit))
                .collect(),
        );
        assert_eq!(kept, filtered, "{label}: user constraints differ");
    }

    /// The lookup tables a build keeps over its prepared library's — its
    /// specialization rows by owner, its relationships' owners, its valued
    /// chain redefinitions — equal tables of every row of the same build.
    /// Returns whether the build read the library's tables.
    fn assert_lookup_tables_equal_whole(model: &Model, label: &str) -> bool {
        let mut r = ResolvedModel::build(model);
        let tables = |r: &mut ResolvedModel| {
            r.b.spec_index = None;
            r.b.ensure_spec_index();
            r.b.chain_redefinitions = None;
            let chains = r.b.chain_redefinitions();
            r.rel_owner = Default::default();
            r.ensure_rel_owner();
            let owners: Vec<Option<usize>> = r.rel_owner.iter().copied().collect();
            r.b.mult_index = None;
            r.b.declared_multiplicity_of(0);
            let declared = r.b.mult_index.take().unwrap().1;
            let multiplicities = (declared, r.b.multiplicity_range_rows());
            (
                r.b.spec_index.take().unwrap(),
                chains,
                owners,
                multiplicities,
            )
        };
        let used = r.b.prepared_from.is_some() && r.b.library_chain_redefinitions().is_some();
        let (spec, chains, owners, (declared, ranges)) = tables(&mut r);
        let prepared = r.b.prepared_from.take();
        let (whole_spec, whole_chains, whole_owners, (whole_declared, whole_ranges)) =
            tables(&mut r);
        r.b.prepared_from = prepared;
        assert!(whole_spec.base_arc().is_empty() && whole_chains.base_arc().is_empty());
        for e in 0..r.b.elements.len() {
            assert_eq!(
                spec.get(&e),
                whole_spec.get(&e),
                "{label}: specializations of {e}"
            );
            assert_eq!(
                chains.get(&e),
                whole_chains.get(&e),
                "{label}: chains of {e}"
            );
            assert_eq!(
                declared.get(&e),
                whole_declared.get(&e),
                "{label}: multiplicity of {e}"
            );
            assert_eq!(
                ranges.get(&e),
                whole_ranges.get(&e),
                "{label}: range rows of {e}"
            );
        }
        assert_eq!(chains.is_empty(), whole_chains.is_empty(), "{label}");
        assert!(
            owners == whole_owners,
            "{label}: relationship owners differ"
        );
        used && !spec.base_arc().is_empty()
    }

    /// The inherited memberships a build reads from its prepared library's
    /// build for the library's scopes, enumerating its own types' as the
    /// checks do, equal those the same build enumerates itself. Returns how
    /// many of the library's scopes it read.
    fn assert_inherited_equal_whole(model: &Model, label: &str) -> usize {
        let mut r = ResolvedModel::build(model);
        let scopes: Vec<usize> = (r.b.lib_boundary..r.b.explicit_len())
            .filter(|&e| is_a!(r.b.elements[e], "Type"))
            .filter_map(|e| r.b.elem_scope.get(&e).copied())
            .collect();
        type Answers = Vec<Arc<super::super::InheritedBindings>>;
        type Cached = IdMap<usize, Arc<super::super::InheritedBindings>>;
        let enumerate = |r: &mut ResolvedModel| -> (Answers, Cached) {
            r.b.drop_inherited_memos();
            let answers = scopes
                .iter()
                .map(|&s| r.b.inherited_bindings(s, true))
                .collect();
            let cached =
                r.b.inherited_cache
                    .iter()
                    .filter(|((_, implied), _)| *implied)
                    .map(|((s, _), bindings)| (*s, Arc::clone(bindings)))
                    .collect();
            (answers, cached)
        };
        let same = |a: &super::super::InheritedBindings, b: &super::super::InheritedBindings| {
            a.members == b.members
                && a.alias_rels == b.alias_rels
                && a.membership_order == b.membership_order
                && a.truncated == b.truncated
                && a.incomplete == b.incomplete
                && a.implicit_redefinitions == b.implicit_redefinitions
        };
        let (answers, cached) = enumerate(&mut r);
        let prepared = r.b.prepared_from.take();
        let (own_answers, own_cached) = enumerate(&mut r);
        r.b.prepared_from = prepared;
        for (i, (shared, own)) in answers.iter().zip(&own_answers).enumerate() {
            assert!(
                same(shared, own),
                "{label}: inherited memberships of scope {} differ",
                scopes[i]
            );
        }
        let mut read = 0;
        for (s, shared) in &cached {
            if *s < r.b.scope_floor {
                read += 1;
            }
            if let Some(own) = own_cached.get(s) {
                assert!(
                    same(shared, own),
                    "{label}: kept memberships of scope {s} differ"
                );
            }
        }
        read
    }

    /// Both graph formats: a library's plans are made in its own.
    const FORMATS: [GraphFormat; 2] = [GraphFormat::LegacyV2, GraphFormat::CanonicalV3];

    fn prepared(units: &[(&str, &str)]) -> Arc<PreparedLibrary> {
        prepared_in(GraphFormat::LegacyV2, units)
    }

    fn prepared_in(format: GraphFormat, units: &[(&str, &str)]) -> Arc<PreparedLibrary> {
        let mut base = Model::with_graph_format(format);
        for (name, text) in units {
            let parsed = base.add_library_source(*name, text);
            assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        }
        base.prepare_library().unwrap()
    }

    fn on(library: &Arc<PreparedLibrary>, units: &[(&str, &str)]) -> Model {
        let mut model = Model::with_graph_format(library.graph_format());
        Arc::clone(library).install(&mut model).unwrap();
        for (name, text) in units {
            let parsed = model.add_source(*name, text);
            assert!(
                parsed.diagnostics.is_empty(),
                "{name}: {:?}",
                parsed.diagnostics
            );
        }
        model
    }

    const KERNEL: &str = "package L {
        behavior B { in x; in y; out z; }
        behavior C :> B { in a; }
        function F { in p; return r; }
        function G :> F { in q; return s; }
        assoc A { end e1; end e2; }
        assoc A2 :> A { end f1; end f2; }
        classifier K { feature f : K; feature g : K; feature h chains f.g; }
    }";
    const KERNEL_USER: &str = "package U {
        behavior D :> L::C { in m; in n; out o; }
        function H :> L::G { in u; return w; }
        assoc A3 :> L::A2 { end g1; end g2; }
        classifier M :> L::K { feature k chains f.f; }
        step s : L::B { in b1; in b2; }
    }";

    #[test]
    fn a_build_extends_its_librarys_plans_like_a_plan_of_every_row() {
        for format in FORMATS {
            let library = prepared_in(format, &[("lib.kerml", KERNEL)]);
            let model = on(&library, &[("user.kerml", KERNEL_USER)]);
            assert!(
                assert_extended_plans_equal_whole(&model, "kernel"),
                "{format:?}"
            );
            // A second build shares the library's plans.
            let first = library.library_plans().unwrap();
            let mut r = ResolvedModel::build(&on(&library, &[("user.kerml", KERNEL_USER)]));
            let Some(Some(second)) = r.b.library_plans(None) else {
                panic!("{format:?}: extended");
            };
            assert!(Arc::ptr_eq(&first, &second));
        }
    }

    /// A build of one graph format on a library prepared in the other
    /// cannot be installed, so a build never extends plans of another
    /// format; the guard reads the library's format all the same.
    #[test]
    fn a_build_extends_plans_of_its_own_graph_format_only() {
        let library = prepared_in(GraphFormat::CanonicalV3, &[("lib.kerml", KERNEL)]);
        let mut other = Model::with_graph_format(GraphFormat::LegacyV2);
        assert!(Arc::clone(&library).install(&mut other).is_err());
        let mut r = ResolvedModel::build(&on(&library, &[("user.kerml", KERNEL_USER)]));
        r.b.graph_format = GraphFormat::LegacyV2;
        assert_eq!(r.b.library_plans(None).map(|p| p.is_some()), Some(false));
    }

    /// The library's planning keeps what it derived for every type it
    /// completed, and a build's planning reads those instead of planning the
    /// library's types again: the build's own plan still equals a planning of
    /// every row.
    #[test]
    fn a_build_plans_only_its_own_types_over_the_librarys_derivations() {
        let library = prepared(&[("lib.kerml", KERNEL)]);
        let plans = library.library_plans().unwrap();
        let complete: Vec<usize> = plans
            .reached
            .iter()
            .copied()
            .filter(|e| !plans.positional.incomplete.contains(e))
            .collect();
        assert!(!complete.is_empty());
        for e in &complete {
            assert!(plans.planned.has(*e), "library type {e} kept");
        }
        let model = on(&library, &[("user.kerml", KERNEL_USER)]);
        assert!(assert_extended_plans_equal_whole(&model, "kernel"));
    }

    /// A user relationship naming a library element as its source changes
    /// what the planners derive for that element: the build plans every row.
    #[test]
    fn a_row_specializing_a_library_type_plans_every_row() {
        for format in FORMATS {
            let library = prepared_in(format, &[("lib.kerml", KERNEL)]);
            for user in [
                "package U { specialization S subclassifier L::K specializes L::B; }",
                "package U { featuring L::K::f by L::B; }",
                "package U { metaclass N; @N about L::K; }",
            ] {
                let model = on(&library, &[("user.kerml", user)]);
                assert!(
                    !assert_extended_plans_equal_whole(&model, user),
                    "{format:?}: {user}"
                );
            }
        }
    }

    /// A user row sharing a library row's id makes ids non-unique, which the
    /// planners read for every row: the build plans every row.
    #[test]
    fn a_row_sharing_a_library_id_plans_every_row() {
        let library = prepared(&[("lib.kerml", KERNEL)]);
        let model = on(&library, &[("user.kerml", KERNEL_USER)]);
        let mut r = ResolvedModel::build(&model);
        let b_row = r.resolve_qualified("L::B").unwrap().0;
        let d_row = r.resolve_qualified("U::D").unwrap().0;
        r.b.elements[d_row].id = r.b.elements[b_row].id;
        r.b.id_index = None;
        r.b.stored_structure = None;
        assert_eq!(r.b.library_plans(None).map(|p| p.is_some()), Some(false));
    }

    /// A library decoded from a prepared snapshot, as the browser binding
    /// loads the standard library, plans the same way.
    #[test]
    fn a_build_on_a_decoded_library_extends_its_plans() {
        for format in FORMATS {
            let library = prepared_in(format, &[("lib.kerml", KERNEL)]);
            let decoded =
                Arc::new(PreparedLibrary::from_bytes(&library.to_bytes(7).unwrap(), 7).unwrap());
            let model = on(&decoded, &[("user.kerml", KERNEL_USER)]);
            assert!(
                assert_extended_plans_equal_whole(&model, "decoded"),
                "{format:?}"
            );
            let source = on(&library, &[("user.kerml", KERNEL_USER)]);
            let (mut a, mut b) = (ResolvedModel::build(&model), ResolvedModel::build(&source));
            let (a, b) = (planned(&mut a), planned(&mut b));
            assert!(a.implied.difference(&b.implied).is_none());
            assert!(a.positional.targets == b.positional.targets);
        }
    }

    /// The plans' build is cut to the library's source rows; its index of
    /// rows by id lies over the library's table, which covers the
    /// materialized rows too, below the cut, instead of tabling the rows
    /// again: every source row is found, and a materialized row's id is
    /// not a row of the build. So for the plans read back from a snapshot
    /// and for the plans made by planning.
    #[test]
    fn the_plans_build_indexes_its_rows_over_the_librarys_table() {
        let library = prepared(&[("lib.kerml", KERNEL)]);
        library.make_plans();
        let wire = library.library_plans().unwrap().to_wire().unwrap();
        let decoded =
            Arc::new(PreparedLibrary::from_bytes(&library.to_bytes(7).unwrap(), 7).unwrap());
        let table = decoded.builder.prefix_ids.as_ref().unwrap();
        for (plans, how) in [
            (
                LibraryPlans::from_wire(&decoded, wire).unwrap(),
                "read back",
            ),
            (LibraryPlans::plan(&decoded).unwrap(), "planned"),
        ] {
            let mut b = plans.build.into_inner().unwrap();
            let rows = b.elements.len();
            assert!(
                rows < table.len(),
                "{how}: the library materialized rows past its source rows"
            );
            let tabled = crate::json::id_index_tabled();
            assert_eq!(b.literal_identities_unique(None), Some(true), "{how}");
            assert_eq!(
                crate::json::id_index_tabled() - tabled,
                0,
                "{how}: no row is tabled again"
            );
            let index = Arc::clone(b.id_index.as_ref().unwrap());
            assert!(index.lies_over(table), "{how}");
            assert_eq!(index.len(), rows, "{how}");
            assert_eq!(index.iter().count(), rows, "{how}");
            assert!(index.iter().all(|(_, &row)| row < rows), "{how}");
            for row in 0..rows {
                let id = b.elements[row].id;
                assert_eq!(b.element_index_of_uuid(id), Some(row), "{how}");
            }
            let materialized = decoded.builder.elements[rows].id;
            assert_eq!(index.get(&materialized), None, "{how}");
            assert_eq!(
                b.element_index_of_uuid(materialized),
                None,
                "{how}: a materialized row is not the build's"
            );
        }
    }

    /// Materializing the implied relationships appends rows naming library
    /// types as their sources; the planning after it still extends the
    /// library's plans, and still equals a planning of every row.
    #[test]
    fn materialized_relationships_leave_the_build_extending_its_librarys_plans() {
        let library = prepared(&[("lib.kerml", KERNEL)]);
        let model = on(&library, &[("user.kerml", KERNEL_USER)]);
        let mut r = ResolvedModel::build(&model);
        r.ensure_implied();
        assert!(r.b.implied.is_some());
        let extended = planned(&mut r);
        assert!(
            extended.extended,
            "the implied rows are not this build's own"
        );
        let prepared = r.b.prepared_from.take();
        let whole = planned(&mut r);
        r.b.prepared_from = prepared;
        assert!(extended.implied.difference(&whole.implied).is_none());
        assert!(extended.positional.targets == whole.positional.targets);
        assert!(extended.positional.incomplete == whole.positional.incomplete);
    }

    /// Enumerations and variations in the library and in the build, and
    /// asserts taking their bodies from library and user definitions.
    #[test]
    fn verify_inputs_read_the_library_once_like_a_walk_of_every_row() {
        let library = prepared(&[(
            "lib.sysml",
            "package L { enum def Color { red; green; } variation part def V { variant part a; } \
             constraint def Pos { in x; x > 0 } constraint def Small { in x; x < 9 } \
             part def P { attribute w = 2; assert constraint { w > 1 } } }",
        )]);
        let model = on(
            &library,
            &[(
                "user.sysml",
                "package U { enum def Shade { dark; light; } part def Q :> L::P { attribute c : L::Color = L::Color::red; } \
                 constraint def Mine { in y; y > 1 } part q : Q { assert constraint p : L::Pos; assert constraint m : Mine; \
                 assert constraint { c == L::Color::red } } }",
            )],
        );
        assert_verify_inputs_equal_whole(&model, "fixture");
        let r = ResolvedModel::build(&model);
        let shared = library.library_enum_types();
        assert!(
            r.b.scopes
                .written_rows()
                .all(|scope| !shared.scopes.contains(&scope)),
            "the build reads the library's entries"
        );
        let names: Vec<String> = r
            .enum_types()
            .into_iter()
            .filter_map(|(e, _)| r.element_name(e).map(str::to_string))
            .collect();
        assert!(
            names.contains(&"Color".to_string()) && names.contains(&"Shade".to_string()),
            "{names:?}"
        );
    }

    const CHAINS: &str = "package L {
        part def A { attribute x; attribute y; }
        part def B { part a : A; }
        part def C :> B { attribute :>> a.x = 3; }
    }";
    const CHAINS_USER: &str = "package U {
        part def D :> L::B { attribute :>> a.y = 4; }
        part d : L::C { attribute :>> a.y = 5; }
    }";

    #[test]
    fn a_builds_lookup_tables_over_its_librarys_equal_tables_of_every_row() {
        let library = prepared(&[("lib.sysml", CHAINS)]);
        let model = on(&library, &[("user.sysml", CHAINS_USER)]);
        assert!(assert_lookup_tables_equal_whole(&model, "chains"));
        assert!(!library.library_chain_redefinitions().is_empty());
        let decoded =
            Arc::new(PreparedLibrary::from_bytes(&library.to_bytes(7).unwrap(), 7).unwrap());
        let model = on(&decoded, &[("user.sysml", CHAINS_USER)]);
        assert!(assert_lookup_tables_equal_whole(&model, "decoded"));
    }

    /// A user row taking a library row's id answers that id in the build's
    /// lookups: the build indexes the chains of every row.
    #[test]
    fn a_row_sharing_a_library_id_indexes_the_chains_of_every_row() {
        let library = prepared(&[("lib.sysml", CHAINS)]);
        let model = on(&library, &[("user.sysml", CHAINS_USER)]);
        let mut r = ResolvedModel::build(&model);
        assert!(r.b.library_chain_redefinitions().is_some());
        let a_row = r.resolve_qualified("L::A::x").unwrap().0;
        let d_row = r.resolve_qualified("U::D").unwrap().0;
        r.b.elements[d_row].id = r.b.elements[a_row].id;
        r.b.id_index = None;
        assert!(r.b.library_chain_redefinitions().is_none());
    }

    fn standard_library() -> Option<Arc<PreparedLibrary>> {
        standard_library_in(GraphFormat::LegacyV2)
    }

    fn standard_library_in(format: GraphFormat) -> Option<Arc<PreparedLibrary>> {
        let path = Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../../spec-refs/SysML-v2-Release/sysml.library");
        if !path.exists() {
            return None;
        }
        let mut model = Model::with_graph_format(format);
        model.load_library_dir(&path).unwrap();
        Some(model.prepare_library().unwrap())
    }

    const VEHICLE: &str = "package V {
        private import ISQ::*;
        private import SI::*;
        private import ScalarValues::*;
        part def Chassis { attribute mass :> ISQ::mass; }
        part def Crawler {
            part chassis : Chassis { :>> mass default 0.1 [kg]; }
            attribute vehicleMass : MassValue = chassis.mass;
            port p : P;
        }
        port def P { in item fuel; }
        requirement def MassLimit {
            subject crawler : Crawler;
            attribute limit : MassValue;
            require constraint { crawler.vehicleMass < limit }
        }
        calc def Total { in a : Real; in b : Real; return : Real = a + b; }
        calc def Twice :> Total { in x : Real; in y : Real; }
        action def Drive { in speed : Real; out distance : Real; }
        action def Cruise :> Drive {
            action start;
            then action go;
            first start then go;
        }
        connection def Link { end a : Crawler; end b : Crawler; }
        part fleet {
            part c1 : Crawler; part c2 : Crawler;
            connection l : Link connect c1 to c2;
            attribute :>> c1.chassis.mass = 2.5 [kg];
        }
        variation part def Kind { variant part small : Crawler; variant part big : Crawler; }
        analysis def MassAnalysis {
            subject crawler : Crawler;
            return calculatedMass : MassValue = crawler.vehicleMass;
            objective { require constraint { calculatedMass < 1 [kg] } }
        }
        part ctx {
            part tiny : Crawler;
            requirement limit : MassLimit { attribute :>> limit = 0.5 [kg]; }
            satisfy limit by tiny;
        }
    }";

    #[test]
    fn builds_on_the_standard_library_extend_its_plans_like_plans_of_every_row() {
        for format in FORMATS {
            let Some(library) = standard_library_in(format) else {
                return;
            };
            let model = on(&library, &[("vehicle.sysml", VEHICLE)]);
            let label = format!("vehicle {format:?}");
            assert!(assert_extended_plans_equal_whole(&model, &label));
            assert!(assert_lookup_tables_equal_whole(&model, &label));
            assert!(assert_inherited_equal_whole(&model, &label) > 0);
        }
    }

    /// Every directory of the corpus's example, training and validation
    /// models as one workspace, and the external Apollo model when present,
    /// on the prepared standard library.
    #[test]
    fn corpus_workspaces_extend_the_standard_librarys_plans_like_plans_of_every_row() {
        for format in FORMATS {
            corpus_workspaces_extend_the_plans_in(format);
        }
    }

    fn corpus_workspaces_extend_the_plans_in(format: GraphFormat) {
        let Some(library) = standard_library_in(format) else {
            return;
        };
        let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../spec-refs");
        let mut workspaces: std::collections::BTreeMap<
            std::path::PathBuf,
            Vec<std::path::PathBuf>,
        > = Default::default();
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
        let mut files = Vec::new();
        for dir in ["examples", "training", "validation"] {
            collect(
                &root.join("SysML-v2-Release/sysml/src").join(dir),
                &mut files,
            );
        }
        for file in files {
            let dir = file.parent().unwrap().to_path_buf();
            workspaces.entry(dir).or_default().push(file);
        }
        let mut apollo = Vec::new();
        collect(&root.join("apollo-11-sysml-v2"), &mut apollo);
        if !apollo.is_empty() {
            workspaces.insert(root.join("apollo-11-sysml-v2"), apollo);
        }
        let (mut checked, mut extended, mut shared, mut inherited) = (0, 0, 0, 0);
        for (dir, mut files) in workspaces {
            files.sort();
            let mut model = Model::with_graph_format(format);
            Arc::clone(&library).install(&mut model).unwrap();
            for file in &files {
                let text = std::fs::read_to_string(file).unwrap();
                model.add_source(
                    file.file_name().unwrap().to_string_lossy().into_owned(),
                    &text,
                );
            }
            let label = format!("{} {format:?}", dir.display());
            checked += 1;
            assert_verify_inputs_equal_whole(&model, &label);
            if assert_lookup_tables_equal_whole(&model, &label) {
                shared += 1;
            }
            inherited += assert_inherited_equal_whole(&model, &label);
            if assert_extended_plans_equal_whole(&model, &label) {
                extended += 1;
            }
        }
        assert!(checked > 80, "{format:?}: {checked} workspaces");
        assert!(
            shared * 10 >= checked * 9,
            "{format:?}: {shared} of {checked} shared"
        );
        assert!(
            inherited > checked,
            "{format:?}: {inherited} library scopes read"
        );
        assert!(
            extended * 10 >= checked * 9,
            "{format:?}: {extended} of {checked} extended"
        );
    }

    /// The first field in which two plans of the same library differ, the
    /// builds aside.
    fn plans_difference(a: &LibraryPlans, b: &LibraryPlans) -> Option<String> {
        let differs = |what: &str, same: bool| (!same).then(|| what.to_string());
        a.implied
            .difference(&b.implied)
            .or_else(|| {
                differs(
                    "positional targets",
                    a.positional.targets == b.positional.targets,
                )
            })
            .or_else(|| {
                differs(
                    "positional incomplete",
                    a.positional.incomplete == b.positional.incomplete,
                )
            })
            .or_else(|| differs("bases", a.bases == b.bases))
            .or_else(|| differs("bases incomplete", a.bases_incomplete == b.bases_incomplete))
            .or_else(|| differs("reached", a.reached == b.reached))
            .or_else(|| differs("facts", a.facts == b.facts))
            .or_else(|| differs("rows", a.rows == b.rows))
            .or_else(|| differs("spec rows", a.spec_rows == b.spec_rows))
            .or_else(|| differs("chained", a.chained == b.chained))
            .or_else(|| differs("names", a.names == b.names))
            .or_else(|| differs("planned types", a.planned.types() == b.planned.types()))
    }

    /// A library with plans of every kind a snapshot carries: implied
    /// specializations (the parts specialize `Parts::Part`, the part usages
    /// subset `Parts::parts`; library packages have the qualified names the
    /// planner reads), positional redefinitions and a feature chain.
    const CARRIED_LIBRARY: &str = "library package Parts { part def Part; part parts : Part[*]; } library package L { part def A { part a : A[0..1]; part b : A; part c : b.a; } part def B :> A { part :>> a; } calc def F { in x; return y; } calc def G :> F { in z; return w; } }";

    /// A snapshot written after the library's plans were made carries them,
    /// and a process reading it takes them back as they were — without
    /// planning: the same implied plan, positional plan, bases, reached types
    /// and facts, and the same graph for a build on either handle. A snapshot
    /// written before carries none, and the plans are made on first request
    /// as before.
    #[test]
    fn a_snapshot_carries_the_plans_made_before_it_was_written() {
        let user = "package U { part b : L::B; calc g : L::G { in z = 1; } }";
        let mut base = Model::new();
        base.add_library_source("lib.sysml", CARRIED_LIBRARY);
        let fresh = base.prepare_library().unwrap();
        let before = Arc::new(PreparedLibrary::from_bytes(&fresh.to_bytes(3).unwrap(), 3).unwrap());
        assert!(!before.carries_plans(), "nothing was planned yet");
        let count = plannings();
        fresh.make_plans();
        assert_eq!(plannings() - count, 1, "the fresh library plans once");
        let plans = fresh.library_plans().expect("the library plans");
        let after = Arc::new(PreparedLibrary::from_bytes(&fresh.to_bytes(3).unwrap(), 3).unwrap());
        assert!(after.carries_plans());
        let count = plannings();
        let carried = after.library_plans().expect("the carried plans read back");
        assert_eq!(plannings(), count, "read back, not planned");
        assert!(!after.carries_plans(), "read back once");
        assert_eq!(plans_difference(&plans, &carried), None);
        let count = plannings();
        let made = before.library_plans().expect("made on request");
        assert_eq!(plannings() - count, 1, "a snapshot without plans plans");
        assert_eq!(plans_difference(&made, &carried), None);
        let graphs = |library: &Arc<PreparedLibrary>| {
            let mut model = Model::new();
            Arc::clone(library).install(&mut model).unwrap();
            model.add_source("user.sysml", user);
            let r = ResolvedModel::build(&model);
            assert!(r.b.prepared_from.is_some(), "a build on the library");
            (
                crate::json::model_to_compact_json(&model),
                crate::check::validate_semantics(&model).len(),
            )
        };
        assert_eq!(graphs(&after), graphs(&before));
    }

    /// The same plans are written the same way every time: the plans of one
    /// library prepared twice encode to the same bytes.
    #[test]
    fn the_plans_are_written_the_same_way_every_time() {
        let encoded = || {
            let mut base = Model::new();
            base.add_library_source("lib.sysml", CARRIED_LIBRARY);
            let prepared = base.prepare_library().unwrap();
            prepared.make_plans();
            let plans = prepared.library_plans().unwrap();
            assert!(
                !plans.implied.is_empty(),
                "the library has implied specializations to write"
            );
            crate::cache_codec::encode(&plans.to_wire().unwrap()).unwrap()
        };
        assert_eq!(encoded(), encoded());
    }

    /// Carried plans that do not fit the library — a row count, a row index
    /// or an edge the planner would not have written — are refused, and the
    /// library is planned instead: the plans are the planner's either way.
    #[test]
    fn carried_plans_that_do_not_fit_the_library_are_planned_instead() {
        let mut base = Model::new();
        base.add_library_source("lib.sysml", CARRIED_LIBRARY);
        let fresh = base.prepare_library().unwrap();
        fresh.make_plans();
        let plans = fresh.library_plans().expect("the library plans");
        let bytes = fresh.to_bytes(3).unwrap();
        assert!(
            !plans.implied.is_empty(),
            "the library has implied specializations to carry"
        );
        type Tamper = fn(&mut LibraryPlansWire);
        let tampered: [(&str, Tamper); 5] = [
            ("one row more", |wire| wire.rows += 1),
            ("an edge the planner does not spell", |wire| {
                wire.implied.candidates.spelled.0[0] = 4;
            }),
            ("a candidate owner past the rows", |wire| {
                wire.implied.candidates.owners.0[0] = wire.rows;
            }),
            ("a planning of a type past the rows", |wire| {
                wire.planned = PlannedTypes::from_wire(
                    std::mem::replace(&mut wire.planned, PlannedTypes::default().to_wire()),
                    usize::MAX,
                )
                .map(|mut planned| {
                    planned.keep_nothing_for(wire.rows);
                    planned.to_wire()
                })
                .unwrap();
            }),
            ("a plan in another configuration", |wire| {
                wire.implied.library_configuration = false;
            }),
        ];
        for (what, tamper) in tampered {
            let handle = Arc::new(PreparedLibrary::from_bytes(&bytes, 3).unwrap());
            let mut wire = plans.to_wire().expect("the plans have a wire form");
            tamper(&mut wire);
            assert!(
                LibraryPlans::from_wire(&handle, wire).is_none(),
                "{what}: refused"
            );
            let mut wire = plans.to_wire().expect("the plans have a wire form");
            tamper(&mut wire);
            handle.set_decoded_plans(Some(wire));
            let count = plannings();
            let planned = handle.library_plans().expect("planned instead");
            assert_eq!(plannings() - count, 1, "{what}: planned instead");
            assert_eq!(plans_difference(&plans, &planned), None, "{what}");
        }
        let handle = Arc::new(PreparedLibrary::from_bytes(&bytes, 3).unwrap());
        assert!(
            LibraryPlans::from_wire(&handle, plans.to_wire().unwrap()).is_some(),
            "the plans as written fit"
        );
    }

    /// The names table a from_wire handle's plans hold is the one in the
    /// cell every build on the library shares: the plans filled it, and a
    /// build asking for the library's names gets the same allocation.
    #[test]
    fn a_decoded_librarys_plans_names_table_is_the_cell_every_build_on_it_shares() {
        let Some(fresh) = standard_library() else {
            return;
        };
        fresh.make_plans();
        let decoded =
            Arc::new(PreparedLibrary::from_bytes(&fresh.to_bytes(7).unwrap(), 7).unwrap());
        let plans = decoded
            .library_plans()
            .expect("the carried plans read back");
        assert!(
            Arc::ptr_eq(&plans.names, &decoded.builder.implied_names()),
            "the plans' names and the shared cell are one table"
        );
    }

    /// The library's own table of its relationships' owners, which the
    /// implied planners now read for a build on the library, gives every
    /// authored row the owner the planners' own scan of the frozen rows
    /// gave: the row whose owned relationships list it, `None` for a row
    /// none lists.
    #[test]
    fn the_librarys_owner_table_gives_each_authored_row_the_owner_the_planners_scan_gave() {
        let Some(library) = standard_library() else {
            return;
        };
        let b = &library.builder;
        // The scan the planners' shared cell made, over every frozen row.
        let mut scanned = vec![None; b.elements.len()];
        for (owner, element) in b.elements.iter().enumerate() {
            for &relationship in &element.owned_relationships {
                scanned[relationship] = Some(owner);
            }
        }
        let table = library.library_rel_owners();
        let differing: Vec<usize> = (0..b.elements.len())
            .filter(|&r| b.is_authored(r) && table[r] != scanned[r])
            .collect();
        assert!(
            differing.is_empty() && table.len() == scanned.len(),
            "{} of {} authored rows owned otherwise: {:?}",
            differing.len(),
            b.lib_implied_from,
            &differing[..differing.len().min(8)]
        );
    }

    /// What each member of the standard library's plans holds, read back
    /// from a snapshot as a host reads them, and what the library's build
    /// behind them holds, member by member; then what the library's tables
    /// made on first read hold. Printed, not asserted: run with
    /// `cargo test -p sysmlv2-model --lib plans_members -- --ignored --nocapture --test-threads=1`.
    #[test]
    #[ignore = "prints a measurement of the standard library"]
    fn the_standard_librarys_plans_members_bytes() {
        use crate::memtest::{held, kept};
        let Some(fresh) = standard_library() else {
            return;
        };
        fresh.make_plans();
        let wire = fresh.library_plans().unwrap().to_wire().unwrap();
        let bytes = fresh.to_bytes(7).unwrap();
        drop(fresh);
        {
            let planned = kept("library decode (plans to be made)", || {
                Arc::new(PreparedLibrary::from_bytes(&bytes, 7).unwrap())
            });
            planned.set_decoded_plans(None);
            let plans = kept("plans made by planning", || {
                LibraryPlans::plan(&planned).unwrap()
            });
            let mut b = plans.build.into_inner().unwrap();
            held("planning build: stored_structure", || {
                b.stored_structure = None
            });
            held("planning build: prefix_structure", || {
                b.prefix_structure = None
            });
            held("planning build: id_index", || b.id_index = None);
            held("planning build: the rest", || drop(b));
        }
        let decoded = kept("library decode", || {
            Arc::new(PreparedLibrary::from_bytes(&bytes, 7).unwrap())
        });
        drop(bytes);
        let plans = kept("plans from wire", || {
            LibraryPlans::from_wire(&decoded, wire).unwrap()
        });
        println!(
            "  rows {}, spec rows {}, build rows {}, names {}",
            plans.rows,
            plans.spec_rows,
            plans.build.lock().unwrap().elements.len(),
            plans.names.len()
        );
        // The inherited memberships a build's checks ask the plans' build
        // for, one library scope's and then every library type's: what
        // that build then holds is what the plans hold after a check.
        let scopes: Vec<usize> = {
            let b = plans.build.lock().unwrap();
            (0..b.elements.len())
                .filter(|&e| is_a!(b.elements[e], "Type"))
                .filter_map(|e| b.elem_scope.get(&e).copied())
                .collect()
        };
        kept("inherited bindings of one library scope", || {
            plans
                .inherited_bindings(scopes[scopes.len() / 2], true)
                .is_some()
        });
        kept("inherited bindings of every library type", || {
            scopes
                .iter()
                .filter(|&&s| plans.inherited_bindings(s, true).is_some())
                .count()
        });
        println!("  {} library type scopes", scopes.len());
        let LibraryPlans {
            rows: _,
            names,
            implied,
            chained: _,
            bases,
            bases_table,
            bases_incomplete,
            positional,
            reached,
            planned,
            spec_rows: _,
            facts: _,
            build,
        } = plans;
        let mut b = build.into_inner().unwrap();
        held("build: stored_structure", || b.stored_structure = None);
        held("build: prefix_structure", || b.prefix_structure = None);
        held("build: id_index", || b.id_index = None);
        held("build: prefix_ids", || b.prefix_ids = None);
        held("build: recorded_lookup_prefix", || {
            b.recorded_lookup_prefix = None
        });
        held("build: supported_implied (shared)", || {
            b.supported_implied = None
        });
        held("build: positional_redefinitions", || {
            b.positional_redefinitions = None
        });
        held("build: library_plans_decided", || {
            b.library_plans_decided = None
        });
        println!(
            "  inherited memos {}, by heritage {}, base contributions {}, heritage reductions {}, import targets {}",
            b.inherited_cache.len(),
            b.inherited_by_heritage.len(),
            b.base_contributions.len(),
            b.heritage_reductions.len(),
            b.import_targets.len()
        );
        held("build: inherited memos", || b.drop_inherited_memos());
        held("build: inherited by heritage", || {
            b.inherited_by_heritage = Default::default()
        });
        held("build: base contributions", || {
            b.base_contributions = Default::default()
        });
        held("build: heritage reductions", || {
            b.heritage_reductions = Default::default()
        });
        held("build: import targets", || {
            b.import_targets = Default::default()
        });
        held("build: spec_index", || b.spec_index = None);
        held("build: spec_memo", || b.spec_memo = None);
        held("build: mult_index", || b.mult_index = None);
        held("build: redefinition closures", || {
            b.redefinition_closures = None
        });
        held("build: name keys", || b.name_keys = None);
        held("build: lookup misses", || {
            b.spec_misses = Default::default();
            b.ref_misses = Default::default();
        });
        held("build: the rest", || drop(b));
        let mut note = |label: &str| println!("  implied: {label} dropped");
        let implied = Arc::try_unwrap(implied).ok().expect("held once now");
        held("implied (all members, see below)", || {
            implied.drop_members(&mut |label| {
                println!(
                    "    after {label}: live {:.3} MB",
                    crate::memtest::live() as f64 / 1e6
                )
            })
        });
        let _ = &mut note;
        held("planned (all tables, see below)", || {
            planned.drop_members(&mut |label| {
                println!(
                    "    after {label}: live {:.3} MB",
                    crate::memtest::live() as f64 / 1e6
                )
            })
        });
        println!(
            "  bases: {} rows, {} with a list, {} values; incomplete {}; reached {}",
            bases.rows(),
            bases.iter().count(),
            bases.values().len(),
            bases_incomplete.len(),
            reached.len()
        );
        held("bases", || drop(bases));
        held("bases_table", || drop(bases_table));
        held("bases_incomplete", || drop(bases_incomplete));
        println!(
            "  positional: {} targets keys / {} values, {} incomplete",
            positional.targets.len(),
            positional.targets.values().map(Vec::len).sum::<usize>(),
            positional.incomplete.len()
        );
        held("positional", || drop(positional));
        held("reached", || drop(reached));
        held("names", || drop(names));
        kept("rel_owners", || decoded.library_rel_owners().len());
        kept("spec_index", || decoded.library_spec_index().len());
        kept("expression_bounds", || {
            let _ = decoded.library_expression_bounds();
        });
        kept("multiplicity_ranges", || {
            decoded.library_multiplicity_ranges().len()
        });
        kept("declared_multiplicities", || {
            decoded.library_declared_multiplicities().len()
        });
        kept("chain_redefinitions", || {
            decoded.library_chain_redefinitions().len()
        });
        kept("enum_types", || decoded.library_enum_types().entries.len());
        kept("implied names cell", || {
            decoded.builder.implied_names().len()
        });
        let model = on(&decoded, &[("vehicle.sysml", VEHICLE)]);
        kept("first build + check on the handle", || {
            crate::check::validate_semantics(&model).len()
        });
        let model = on(&decoded, &[("vehicle.sysml", VEHICLE)]);
        kept("second build + check", || {
            crate::check::validate_semantics(&model).len()
        });
        // The implied relationships of a build on the library materialized,
        // twice: the first also makes what every build over the library's
        // plans shares.
        let mut first = ResolvedModel::build(&model);
        let mut second = ResolvedModel::build(&model);
        kept("first materialization on the handle", || {
            first.ensure_implied()
        });
        kept("second materialization on the handle", || {
            second.ensure_implied()
        });
    }
}
