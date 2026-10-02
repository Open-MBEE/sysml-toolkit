//! Detached static and dynamic specialization recipes.
use super::positional::PositionalRedefinitions;
use std::{collections::HashMap, sync::Arc};
use uuid::Uuid;

/// Exact materialization recipe, including the surviving legacy UUID. A recipe
/// is not just a (source,target) pair: metaclass, typed aliases and ordering are
/// observable. Static recipes come from the shared emitter, or are checked
/// against its existing physical rows before this snapshot is admitted.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct Edge {
    pub owner: usize,
    pub owner_id: Uuid,
    pub id: Uuid,
    pub kind: &'static str,
    pub source_key: &'static str,
    pub target_key: &'static str,
    pub target: Uuid,
}

/// One exact immutable prefix. Recreating this Arc after any provenance or
/// configuration change intentionally makes pending admission stale, even if
/// the new recipes happen to compare equal. Never reconstruct a prefix from
/// current predictions alone when old physical rows already exist. The shared
/// capture gate compares actual fields/order/carriers and preserves physical IDs.
#[derive(Clone)]
pub(super) struct StaticPrefix {
    pub authored_end: usize,
    pub rows: Vec<Edge>,
    pub positional: Arc<PositionalRedefinitions>,
    pub chain_bases: Arc<super::type_relations::FeatureChainBases>,
    pub planner_bases: HashMap<usize, Vec<usize>>,
    pub planner_incomplete: std::collections::HashSet<usize>,
    pub specializations: HashMap<Uuid, Vec<Uuid>>,
}

/// The immutable accepted batch. All vectors/maps are fully constructed before
/// publication. Direct bases and positional targets include static and dynamic
/// contributions; tail contains only additions, in final materialization order.
/// Result/Binding rows are reserved with these edges by the common tail builder
/// before this value may publish; they are deliberately not constructed here.
#[derive(Clone)]
pub(super) struct Plan {
    pub static_prefix: Arc<StaticPrefix>,
    pub direct_bases: HashMap<usize, Vec<usize>>,
    pub added_bases: HashMap<usize, Vec<usize>>,
    pub affected_owners: std::collections::HashSet<usize>,
    pub incomplete_bases: std::collections::HashSet<usize>,
    pub specializations: HashMap<Uuid, Vec<Uuid>>,
    pub positional: PositionalRedefinitions,
    pub tail: Vec<Edge>,
}
