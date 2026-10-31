//! Recorded-only inherited name selection for complete explicit heritage.
//! Complex import, filter, chain and implied-heritage contexts retain the
//! contextual resolver until those dependencies share a complete recorded plan.

use super::{Builder, LookupAccess, LookupResult, MissTable};
use crate::bulk::{Bytes, Flags, IndexLists, Ints};
use crate::layered::{IdMap, LayeredMap, LayeredVec};
use crate::metaclass::is_a;
use std::collections::{HashMap, HashSet};
use std::sync::Arc;

#[derive(Clone, PartialEq, Debug)]
struct Member {
    target: usize,
    scope: Option<usize>,
    names: Vec<String>,
    visibility: LookupAccess,
    alias: bool,
}

#[derive(Clone, PartialEq, Debug)]
struct Node {
    bases: Vec<usize>,
    owned: Vec<usize>,
    owned_features: Vec<usize>,
}

#[derive(Clone, Default)]
pub(super) struct Graph {
    nodes: LayeredVec<Option<Node>>,
    members: LayeredMap<usize, Member>,
    header_bases: LayeredMap<usize, Vec<usize>>,
    has_ordered_headers: bool,
    features: LayeredMap<usize, ()>,
    redefinitions: LayeredMap<usize, Option<Vec<usize>>>,
    inherited: LayeredMap<usize, Option<Arc<Vec<usize>>>>,
    suppressed: LayeredMap<usize, Arc<Vec<usize>>>,
    ids: LayeredMap<uuid::Uuid, usize>,
    element_count: usize,
    absent_roots: HashSet<String>,
    /// Root misses behind each scope's node inputs — the recorded outcomes
    /// of its owner's specializations and alias memberships, whether or not
    /// a node resulted — and the implied roots the node takes as absent.
    /// A selection through the graph depends on every node it read.
    input_misses: MissTable,
    /// Root misses behind each feature's recorded redefinition targets.
    redefinition_misses: MissTable,
    /// Root misses behind each scope's header bases.
    header_misses: MissTable,
    /// Root misses behind each memoized inherited projection (`inherited`),
    /// complete or not.
    collected_misses: MissTable,
}

/// A frozen graph as a snapshot carries it: every table as columns over
/// the element and scope indices of the rows the graph was built on, each
/// map as its rows sorted by key, so the same graph is written the same way
/// every time. The id map is left out — the rows carry their ids already —
/// and made from them when the graph is read (see [`Graph::from_wire`]).
#[derive(Clone, PartialEq, Debug, serde::Serialize, serde::Deserialize)]
pub(crate) struct GraphWire {
    elements: usize,
    scopes: usize,
    has_ordered_headers: bool,
    /// The scopes with a node, each with its bases (scopes), its owned
    /// Memberships and its owned Features (rows): three lists under one
    /// sequence of scopes.
    node_bases: IndexLists,
    node_owned: IndexLists,
    node_features: IndexLists,
    /// The Memberships the nodes own: each one's row, its member's row, the
    /// member's scope (the scope count for none), its visibility, whether
    /// it is an alias, and how many of `member_names` are its names.
    member_rows: Ints,
    member_targets: Ints,
    member_scopes: Ints,
    member_visibility: Bytes,
    member_aliases: Flags,
    member_name_counts: Ints,
    member_names: Vec<String>,
    /// The header bases by scope.
    header_bases: IndexLists,
    /// The rows that are Features.
    features: Ints,
    /// The recorded redefinition targets by redefining Feature, and the
    /// Features whose targets are left to the resolver.
    redefinitions: IndexLists,
    redefinitions_open: Ints,
    /// The memoized inherited projections by scope and the scopes whose
    /// projection is memoized as unavailable; the suppressed Memberships by
    /// scope.
    inherited: IndexLists,
    inherited_open: Ints,
    suppressed: IndexLists,
    /// The implied root names the nodes take as absent, sorted.
    absent_roots: Vec<String>,
}

#[cfg(test)]
impl GraphWire {
    /// The names of the tables in which `other` differs from this wire.
    pub(crate) fn differences(&self, other: &Self) -> Vec<&'static str> {
        let mut names = Vec::new();
        macro_rules! compare {
            ($($field:ident),*) => {
                $(if self.$field != other.$field {
                    names.push(stringify!($field));
                })*
            };
        }
        compare!(
            elements,
            scopes,
            has_ordered_headers,
            node_bases,
            node_owned,
            node_features,
            member_rows,
            member_targets,
            member_scopes,
            member_visibility,
            member_aliases,
            member_name_counts,
            member_names,
            header_bases,
            features,
            redefinitions,
            redefinitions_open,
            inherited,
            inherited_open,
            suppressed,
            absent_roots
        );
        names
    }
}

/// Note the misses behind the graph entry `key` of `table` among `misses`.
fn note(misses: &mut Vec<String>, table: &MissTable, key: usize) {
    if let Some(entry) = table.get(key) {
        super::note_misses(misses, entry.iter());
    }
}

/// Keep `misses` as the misses behind the graph entry `key` of `table`.
fn keep(table: &mut MissTable, key: usize, misses: Vec<String>) {
    table.set(key, &misses);
}

/// A short-lived proof that an alias spelling can be followed without import
/// walks. It uses stored explicit bases and declaration tables, never the
/// contextual resolver or its semantic caches.
struct AliasProof<'a> {
    b: &'a Builder,
    graph: &'a mut Graph,
    active: HashSet<usize>,
    bindings: HashMap<(usize, String, u8), Option<Option<usize>>>,
    /// Root misses behind everything the proofs read: the nodes their
    /// selections went through, the implied roots they took as absent, and
    /// the names they looked up and did not find at the root.
    misses: Vec<String>,
}

impl AliasProof<'_> {
    fn target(&mut self, origin: usize, qn: &super::QualifiedName, depth: usize) -> Option<usize> {
        if depth > super::MAX_RESOLUTION_DEPTH {
            return None;
        }
        let first = qn.segments.first()?;
        let mut scope = if qn.is_global { 0 } else { origin };
        let mut target = loop {
            match self.binding(scope, &first.value, LookupAccess::All, depth)? {
                Some(target) => break target,
                None if scope == 0 => {
                    super::note_misses(&mut self.misses, [&first.value]);
                    return None;
                }
                None => scope = self.b.scopes[scope].parent?,
            }
        };
        for (step, segment) in qn.segments.iter().enumerate().skip(1) {
            let scope = *self.b.elem_scope.get(&target)?;
            let access = if self.b.scope_is_within(origin, scope) {
                LookupAccess::All
            } else if self.can_access_protected(origin, scope) {
                LookupAccess::Protected
            } else {
                LookupAccess::Public
            };
            target = self.binding(scope, &segment.value, access, depth + step)??;
        }
        Some(target)
    }

    // Some(None) proves the spelling absent here, permitting a lexical
    // parent step. None means contextual resolution may contribute a binding.
    fn binding(
        &mut self,
        scope: usize,
        name: &str,
        access: LookupAccess,
        depth: usize,
    ) -> Option<Option<usize>> {
        if depth > super::MAX_RESOLUTION_DEPTH {
            return None;
        }
        let key = (scope, name.to_owned(), access as u8);
        if let Some(result) = self.bindings.get(&key) {
            return *result;
        }
        // An active cycle is not an import-free resolution proof.
        self.bindings.insert(key.clone(), None);
        let result = self.binding_uncached(scope, name, access, depth);
        self.bindings.insert(key, result);
        result
    }

    fn binding_uncached(
        &mut self,
        scope: usize,
        name: &str,
        access: LookupAccess,
        depth: usize,
    ) -> Option<Option<usize>> {
        let context = &self.b.scopes[scope];
        for names in [&context.names, &context.effective_names] {
            let mut bindings = names
                .get(name)
                .into_iter()
                .flatten()
                .filter(|binding| access.admits(binding.visibility));
            if let Some(binding) = bindings.next() {
                if bindings.any(|other| other.elem != binding.elem) {
                    return None;
                }
                return Some(Some(binding.elem));
            }
        }
        let mut aliases = context
            .aliases
            .iter()
            .filter(|(n, _, rel)| n == name && self.b.import_admitted(*rel, access));
        if let Some((_, qn, rel)) = aliases.next() {
            if aliases.any(|(_, _, other)| other != rel) || !self.active.insert(*rel) {
                return None;
            }
            let target = self.target(scope, qn, depth + 1);
            self.active.remove(rel);
            return target.map(Some);
        }
        if context.implied_ends.iter().any(|(n, _, _)| *n == name)
            || !context.imports.is_empty()
            || !context.member_imports.is_empty()
            || !context.filters.is_empty()
            || !context.chain_bases.is_empty()
            || context.owner.is_some_and(|owner| {
                self.b
                    .metadata_of
                    .get(&owner)
                    .is_some_and(|m| !m.is_empty())
            })
            || !Graph::implied_roots_absent(self.b, scope)
        {
            return None;
        }
        let absent = Graph::implied_roots(context);
        super::note_misses(&mut self.misses, &absent);
        self.graph.absent_roots.extend(absent);
        if context.bases.is_empty() {
            return Some(None);
        }
        let (hits, _) = self
            .graph
            .select(scope, name, access, None, false, &mut self.misses)?;
        let mut result = LookupResult::Missing;
        for hit in hits {
            if let LookupResult::Found(target, _, Some(alias)) = hit {
                let owner = self.b.elements[alias]
                    .props
                    .get("owningRelatedElement")?
                    .as_reference()
                    .and_then(|id| self.graph.ids.get(&id).copied())?;
                let origin = *self.b.elem_scope.get(&owner)?;
                let (_, qn, _) = self.b.scopes[origin]
                    .aliases
                    .iter()
                    .find(|(_, _, rel)| *rel == alias)?;
                if !self.active.insert(alias) {
                    return None;
                }
                let certified = self.target(origin, qn, depth + 1);
                self.active.remove(&alias);
                if certified != Some(target) {
                    return None;
                }
            }
            result = self.b.merge_lookup(result, hit);
        }
        match result {
            LookupResult::Found(target, _, _) => Some(Some(target)),
            LookupResult::Missing => Some(None),
            LookupResult::Ambiguous => None,
        }
    }

    fn can_access_protected(&mut self, mut origin: usize, target: usize) -> bool {
        let mut seen = HashSet::new();
        loop {
            let mut pending = vec![origin];
            while let Some(scope) = pending.pop() {
                if !seen.insert(scope) {
                    continue;
                }
                note(&mut self.misses, &self.graph.input_misses, scope);
                if let Some(node) = self.graph.nodes.get(scope).and_then(Option::as_ref) {
                    if node.bases.contains(&target) {
                        return true;
                    }
                    pending.extend(node.bases.iter().copied());
                }
            }
            let Some(parent) = self.b.scopes[origin].parent else {
                return false;
            };
            origin = parent;
        }
    }
}

impl Graph {
    /// A single-base chain with no redeclarations, aliases or redefinitions
    /// cannot change when selection moves before name matching.
    pub(super) fn needed(b: &Builder) -> bool {
        let has_redefinition = b.elements.iter().any(|e| is_a!(e, "Redefinition"));
        let candidate = b.scopes.iter().any(|s| {
            !s.aliases.is_empty()
                || s.written_base_count() > 1
                || (s.written_base_count() > 0
                    && s.owner.is_some_and(|owner| {
                        b.elements[owner]
                            .owned_relationships
                            .iter()
                            .any(|&r| is_a!(b.elements[r], "Membership"))
                    }))
        });
        has_redefinition
            || (candidate && (0..b.scopes.len()).any(|s| Self::scope_inputs(b, s).is_some()))
    }

    fn scope_inputs(b: &Builder, s: usize) -> Option<(usize, Vec<usize>)> {
        let scope = &b.scopes[s];
        let owner = scope.owner?;
        if !b.dynamic_evidence_current(owner) || !b.result_redefinition_evidence_current(owner) {
            return None;
        }
        if b.effective_dynamic_plan().is_some_and(|plan| {
            plan.added_bases
                .get(&owner)
                .is_some_and(|bases| !bases.is_empty())
        }) {
            return None;
        }
        if !is_a!(b.elements[owner], "Type")
            || is_a!(b.elements[owner], "Definition")
            || is_a!(b.elements[owner], "Usage")
            || !scope.imports.is_empty()
            || !scope.member_imports.is_empty()
            || !scope.filters.is_empty()
            || !scope.chain_bases.is_empty()
            || !scope.implied_ends.is_empty()
            || b.metadata_of.get(&owner).is_some_and(|m| !m.is_empty())
        {
            return None;
        }
        // Only a provably absent global implied root can be ignored.
        // No lexical resolution is allowed while building this snapshot.
        if !Self::implied_roots_absent(b, s) {
            return None;
        }
        let owned_features = b.owned_member_elems(owner, true);
        // End, parameter and result slots can acquire positional edges
        // without any loaded library. Their closures need the completed
        // positional plan and stay outside this explicit-only snapshot.
        if owned_features.iter().any(|&feature| {
            b.elements[feature]
                .props
                .get("isEnd")
                .and_then(|v| v.as_bool())
                == Some(true)
                || b.elements[feature].owning_relationship.is_some_and(|r| {
                    is_a!(b.elements[r], "ParameterMembership")
                        || is_a!(b.elements[r], "ReturnParameterMembership")
                })
        }) {
            return None;
        }
        Some((owner, owned_features))
    }

    /// The global roots of a scope's implied bases: taking them as absent
    /// depends on each staying a root miss, and on the root importing
    /// nothing ([`super::ROOT_IMPORTS`]).
    fn implied_roots(scope: &super::Scope) -> Vec<String> {
        let mut roots: Vec<String> = scope
            .implied_bases
            .iter()
            .filter_map(|qn| qn.segments.first().map(|n| n.value.clone()))
            .collect();
        if !roots.is_empty() {
            roots.push(super::ROOT_IMPORTS.to_owned());
        }
        roots
    }

    /// Whether any node or alias proof takes implied roots as absent.
    pub(super) fn takes_implied_roots_absent(&self) -> bool {
        !self.absent_roots.is_empty()
    }

    fn implied_roots_absent(b: &Builder, scope: usize) -> bool {
        b.scopes[scope].implied_bases.iter().all(|qn| {
            qn.is_global
                && qn.segments.first().is_some_and(|first| {
                    let root = &b.scopes[0];
                    root.names.get(&first.value).is_none()
                        && root.effective_names.get(&first.value).is_none()
                        && !root.aliases.iter().any(|(name, _, _)| name == &first.value)
                        && root.imports.is_empty()
                        && root.member_imports.is_empty()
                })
                && (b.external_implied_names.is_empty()
                    || !b.external_implied_names.contains_key(
                        &qn.segments
                            .iter()
                            .map(|s| s.value.as_str())
                            .collect::<Vec<_>>()
                            .join("::"),
                    ))
        })
    }

    pub(super) fn build(b: &Builder) -> Self {
        let prefix = b
            .recorded_lookup_prefix
            .as_ref()
            .filter(|g| g.compatible_prefix(b));
        let start_element = prefix.map_or(0, |g| g.element_count);
        let start_scope = prefix.map_or(0, |g| g.nodes.len());
        let mut ids = prefix.map_or_else(LayeredMap::default, |g| g.ids.clone());
        for (e, element) in b.elements.iter().enumerate().skip(start_element) {
            ids.insert(element.id, e);
        }
        let target = |r: usize, key: &str| {
            b.elements[r]
                .props
                .get(key)
                .and_then(|v| v.as_reference())
                .and_then(|id| ids.get(&id).copied())
        };
        let mut graph = prefix.map_or_else(Self::default, |g| g.as_ref().clone());
        // Only a build that records its library outcomes reads the misses.
        let attribute = b.lib_record.is_some();
        graph.nodes.resize(b.scopes.len(), None);
        graph.element_count = b.elements.len();
        for (e, element) in b.elements.iter().enumerate().skip(start_element) {
            if is_a!(element, "Feature") {
                graph.features.insert(e, ());
            }
            let positional_source = is_a!(element, "Usage")
                || element.props.get("isEnd").and_then(|v| v.as_bool()) == Some(true)
                || element.owning_relationship.is_some_and(|r| {
                    is_a!(b.elements[r], "ParameterMembership")
                        || is_a!(b.elements[r], "ReturnParameterMembership")
                });
            let positional_source = positional_source
                || element
                    .props
                    .get("direction")
                    .and_then(|v| v.as_str())
                    .is_some();
            let mut targets = if positional_source {
                None
            } else {
                Some(Vec::new())
            };
            let mut misses = Vec::new();
            for &r in &element.owned_relationships {
                if is_a!(b.elements[r], "Redefinition") {
                    note(&mut misses, &b.ref_misses, r);
                    match (targets.as_mut(), target(r, "redefinedFeature")) {
                        (Some(targets), Some(t)) => targets.push(t),
                        _ => targets = None,
                    }
                }
            }
            if targets.as_ref().is_none_or(|v| !v.is_empty()) {
                graph.redefinitions.insert(e, targets);
                keep(&mut graph.redefinition_misses, e, misses);
            }
        }
        // Header starting contexts are independent of whether Membership
        // selection is fully recorded. Each context may still need ordinary
        // imports, implied heritage or positional lookup. Freeze their stored
        // explicit endpoints with the rest of this pass's snapshot.
        for (s, scope) in b.scopes.iter().enumerate().skip(start_scope) {
            if let Some(owner) = scope.owner.filter(|&e| is_a!(b.elements[e], "Type")) {
                let mut misses = Vec::new();
                for &r in &b.elements[owner].owned_relationships {
                    if is_a!(b.elements[r], "Specialization") {
                        note(&mut misses, &b.ref_misses, r);
                    }
                }
                let bases: Option<Vec<_>> = b.elements[owner]
                    .owned_relationships
                    .iter()
                    .copied()
                    .filter(|&r| is_a!(b.elements[r], "Specialization"))
                    .map(|r| {
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
                        .find_map(|key| target(r, key))
                        .and_then(|e| b.elem_scope.get(&e).copied())
                    })
                    .collect();
                keep(&mut graph.header_misses, s, misses);
                if let Some(bases) = bases {
                    if scope.chain_bases.is_empty() && bases.len() == scope.written_base_count() {
                        graph.header_bases.insert(s, bases);
                    }
                }
            }
            let Some((owner, owned_features)) = Self::scope_inputs(b, s) else {
                continue;
            };
            let implied = Self::implied_roots(scope);
            if attribute {
                let mut inputs = implied.clone();
                for &r in &b.elements[owner].owned_relationships {
                    let relation = &b.elements[r];
                    if is_a!(relation, "Specialization")
                        || (is_a!(relation, "Membership") && !is_a!(relation, "OwningMembership"))
                    {
                        note(&mut inputs, &b.ref_misses, r);
                    }
                }
                keep(&mut graph.input_misses, s, inputs);
            }
            graph.absent_roots.extend(implied);
            let mut node = Node {
                bases: Vec::new(),
                owned: Vec::new(),
                owned_features,
            };
            let mut complete = true;
            let mut written_bases = 0;
            for &r in &b.elements[owner].owned_relationships {
                let relation = &b.elements[r];
                if is_a!(relation, "Specialization") {
                    written_bases += 1;
                    let general = [
                        "general",
                        "superclassifier",
                        "type",
                        "subsettedFeature",
                        "redefinedFeature",
                        "referencedFeature",
                        "crossedFeature",
                    ]
                    .iter()
                    .find_map(|key| target(r, key));
                    if let Some(t) = general {
                        if let Some(&base) = b.elem_scope.get(&t) {
                            node.bases.push(base);
                        } else {
                            complete = false;
                        }
                    } else {
                        complete = false;
                    }
                }
                if !is_a!(relation, "Membership") {
                    continue;
                }
                let visibility = match relation.props.get("visibility").and_then(|v| v.as_str()) {
                    Some("private") => continue,
                    Some("protected") => LookupAccess::Protected,
                    _ => LookupAccess::Public,
                };
                let member = if is_a!(relation, "OwningMembership") {
                    relation.children.first().copied()
                } else {
                    target(r, "memberElement")
                };
                let Some(member) = member else {
                    complete = false;
                    continue;
                };
                let alias = !is_a!(relation, "OwningMembership");
                let names: Vec<String> = if alias {
                    ["memberName", "memberShortName"]
                        .iter()
                        .filter_map(|key| relation.props.get(key).and_then(|v| v.as_str()))
                        .map(str::to_owned)
                        .collect()
                } else {
                    let (name, short) = b.elements[member].props.declared_names();
                    [name, short]
                        .into_iter()
                        .flatten()
                        .map(str::to_owned)
                        .collect()
                };
                // Unnamed Features can acquire effective names through several
                // specialization rules. Leave those contexts to the resolver.
                if names.is_empty() && graph.features.contains_key(&member) {
                    complete = false;
                }
                graph.members.insert(
                    r,
                    Member {
                        target: member,
                        scope: b.elem_scope.get(&member).copied(),
                        names,
                        visibility,
                        alias,
                    },
                );
                node.owned.push(r);
            }
            if complete && written_bases == scope.written_base_count() {
                graph.nodes[s] = Some(node);
            }
        }
        graph.ids = ids;
        // Alias proofs read the same filtered inherited Membership projection
        // as lookup. Invalidating a provider can invalidate another proof, so
        // repeat monotonically; each non-final round removes at least one node.
        // Whether a node survives depends on what its proof read; the proofs
        // share their binding memo, so each proven node takes all of it.
        let mut proof_misses = Vec::new();
        let mut proven = Vec::new();
        loop {
            let mut invalid = Vec::new();
            {
                let mut proof = AliasProof {
                    b,
                    graph: &mut graph,
                    active: HashSet::new(),
                    bindings: HashMap::new(),
                    misses: Vec::new(),
                };
                for (s, scope) in b.scopes.iter().enumerate().skip(start_scope) {
                    if proof.graph.nodes[s].is_none() {
                        continue;
                    }
                    for (_, qn, alias) in &scope.aliases {
                        if !b.import_admitted(*alias, LookupAccess::Protected) {
                            continue;
                        }
                        let Some(member) = proof.graph.members.get(alias).map(|m| m.target) else {
                            continue;
                        };
                        proven.push(s);
                        proof.active.insert(*alias);
                        let certified = proof.target(s, qn, 0);
                        proof.active.remove(alias);
                        if certified != Some(member) {
                            invalid.push(s);
                            break;
                        }
                    }
                }
                super::note_misses(&mut proof_misses, &proof.misses);
            }
            if invalid.is_empty() {
                break;
            }
            for scope in invalid {
                graph.nodes[scope] = None;
            }
            // The immutable library prefix was certified before freezing;
            // only the newly appended projections depend on these nodes.
            graph.inherited = prefix.map_or_else(LayeredMap::default, |g| g.inherited.clone());
            graph.suppressed = prefix.map_or_else(LayeredMap::default, |g| g.suppressed.clone());
            graph.collected_misses.clear();
        }
        if attribute && !proof_misses.is_empty() {
            proven.sort_unstable();
            proven.dedup();
            for s in proven {
                let mut inputs = graph
                    .input_misses
                    .get(s)
                    .map_or_else(Vec::new, |m| m.to_vec());
                super::note_misses(&mut inputs, &proof_misses);
                keep(&mut graph.input_misses, s, inputs);
            }
            // Projections the proofs memoized read these inputs before.
            graph.inherited = prefix.map_or_else(LayeredMap::default, |g| g.inherited.clone());
            graph.suppressed = prefix.map_or_else(LayeredMap::default, |g| g.suppressed.clone());
            graph.collected_misses.clear();
        }
        // A redefinition resolves from the header bases of the Type owning
        // its redefining feature once the graph is ready, which a lexical
        // bootstrap cannot anticipate: such a header needs the later passes.
        graph.has_ordered_headers |=
            b.elements
                .iter()
                .enumerate()
                .skip(start_element)
                .any(|(feature, element)| {
                    element
                        .owned_relationships
                        .iter()
                        .any(|&r| is_a!(b.elements[r], "Redefinition"))
                        && b.owner_elem(feature)
                            .and_then(|owner| b.elem_scope.get(&owner))
                            .is_some_and(|&scope| {
                                graph.header_bases.get(&scope).is_some_and(|bases| {
                                    !bases.is_empty() || graph.nodes[scope].is_some()
                                })
                            })
                });
        graph
    }

    fn compatible_prefix(&self, b: &Builder) -> bool {
        self.element_count == b.lib_boundary
            && self.element_count <= b.elements.len()
            && self.nodes.len() <= b.scopes.len()
            && b.external_implied_names.is_empty()
            && b.scopes[0].imports.is_empty()
            && b.scopes[0].member_imports.is_empty()
            && b.scopes[0].filters.is_empty()
            && self.absent_roots.iter().all(|name| {
                let root = &b.scopes[0];
                root.names.get(name).is_none()
                    && root.effective_names.get(name).is_none()
                    && !root.aliases.iter().any(|(n, _, _)| n == name)
            })
    }

    /// After a pass that changed no outcome, the graph the pass read is the
    /// one a build from these outcomes would make, apart from what the pass
    /// memoized and collected while reading it: reset those as a build does.
    pub(super) fn settle(&mut self, b: &Builder) {
        let prefix = b
            .recorded_lookup_prefix
            .as_ref()
            .filter(|g| g.compatible_prefix(b));
        self.inherited = prefix.map_or_else(LayeredMap::default, |g| g.inherited.clone());
        self.suppressed = prefix.map_or_else(LayeredMap::default, |g| g.suppressed.clone());
        self.collected_misses.clear();
        note_settled();
    }

    /// The graph as a snapshot carries it (see [`GraphWire`]).
    pub(super) fn to_wire(&self) -> GraphWire {
        let scopes = self.nodes.len();
        fn sorted<V>(map: &LayeredMap<usize, V>) -> Vec<(usize, &V)> {
            let mut rows: Vec<(usize, &V)> = map.iter().map(|(&k, v)| (k, v)).collect();
            rows.sort_unstable_by_key(|&(k, _)| k);
            rows
        }
        // a table of lists as the lists it has and the keys of the rows
        // without one
        fn split<V>(
            rows: Vec<(usize, &V)>,
            list: impl Fn(&V) -> Option<&[usize]>,
        ) -> (IndexLists, Ints) {
            let mut lists = Vec::new();
            let mut open = Vec::new();
            for (k, v) in rows {
                match list(v) {
                    Some(values) => lists.push((k, values.to_vec())),
                    None => open.push(k),
                }
            }
            (lists.into(), Ints(open))
        }
        let nodes: Vec<(usize, &Node)> = (0..scopes)
            .filter_map(|s| self.nodes[s].as_ref().map(|node| (s, node)))
            .collect();
        let node_lists = |list: fn(&Node) -> &[usize]| -> IndexLists {
            nodes
                .iter()
                .map(|&(s, node)| (s, list(node).to_vec()))
                .collect::<Vec<_>>()
                .into()
        };
        let members = sorted(&self.members);
        let (redefinitions, redefinitions_open) =
            split(sorted(&self.redefinitions), |targets| targets.as_deref());
        let (inherited, inherited_open) = split(sorted(&self.inherited), |rows| {
            rows.as_deref().map(|rows| rows.as_slice())
        });
        let (suppressed, _) = split(sorted(&self.suppressed), |rows| Some(rows.as_slice()));
        let (header_bases, _) = split(sorted(&self.header_bases), |bases| Some(bases.as_slice()));
        let mut features: Vec<usize> = self.features.keys().copied().collect();
        features.sort_unstable();
        let mut absent_roots: Vec<String> = self.absent_roots.iter().cloned().collect();
        absent_roots.sort_unstable();
        GraphWire {
            elements: self.element_count,
            scopes,
            has_ordered_headers: self.has_ordered_headers,
            node_bases: node_lists(|node| node.bases.as_slice()),
            node_owned: node_lists(|node| node.owned.as_slice()),
            node_features: node_lists(|node| node.owned_features.as_slice()),
            member_rows: Ints(members.iter().map(|&(r, _)| r).collect()),
            member_targets: Ints(members.iter().map(|&(_, m)| m.target).collect()),
            member_scopes: Ints(
                members
                    .iter()
                    .map(|&(_, m)| m.scope.unwrap_or(scopes))
                    .collect(),
            ),
            member_visibility: Bytes(members.iter().map(|&(_, m)| m.visibility as u8).collect()),
            member_aliases: members
                .iter()
                .map(|&(_, m)| m.alias)
                .collect::<Vec<bool>>()
                .into(),
            member_name_counts: Ints(members.iter().map(|&(_, m)| m.names.len()).collect()),
            member_names: members
                .iter()
                .flat_map(|&(_, m)| m.names.iter().cloned())
                .collect(),
            header_bases,
            features: Ints(features),
            redefinitions,
            redefinitions_open,
            inherited,
            inherited_open,
            suppressed,
            absent_roots,
        }
    }

    /// The graph read back from its wire form for the rows of `b`; `None`
    /// when the wire does not fit them — a row or scope count, an index or a
    /// visibility the rows do not have, a table with a key twice, a node's
    /// owned row or a memoized projection's row that is no Membership of the
    /// graph — in which case the caller builds one. The id map is made from
    /// the rows.
    pub(super) fn from_wire(wire: GraphWire, b: &Builder) -> Option<Self> {
        let elements = b.elements.len();
        let scopes = b.scopes.len();
        if wire.elements != elements || wire.scopes != scopes {
            return None;
        }
        let fits_row = |i: usize| (i < elements).then_some(i);
        let fits_scope = |i: usize| (i < scopes).then_some(i);
        // keyed lists as a table: every key once, every index fitting
        fn table<V>(
            lists: IndexLists,
            key: impl Fn(usize) -> Option<usize>,
            value: impl Fn(usize) -> Option<usize>,
            wrap: impl Fn(Vec<usize>) -> V,
        ) -> Option<IdMap<usize, V>> {
            let lists = lists.into_lists()?;
            let mut table = IdMap::with_capacity_and_hasher(lists.len(), Default::default());
            for (k, values) in lists {
                if !values.iter().all(|&v| value(v).is_some()) {
                    return None;
                }
                if table.insert(key(k)?, wrap(values)).is_some() {
                    return None;
                }
            }
            Some(table)
        }
        // the rows of a table without a list, once each
        fn open<V: Clone>(
            table: &mut IdMap<usize, V>,
            keys: Ints,
            key: impl Fn(usize) -> Option<usize>,
            value: V,
        ) -> Option<()> {
            for k in keys.0 {
                if table.insert(key(k)?, value.clone()).is_some() {
                    return None;
                }
            }
            Some(())
        }
        let n = wire.member_rows.0.len();
        let aliases = wire.member_aliases.into_flags()?;
        let name_count = wire
            .member_name_counts
            .0
            .iter()
            .try_fold(0usize, |sum, &c| sum.checked_add(c))?;
        if wire.member_targets.0.len() != n
            || wire.member_scopes.0.len() != n
            || wire.member_visibility.0.len() != n
            || aliases.len() != n
            || wire.member_name_counts.0.len() != n
            || name_count != wire.member_names.len()
        {
            return None;
        }
        let mut names = wire.member_names.into_iter();
        let mut members = IdMap::with_capacity_and_hasher(n, Default::default());
        let columns = wire
            .member_rows
            .0
            .into_iter()
            .zip(wire.member_targets.0)
            .zip(wire.member_scopes.0)
            .zip(wire.member_visibility.0)
            .zip(aliases)
            .zip(wire.member_name_counts.0);
        for (((((r, target), scope), visibility), alias), count) in columns {
            let visibility = match visibility {
                0 => LookupAccess::Public,
                1 => LookupAccess::Protected,
                2 => LookupAccess::All,
                _ => return None,
            };
            let member = Member {
                target: fits_row(target)?,
                scope: if scope == scopes {
                    None
                } else {
                    Some(fits_scope(scope)?)
                },
                names: names.by_ref().take(count).collect(),
                visibility,
                alias,
            };
            if members.insert(fits_row(r)?, member).is_some() {
                return None;
            }
        }
        // the rows the lookups take as Memberships of the graph
        let is_member = |r: usize| members.contains_key(&r).then_some(r);
        let bases = wire.node_bases.into_lists()?;
        let owned = wire.node_owned.into_lists()?;
        let owned_features = wire.node_features.into_lists()?;
        if bases.len() != owned.len() || bases.len() != owned_features.len() {
            return None;
        }
        let mut nodes: Vec<Option<Node>> = vec![None; scopes];
        for (((s, bases), (s2, owned)), (s3, owned_features)) in
            bases.into_iter().zip(owned).zip(owned_features)
        {
            if s != s2 || s != s3 || fits_scope(s).is_none() || nodes[s].is_some() {
                return None;
            }
            if !bases.iter().all(|&x| fits_scope(x).is_some())
                || !owned.iter().all(|&x| is_member(x).is_some())
                || !owned_features.iter().all(|&x| fits_row(x).is_some())
            {
                return None;
            }
            nodes[s] = Some(Node {
                bases,
                owned,
                owned_features,
            });
        }
        let mut redefinitions = table(wire.redefinitions, fits_row, fits_row, Some)?;
        open(&mut redefinitions, wire.redefinitions_open, fits_row, None)?;
        let mut inherited = table(wire.inherited, fits_scope, is_member, |rows| {
            Some(Arc::new(rows))
        })?;
        open(&mut inherited, wire.inherited_open, fits_scope, None)?;
        let suppressed = table(wire.suppressed, fits_scope, is_member, Arc::new)?;
        let header_bases = table(wire.header_bases, fits_scope, fits_scope, |bases| bases)?;
        let mut features =
            IdMap::with_capacity_and_hasher(wire.features.0.len(), Default::default());
        for e in wire.features.0 {
            if features.insert(fits_row(e)?, ()).is_some() {
                return None;
            }
        }
        let mut ids = IdMap::with_capacity_and_hasher(elements, Default::default());
        for (e, element) in b.elements.iter().enumerate() {
            ids.insert(element.id, e);
        }
        Some(Self {
            nodes: LayeredVec::over(Arc::new(nodes)),
            members: LayeredMap::over(Arc::new(members)),
            header_bases: LayeredMap::over(Arc::new(header_bases)),
            has_ordered_headers: wire.has_ordered_headers,
            features: LayeredMap::over(Arc::new(features)),
            redefinitions: LayeredMap::over(Arc::new(redefinitions)),
            inherited: LayeredMap::over(Arc::new(inherited)),
            suppressed: LayeredMap::over(Arc::new(suppressed)),
            ids: LayeredMap::over(Arc::new(ids)),
            element_count: elements,
            absent_roots: wire.absent_roots.into_iter().collect(),
            ..Self::default()
        })
    }

    /// Cover the rows appended to `b` since this graph was built, from row
    /// `from`: the prepared library's own materialized rows (see
    /// `Builder::seal_prefix_semantics`), which are relationships without
    /// owned relationships of their own, so they join the id map and the
    /// row count and no other table; a snapshot's wire then fits the rows
    /// the library has, and a build on them reads the rows by id.
    /// This graph read over its first `rows` rows only: the frozen graph of
    /// a prepared library whose own materialized rows a build leaves out
    /// (see `Builder::truncate_prefix_to_source_rows`). Its tables were made
    /// over those rows before the materialized rows were added (see
    /// [`Self::cover_rows`]), which added their ids alone; the ids stay,
    /// as no source row names one.
    pub(super) fn over_rows(&self, rows: usize) -> Self {
        debug_assert!(rows <= self.element_count);
        let mut graph = self.clone();
        graph.element_count = rows;
        graph
    }

    pub(super) fn cover_rows(&mut self, b: &Builder, from: usize) {
        debug_assert_eq!(
            self.element_count, from,
            "the graph covers the rows before `from`"
        );
        debug_assert_eq!(self.nodes.len(), b.scopes.len(), "the rows add no scope");
        for (e, element) in b.elements.iter().enumerate().skip(from) {
            debug_assert!(
                is_a!(element, "Relationship") && element.owned_relationships.is_empty(),
                "row {e} is a materialized relationship"
            );
            self.ids.insert(element.id, e);
        }
        self.element_count = b.elements.len();
    }

    pub(super) fn freeze(&mut self) {
        self.nodes.freeze();
        self.members.freeze();
        self.header_bases.freeze();
        self.features.freeze();
        self.redefinitions.freeze();
        self.inherited.freeze();
        self.suppressed.freeze();
        self.ids.freeze();
        // Builds on a prepared library never record resolution outcomes.
        self.input_misses.clear();
        self.redefinition_misses.clear();
        self.header_misses.clear();
        self.collected_misses.clear();
    }

    /// The rows by id, when the table is frozen whole.
    pub(super) fn frozen_ids(&self) -> Option<Arc<crate::layered::IdMap<uuid::Uuid, usize>>> {
        self.ids.frozen_arc().cloned()
    }

    /// [`Self::frozen_ids`] when the graph tables exactly `rows` rows.
    pub(super) fn frozen_ids_over(
        &self,
        rows: usize,
    ) -> Option<Arc<crate::layered::IdMap<uuid::Uuid, usize>>> {
        (self.element_count == rows).then(|| self.frozen_ids())?
    }

    pub(super) fn has_replay_context(&mut self) -> bool {
        // Whether passes follow is not an outcome of any one reference.
        let misses = &mut Vec::new();
        self.has_ordered_headers
            || (0..self.nodes.len()).any(|s| {
                self.nodes[s]
                    .as_ref()
                    .is_some_and(|node| !node.bases.is_empty())
                    && self.direct_bases(s, misses).is_some()
            })
    }

    /// The header bases of `scope`; the root misses behind them (or behind
    /// their absence) join `misses`.
    pub(super) fn header_bases(
        &self,
        scope: usize,
        misses: &mut Vec<String>,
    ) -> Option<Vec<usize>> {
        note(misses, &self.header_misses, scope);
        self.header_bases.get(&scope).cloned()
    }

    /// The direct bases of `scope` when every inherited projection they
    /// need is recorded; the root misses behind that answer join `misses`.
    pub(super) fn direct_bases(
        &mut self,
        scope: usize,
        misses: &mut Vec<String>,
    ) -> Option<Vec<usize>> {
        note(misses, &self.input_misses, scope);
        let bases = self.nodes.get(scope)?.as_ref()?.bases.clone();
        for &base in &bases {
            self.collect(base, false, misses)?;
        }
        Some(bases)
    }

    fn closure(&self, source: usize, misses: &mut Vec<String>) -> Option<HashSet<usize>> {
        let mut found = HashSet::new();
        let mut todo = vec![source];
        while let Some(e) = todo.pop() {
            if !found.insert(e) {
                continue;
            }
            if let Some(targets) = self.redefinitions.get(&e) {
                note(misses, &self.redefinition_misses, e);
                todo.extend(targets.as_ref()?.iter().copied());
            }
        }
        Some(found)
    }

    /// The inherited projection of `root`; the root misses behind it — or
    /// behind its absence — join `misses`.
    fn collect(
        &mut self,
        root: usize,
        skip_owned: bool,
        misses: &mut Vec<String>,
    ) -> Option<Arc<Vec<usize>>> {
        if !skip_owned {
            if let Some(result) = self.inherited.get(&root) {
                note(misses, &self.collected_misses, root);
                return result.clone();
            }
        }
        let mut read = Vec::new();
        let result = self.collect_uncached(root, skip_owned, &mut read);
        super::note_misses(misses, &read);
        if !skip_owned {
            self.inherited.insert(root, result.clone());
            keep(&mut self.collected_misses, root, read);
        }
        result
    }

    /// `read` gathers the root misses behind every node, projection and
    /// redefinition the answer reads, including one it gave up on.
    fn collect_uncached(
        &mut self,
        root: usize,
        skip_owned: bool,
        read: &mut Vec<String>,
    ) -> Option<Arc<Vec<usize>>> {
        if !skip_owned {
            if let Some(value) = self.inherited.get(&root) {
                note(read, &self.collected_misses, root);
                return value.clone();
            }
        }
        let mut state = HashMap::new();
        let mut order = Vec::new();
        let mut todo = vec![(root, false)];
        while let Some((s, exiting)) = todo.pop() {
            if s != root && self.inherited.contains_key(&s) {
                note(read, &self.collected_misses, s);
                continue;
            }
            if exiting {
                state.insert(s, 2);
                order.push(s);
                continue;
            }
            match state.get(&s) {
                Some(1) => return None,
                Some(2) => continue,
                _ => {}
            }
            note(read, &self.input_misses, s);
            let node = self.nodes.get(s)?.as_ref()?;
            state.insert(s, 1);
            todo.push((s, true));
            todo.extend(node.bases.iter().rev().map(|&base| (base, false)));
        }
        let mut result = None;
        for s in order {
            let node = self.nodes[s].as_ref()?.clone();
            // What this scope's projection reads, kept with its memo.
            let mut here = Vec::new();
            note(&mut here, &self.input_misses, s);
            let mut rows = Vec::new();
            let mut seen = HashSet::new();
            let mut suppressed = Vec::new();
            let mut suppressed_seen = HashSet::new();
            for base in node.bases {
                note(&mut here, &self.collected_misses, base);
                note(read, &self.collected_misses, base);
                if let Some(prior) = self.suppressed.get(&base) {
                    for &m in prior.iter() {
                        if suppressed_seen.insert(m) {
                            suppressed.push(m);
                        }
                    }
                }
                let base_node = self.nodes[base].as_ref()?;
                let inherited = self.inherited.get(&base)?.as_ref()?;
                for &m in base_node.owned.iter().chain(inherited.iter()) {
                    if seen.insert(m) {
                        rows.push(m);
                    }
                }
            }
            let mut owned_direct = HashSet::new();
            if !(s == root && skip_owned) {
                for feature in node.owned_features {
                    if let Some(targets) = self.redefinitions.get(&feature) {
                        note(&mut here, &self.redefinition_misses, feature);
                        note(read, &self.redefinition_misses, feature);
                        owned_direct.extend(targets.as_ref()?.iter().copied());
                    }
                }
            }
            let mut inherited_features = HashSet::new();
            for &m in &rows {
                let e = self.members.get(&m)?.target;
                if self.features.contains_key(&e) {
                    inherited_features.insert(e);
                }
            }
            // As the projection reducer: a Feature's Memberships are removed
            // by another inherited Feature's redefinition closure or by an
            // owned redefinition, never by another Membership of itself.
            let mut removed = HashSet::new();
            for &e in &inherited_features {
                let Some(closure) = self.closure(e, &mut here) else {
                    super::note_misses(read, &here);
                    return None;
                };
                removed.extend(closure.iter().copied().filter(|&t| t != e));
                if !closure.is_disjoint(&owned_direct) {
                    removed.insert(e);
                }
            }
            super::note_misses(read, &here);
            rows.retain(|m| {
                let retain = !self
                    .features
                    .contains_key(&self.members.get(m).unwrap().target)
                    || !removed.contains(&self.members.get(m).unwrap().target);
                if !retain && suppressed_seen.insert(*m) {
                    suppressed.push(*m);
                }
                retain
            });
            self.suppressed.insert(s, Arc::new(suppressed));
            let rows = Arc::new(rows);
            if s != root || !skip_owned {
                self.inherited.insert(s, Some(Arc::clone(&rows)));
                keep(&mut self.collected_misses, s, here);
            }
            if s == root {
                result = Some(rows);
            }
        }
        result
    }

    /// Inherited members of `scope` named `name`; the root misses behind the
    /// answer — or behind its absence — join `misses`.
    pub(super) fn select(
        &mut self,
        scope: usize,
        name: &str,
        access: LookupAccess,
        exclude: Option<usize>,
        skip_owned: bool,
        misses: &mut Vec<String>,
    ) -> Option<(Vec<LookupResult>, bool)> {
        let rows = self.collect(scope, skip_owned, misses)?;
        let hits: Vec<_> = rows
            .iter()
            .filter_map(|m| {
                let member = &self.members.get(m).unwrap();
                (Some(member.target) != exclude
                    && access.inherited().admits(member.visibility)
                    && member.names.iter().any(|n| n == name))
                .then_some(LookupResult::Found(
                    member.target,
                    member.scope,
                    member.alias.then_some(*m),
                ))
            })
            .collect();
        let suppressed = hits.is_empty()
            && self.suppressed.get(&scope).is_some_and(|rows| {
                rows.iter().any(|m| {
                    let member = &self.members.get(m).unwrap();
                    Some(member.target) != exclude
                        && access.inherited().admits(member.visibility)
                        && member.names.iter().any(|n| n == name)
                })
            });
        Some((hits, suppressed))
    }
}

/// Resolution mutates pending properties and query state, never declaration
/// topology. Keep one bounded rollback point instead of cloning every element,
/// source scope and expression table before each fixed-point pass.
pub(super) struct Checkpoint {
    properties: Vec<(usize, crate::properties::Properties)>,
    spec_resolved: crate::layered::LayeredVec<Option<usize>>,
    spec_misses: MissTable,
    ref_misses: MissTable,
    semantic_memo: crate::semantic_memo::SemanticMemo,
    metadata: super::metadata_associations::Snapshot,
    unresolved: Vec<(usize, super::QualifiedName)>,
    ambiguous: Vec<(usize, super::QualifiedName)>,
    blocked: Vec<super::BlockedSite>,
    sites: Vec<super::RefSite>,
    used: crate::layered::IdSet<usize>,
    roots: HashSet<String>,
    identity_pending: Vec<super::PendingRef>,
    pub(super) lib_record: Option<Vec<(Option<uuid::Uuid>, Vec<String>)>>,
    library_refs_to_users: bool,
    query_imports: super::ImportWalks,
    current_misses: Vec<String>,
    exclude: Option<usize>,
    declared_only: bool,
    identity_origin: Option<usize>,
    header_owner: Option<usize>,
    header_base: Option<usize>,
    suppressed: bool,
    probing: bool,
    widen: Option<(usize, LookupAccess)>,
    element_count: usize,
    scope_count: usize,
}
impl Checkpoint {
    pub(super) fn capture(b: &Builder, pending: &[super::PendingRef]) -> Self {
        let mut seen = HashSet::new();
        Self {
            properties: pending
                .iter()
                .filter(|p| seen.insert(p.elem))
                .map(|p| (p.elem, b.elements[p.elem].props.clone()))
                .collect(),
            spec_resolved: b.spec_resolved.clone(),
            spec_misses: b.spec_misses.clone(),
            ref_misses: b.ref_misses.clone(),
            semantic_memo: b.semantic_memo.clone(),
            metadata: b.metadata_snapshot(),
            unresolved: b.unresolved.clone(),
            ambiguous: b.ambiguous.clone(),
            blocked: b.blocked.clone(),
            sites: b.ref_sites.clone(),
            used: b.used_imports.clone(),
            roots: b.root_misses.clone(),
            identity_pending: b.id_binding_pending.clone(),
            lib_record: b.lib_record.clone(),
            library_refs_to_users: b.library_refs_to_users,
            query_imports: b.query_imports.clone(),
            current_misses: b.current_misses.clone(),
            exclude: b.exclude,
            declared_only: b.declared_only,
            identity_origin: b.identity_origin_unit,
            header_owner: b.redefinition_lookup_owner,
            header_base: b.redefinition_lookup_base,
            suppressed: b.recorded_lookup_suppressed,
            probing: b.probing,
            widen: b.widen,
            element_count: b.elements.len(),
            scope_count: b.scopes.len(),
        }
    }
    pub(super) fn restore(&self, b: &mut Builder) {
        debug_assert_eq!(b.elements.len(), self.element_count);
        debug_assert_eq!(b.scopes.len(), self.scope_count);
        for (e, props) in &self.properties {
            b.elements[*e].props = props.clone();
        }
        b.restore_metadata_snapshot(&self.metadata);
        b.spec_resolved = self.spec_resolved.clone();
        b.spec_misses = self.spec_misses.clone();
        b.ref_misses = self.ref_misses.clone();
        b.semantic_memo = self.semantic_memo.clone();
        b.unresolved = self.unresolved.clone();
        b.ambiguous = self.ambiguous.clone();
        b.blocked = self.blocked.clone();
        b.ref_sites = self.sites.clone();
        b.used_imports = self.used.clone();
        b.root_misses = self.roots.clone();
        b.id_binding_pending = self.identity_pending.clone();
        b.lib_record = self.lib_record.clone();
        b.library_refs_to_users = self.library_refs_to_users;
        b.query_imports = self.query_imports.clone();
        b.current_misses = self.current_misses.clone();
        b.exclude = self.exclude;
        b.declared_only = self.declared_only;
        b.identity_origin_unit = self.identity_origin;
        b.redefinition_lookup_owner = self.header_owner;
        b.redefinition_lookup_base = self.header_base;
        b.recorded_lookup_suppressed = self.suppressed;
        b.probing = self.probing;
        b.widen = self.widen;
        b.pending.clear();
        b.lib_hints = None;
        b.replay_completions = None;
        b.reset_lookup_caches();
    }
}

#[cfg(test)]
mod tests {
    use crate::{json::ResolvedModel, libcache::LibraryCache, model::Model};
    use sysmlv2_syntax::ast::QualifiedName;

    /// Replay passes may take a recorded library outcome again, but only a
    /// target: a recorded miss is resolved afresh, so a library name that is
    /// ambiguous (not missing) is reported as a cold build reports it.
    #[test]
    fn replayed_library_misses_keep_cold_classification() {
        let library = "standard library package L { \
            package A { class X; } package B { class X; } \
            private import A::*; private import B::*; \
            class P { feature f; } class Q :> P { feature redefines f; } \
            class Y :> X; class Z :> Missing; }";
        let user = "class C :> L::Q { feature redefines f; }";
        let mut base = Model::new();
        assert!(
            base.add_library_source("lib.kerml", library)
                .diagnostics
                .is_empty()
        );
        base.record_library_cache();
        ResolvedModel::build(&base);
        let cache =
            LibraryCache::from_bytes(&base.take_recorded_library_cache().unwrap().to_bytes())
                .unwrap();
        let build = |warm: bool| {
            let mut model = Model::new();
            model.add_library_source("lib.kerml", library);
            if warm {
                model.set_library_cache(cache.clone());
            }
            assert!(model.add_source("user.kerml", user).diagnostics.is_empty());
            ResolvedModel::build(&model)
        };
        let names = |refs: &[(usize, QualifiedName)]| {
            refs.iter()
                .map(|(e, qn)| (*e, qn.to_ref_string()))
                .collect::<Vec<_>>()
        };
        let (cold, warm) = (build(false), build(true));
        assert_eq!(names(&cold.b.ambiguous).len(), 1, "`X` is ambiguous");
        assert_eq!(names(&cold.b.unresolved).len(), 1, "`Missing` is missing");
        assert_eq!(names(&warm.b.ambiguous), names(&cold.b.ambiguous));
        assert_eq!(names(&warm.b.unresolved), names(&cold.b.unresolved));
    }
}

#[cfg(test)]
thread_local! {
    static SETTLED: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}
#[cfg(test)]
pub(super) fn settled_passes() -> usize {
    SETTLED.with(|c| c.get())
}
#[cfg(test)]
fn note_settled() {
    SETTLED.with(|c| c.set(c.get() + 1));
}
#[cfg(not(test))]
fn note_settled() {}

#[cfg(test)]
mod settle_tests {
    use super::*;
    use crate::{json::ResolvedModel, model::Model};

    /// A redefinition chain the bootstrap already resolves: the first redo
    /// pass changes nothing, and the loop settles the graph it read instead
    /// of building another; the settled graph is one built from the final
    /// rows in every table, with and without a recording's miss tables.
    #[test]
    fn a_confirming_pass_settles_the_graph_it_read() {
        for recording in [false, true] {
            let mut model = Model::new();
            let parsed = model.add_source(
                "chain.kerml",
                "class A { feature x; } class B :> A { feature :>> x; } \
                 class C :> B { feature :>> x; } class D :> C { feature :>> x; }",
            );
            assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
            if recording {
                model.record_library_cache();
            }
            let settled_before = settled_passes();
            let r = ResolvedModel::build(&model);
            assert!(
                settled_passes() > settled_before,
                "the build ended on a pass that changed nothing"
            );
            assert!(
                r.b.recorded_lookup_graph.is_some(),
                "the settled graph is kept"
            );
            let mut settled = r.b.recorded_lookup_graph.clone().unwrap();
            let mut fresh = Graph::build(&r.b);
            let mut misses = Vec::new();
            assert_eq!(settled.has_replay_context(), fresh.has_replay_context());
            assert_eq!(settled.element_count, fresh.element_count);
            assert_eq!(settled.absent_roots, fresh.absent_roots);
            assert_eq!(settled.has_ordered_headers, fresh.has_ordered_headers);
            let scopes = r.b.scopes.len();
            let elements = r.b.elements.len();
            let table = |t: &MissTable, n: usize| {
                (0..n)
                    .map(|i| t.get(i).map(|m| m.to_vec()))
                    .collect::<Vec<_>>()
            };
            for scope in 0..scopes {
                assert_eq!(
                    settled.nodes[scope], fresh.nodes[scope],
                    "node of scope {scope}"
                );
                assert_eq!(
                    settled.header_bases.get(&scope),
                    fresh.header_bases.get(&scope),
                    "header bases of scope {scope}"
                );
                assert_eq!(
                    settled.header_bases(scope, &mut misses),
                    fresh.header_bases(scope, &mut misses),
                    "header bases read for scope {scope}"
                );
                assert_eq!(
                    settled.direct_bases(scope, &mut misses),
                    fresh.direct_bases(scope, &mut misses),
                    "bases of scope {scope}"
                );
            }
            // A recording's miss tables grow after the settle (the root-import
            // pseudo miss joins every outcome's misses at the end of the
            // build), so a graph built then differs from the settled one
            // there by design: compared only where nothing is recorded.
            if !recording {
                assert_eq!(
                    table(&settled.header_misses, scopes),
                    table(&fresh.header_misses, scopes)
                );
                assert_eq!(
                    table(&settled.input_misses, scopes),
                    table(&fresh.input_misses, scopes)
                );
                assert_eq!(
                    table(&settled.redefinition_misses, elements),
                    table(&fresh.redefinition_misses, elements)
                );
            }
            // (`inherited`, `suppressed` and `collected_misses` are memos the
            // lookups after the settle fill again, as they would a fresh graph's.)
            for e in 0..elements {
                assert_eq!(settled.members.get(&e), fresh.members.get(&e), "member {e}");
                assert_eq!(
                    settled.redefinitions.get(&e),
                    fresh.redefinitions.get(&e),
                    "redefinitions of {e}"
                );
                assert_eq!(
                    settled.features.contains_key(&e),
                    fresh.features.contains_key(&e)
                );
            }
            // `ids` is a build-time table of the identities the rows had when
            // the graph was built, which the identity assignment after the
            // settle rewrote for a fresh build: compared by count only.
            assert_eq!(settled.ids.iter().count(), fresh.ids.iter().count());
            // the chain's three redefinitions each resolved to a feature
            let redefinitions: Vec<_> = (0..elements)
                .filter(|&e| r.b.elements[e].ty == "Redefinition")
                .collect();
            assert_eq!(redefinitions.len(), 3);
            for &e in &redefinitions {
                let target = r.b.elements[e]
                    .props
                    .get("redefinedFeature")
                    .and_then(|v| v.as_reference())
                    .expect("resolved");
                let target_row = fresh.ids.get(&target).copied().expect("a row");
                assert_eq!(r.b.elements[target_row].ty, "Feature");
            }
            if recording {
                assert!(
                    (0..scopes).any(|s| settled.input_misses.get(s).is_some()),
                    "a recording attributes misses"
                );
            }
        }
    }
}

#[cfg(test)]
mod wire_tests {
    use super::*;
    use crate::{json::ResolvedModel, model::Model};

    /// A frozen graph written as a snapshot carries it reads back as the
    /// same graph, with the rows' ids; a wire whose indices, visibilities or
    /// keys do not fit the rows is refused.
    #[test]
    fn a_graph_round_trips_through_its_wire_and_a_misfit_is_refused() {
        let mut model = Model::new();
        let parsed = model.add_source(
            "graph.kerml",
            "class A { feature x; protected feature y; } \
             class B :> A { feature :>> x; alias z for x; } \
             package N { class C; } alias D for N::C;",
        );
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let r = ResolvedModel::build(&model);
        let mut graph = Graph::build(&r.b);
        graph.freeze();
        let wire = graph.to_wire();
        assert!(!wire.member_rows.0.is_empty(), "the model has Memberships");
        assert!(
            !wire.node_bases.clone().into_lists().unwrap().is_empty(),
            "the model has nodes"
        );
        let read = Graph::from_wire(wire.clone(), &r.b).expect("the wire fits its rows");
        assert_eq!(read.to_wire(), wire);
        assert_eq!(read.ids.get(&r.b.elements[0].id), Some(&0));
        assert_eq!(read.ids.iter().count(), r.b.elements.len());
        let elements = r.b.elements.len();
        let mut misfit = wire.clone();
        misfit.member_targets.0[0] = elements;
        assert!(
            Graph::from_wire(misfit, &r.b).is_none(),
            "a member beyond the rows"
        );
        let mut misfit = wire.clone();
        misfit.member_visibility.0[0] = 3;
        assert!(
            Graph::from_wire(misfit, &r.b).is_none(),
            "a visibility there is not"
        );
        let mut misfit = wire.clone();
        misfit.features.0.push(misfit.features.0[0]);
        assert!(Graph::from_wire(misfit, &r.b).is_none(), "a Feature twice");
        let mut misfit = wire.clone();
        misfit.member_name_counts.0[0] += 1;
        assert!(
            Graph::from_wire(misfit, &r.b).is_none(),
            "names not covered"
        );
        let feature = wire.features.0[0];
        assert!(!wire.member_rows.0.contains(&feature));
        let mut misfit = wire.clone();
        let mut owned = misfit.node_owned.into_lists().unwrap();
        owned[0].1.push(feature);
        misfit.node_owned = owned.into();
        assert!(
            Graph::from_wire(misfit, &r.b).is_none(),
            "an owned row that is no Membership"
        );
        let mut misfit = wire.clone();
        misfit.suppressed = vec![(0, vec![feature])].into();
        assert!(
            Graph::from_wire(misfit, &r.b).is_none(),
            "a suppressed row that is no Membership"
        );
        let mut misfit = wire;
        misfit.scopes += 1;
        assert!(
            Graph::from_wire(misfit, &r.b).is_none(),
            "another scope count"
        );
    }
}
