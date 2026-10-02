//! Recorded-only inherited name selection for complete explicit heritage.
//! Complex import, filter, chain and implied-heritage contexts retain the
//! contextual resolver until those dependencies share a complete recorded plan.

use super::{Builder, LookupAccess, LookupResult, MissTable};
use crate::layered::{LayeredMap, LayeredVec};
use crate::metaclass::conforms;
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
        let has_redefinition = b.elements.iter().any(|e| conforms(e.ty, "Redefinition"));
        let candidate = b.scopes.iter().any(|s| {
            !s.aliases.is_empty()
                || s.bases.len() > 1
                || (!s.bases.is_empty()
                    && s.owner.is_some_and(|owner| {
                        b.elements[owner]
                            .owned_relationships
                            .iter()
                            .any(|&r| conforms(b.elements[r].ty, "Membership"))
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
        if !conforms(b.elements[owner].ty, "Type")
            || conforms(b.elements[owner].ty, "Definition")
            || conforms(b.elements[owner].ty, "Usage")
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
                    conforms(b.elements[r].ty, "ParameterMembership")
                        || conforms(b.elements[r].ty, "ReturnParameterMembership")
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
            if conforms(element.ty, "Feature") {
                graph.features.insert(e, ());
            }
            let positional_source = conforms(element.ty, "Usage")
                || element.props.get("isEnd").and_then(|v| v.as_bool()) == Some(true)
                || element.owning_relationship.is_some_and(|r| {
                    conforms(b.elements[r].ty, "ParameterMembership")
                        || conforms(b.elements[r].ty, "ReturnParameterMembership")
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
                if conforms(b.elements[r].ty, "Redefinition") {
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
            if let Some(owner) = scope.owner.filter(|&e| conforms(b.elements[e].ty, "Type")) {
                let mut misses = Vec::new();
                for &r in &b.elements[owner].owned_relationships {
                    if conforms(b.elements[r].ty, "Specialization") {
                        note(&mut misses, &b.ref_misses, r);
                    }
                }
                let bases: Option<Vec<_>> = b.elements[owner]
                    .owned_relationships
                    .iter()
                    .copied()
                    .filter(|&r| conforms(b.elements[r].ty, "Specialization"))
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
                    if scope.chain_bases.is_empty() && bases.len() == scope.bases.len() {
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
                    if conforms(relation.ty, "Specialization")
                        || (conforms(relation.ty, "Membership")
                            && !conforms(relation.ty, "OwningMembership"))
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
                if conforms(relation.ty, "Specialization") {
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
                if !conforms(relation.ty, "Membership") {
                    continue;
                }
                let visibility = match relation.props.get("visibility").and_then(|v| v.as_str()) {
                    Some("private") => continue,
                    Some("protected") => LookupAccess::Protected,
                    _ => LookupAccess::Public,
                };
                let member = if conforms(relation.ty, "OwningMembership") {
                    relation.children.first().copied()
                } else {
                    target(r, "memberElement")
                };
                let Some(member) = member else {
                    complete = false;
                    continue;
                };
                let alias = !conforms(relation.ty, "OwningMembership");
                let props = if alias {
                    &relation.props
                } else {
                    &b.elements[member].props
                };
                let keys = if alias {
                    ["memberName", "memberShortName"]
                } else {
                    ["declaredName", "declaredShortName"]
                };
                let names: Vec<_> = keys
                    .iter()
                    .filter_map(|key| props.get(key).and_then(|v| v.as_str()).map(str::to_owned))
                    .collect();
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
            if complete && written_bases == scope.bases.len() {
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
                        .any(|&r| conforms(b.elements[r].ty, "Redefinition"))
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
            let mut counts = HashMap::new();
            for &m in &rows {
                let e = self.members.get(&m)?.target;
                if self.features.contains_key(&e) {
                    *counts.entry(e).or_insert(0usize) += 1;
                }
            }
            let mut removed = HashSet::new();
            for (&e, &count) in &counts {
                let Some(closure) = self.closure(e, &mut here) else {
                    super::note_misses(read, &here);
                    return None;
                };
                removed.extend(closure.iter().copied().filter(|&t| t != e || count > 1));
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
