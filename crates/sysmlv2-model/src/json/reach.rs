//! What a lookup in a scope can reach, so that a lookup that misses stops
//! early.
//!
//! A name looked up in a scope is found among the scope's own names — its
//! declared and effective names, its aliases, its implied end names, the
//! names its membership imports bring in — or through its bases and its
//! namespace imports, transitively; through a recursive import, in every
//! nested scope of the imported namespace as well. A lookup that finds
//! nothing walks all of that, once per query, and a model being typed
//! misses constantly: on a model with a few hundred unresolved references
//! and recursive imports of a large namespace, the resolver visited scopes
//! thirty million times per pass, nearly all of them to find nothing.
//!
//! This module keeps, per scope, the set of names such a walk could find
//! — a superset: visibility, exclusion, filters and redefinition only take
//! away from it — and the lookups skip a base, an import or a nested
//! scope whose set lacks the name. The sets are a function of structure
//! that does not change within a build once read: the scopes' name tables
//! are written by the build, and the resolved bases and imports the walk
//! reads are kept by the lookup caches for the rest of the build. So the
//! sets are made once per build, lazily, for the closure a lookup reaches,
//! and shared; appended scopes and a dynamic plan, which can add bases
//! and members, set the index aside.
//!
//! The reach graph has two kinds of node per scope: the lookups in the
//! scope ([`Node::Lookup`], what [`Builder::lookup_body`] walks: the own
//! names plus the lookups in the bases and the imports), and those of the
//! scope and every nested scope ([`Node::Tree`], what
//! [`Builder::lookup_recursive`] walks for a recursive import). Imports
//! and heritage can be cyclic, so the sets are made per strongly connected
//! component, in reverse topological order. A node keeps its own names
//! apart from what it reaches through its edges, and nodes with the same
//! edges share that part: every type specializing one base, every package
//! importing one set of packages, holds one copy of the names beyond it.

use super::{Builder, FillMisses};
use crate::layered::{IdMap, IdSet};
use std::sync::Arc;

/// The names a lookup through a node of the reach graph can find, as
/// [`name_hash`]es: the node's own, and those beyond its edges. With them,
/// the root misses behind the lookup caches such a walk reads (see
/// [`Builder::note_fill_misses`]): a lookup that skips the walk notes them
/// as the walk would have — those of the whole closure, where a walk
/// under public access would not have entered a non-public import.
#[derive(Default)]
pub(super) struct Reach {
    /// The names found without leaving the node's scopes, sorted.
    own: Box<[u64]>,
    /// The names found beyond the node's edges, shared with every node
    /// whose edges lead to the same reaches.
    beyond: Option<Arc<IdSet<u64>>>,
    misses: Vec<String>,
}

impl Reach {
    /// Whether a name with this hash could be found.
    fn may_have(&self, hash: u64) -> bool {
        self.own.binary_search(&hash).is_ok()
            || self
                .beyond
                .as_ref()
                .is_some_and(|beyond| beyond.contains(&hash))
    }

    /// Every name hash, sorted.
    #[cfg(test)]
    fn names(&self) -> Vec<u64> {
        let mut names: Vec<u64> = self.own.to_vec();
        if let Some(beyond) = &self.beyond {
            names.extend(beyond.iter().copied());
        }
        names.sort_unstable();
        names.dedup();
        names
    }
}

/// The names beyond a set of reaches, made once per set: the key is the
/// reaches' identities, which the value keeps alive.
pub(super) type Beyond =
    std::collections::HashMap<Box<[usize]>, (Vec<Arc<Reach>>, Arc<IdSet<u64>>)>;

/// A node of the reach graph.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(super) enum Node {
    /// The lookups in a scope: its own names, its bases' and its imports'.
    Lookup(usize),
    /// The lookups in a scope and in every scope nested in it, as a
    /// recursive import sees them.
    Tree(usize),
}

impl Node {
    fn scope(self) -> usize {
        match self {
            Self::Lookup(s) | Self::Tree(s) => s,
        }
    }

    /// The node's slot in a scope's memo row.
    fn slot(self) -> usize {
        match self {
            Self::Lookup(_) => 0,
            Self::Tree(_) => 1,
        }
    }

    /// The node as one number, for the component search's tables.
    fn key(self) -> usize {
        self.scope() * 2 + self.slot()
    }
}

/// The hash a name is kept under: FNV-1a over its bytes, a function of the
/// text alone.
pub(super) fn name_hash(name: &str) -> u64 {
    let mut hash: u64 = 0xcbf2_9ce4_8422_2325;
    for byte in name.bytes() {
        hash ^= u64::from(byte);
        hash = hash.wrapping_mul(0x0000_0100_0000_01b3);
    }
    hash
}

#[cfg(test)]
thread_local!(static PRUNING: std::cell::Cell<bool> = const { std::cell::Cell::new(true) });

/// A search of the reach graph from one node: Tarjan's strongly connected
/// components, iterative, over the nodes not yet in the memo.
struct Search {
    /// Each visited node's visit number, by node key.
    index: IdMap<usize, usize>,
    /// The lowest visit number reachable from each visited node, by visit
    /// number.
    low: Vec<usize>,
    /// The edges of each visited node, by node key.
    edges: IdMap<usize, Vec<Node>>,
    /// The nodes visited and not yet assigned to a component.
    stack: Vec<Node>,
    on_stack: IdSet<usize>,
    /// The nodes being visited, each with the next edge to follow.
    frames: Vec<(Node, usize)>,
}

impl Builder {
    /// Whether a lookup of a name (hashed as [`name_hash`]) through `node`
    /// could find anything. `false` only when the node's reach is known and
    /// lacks the name; the root misses behind that reach are then noted as
    /// the walk would have noted them.
    pub(super) fn may_reach(&mut self, node: Node, hash: u64) -> bool {
        #[cfg(test)]
        if !PRUNING.with(std::cell::Cell::get) {
            return true;
        }
        // A dynamic plan adds bases the structure does not have.
        if self.effective_dynamic_plan().is_some() {
            return true;
        }
        let Some(reach) = self.reach(node) else {
            return true;
        };
        if reach.may_have(hash) {
            return true;
        }
        if !reach.misses.is_empty() {
            super::note_misses(&mut self.current_misses, &reach.misses);
        }
        false
    }

    /// The reach of `node`, from the memo or made now with its closure;
    /// `None` when it cannot be made now (a cache the closure reads is
    /// being filled by the lookup this runs inside).
    fn reach(&mut self, node: Node) -> Option<Arc<Reach>> {
        if self.reach_scopes != self.scopes.len() {
            // Scopes were appended: a nested scope the memo did not see.
            self.reset_reach_memo();
        }
        if let Some(reach) = &self.reach_memo[node.scope()][node.slot()] {
            return Some(Arc::clone(reach));
        }
        self.search_reach(node)
    }

    /// Forget every reach made so far.
    pub(super) fn reset_reach_memo(&mut self) {
        let n = self.scopes.len();
        self.reach_memo = crate::layered::ScopeTable::new(self.scope_floor, n);
        self.reach_beyond.clear();
        self.reach_scopes = n;
    }

    fn memoized_reach(&self, node: Node) -> Option<&Arc<Reach>> {
        self.reach_memo[node.scope()][node.slot()].as_ref()
    }

    /// Make the reach of `root` and of every node its closure holds that
    /// the memo lacks, component by component.
    fn search_reach(&mut self, root: Node) -> Option<Arc<Reach>> {
        let mut search = Search {
            index: IdMap::default(),
            low: Vec::new(),
            edges: IdMap::default(),
            stack: Vec::new(),
            on_stack: IdSet::default(),
            frames: Vec::new(),
        };
        self.visit_reach(&mut search, root)?;
        while let Some(&(node, next)) = search.frames.last() {
            let edges = &search.edges[&node.key()];
            if let Some(&child) = edges.get(next) {
                search.frames.last_mut().expect("the frame just read").1 = next + 1;
                if self.memoized_reach(child).is_some() {
                    continue;
                }
                if let Some(&at) = search.index.get(&child.key()) {
                    if search.on_stack.contains(&child.key()) {
                        let here = search.index[&node.key()];
                        search.low[here] = search.low[here].min(at);
                    }
                    continue;
                }
                self.visit_reach(&mut search, child)?;
                continue;
            }
            search.frames.pop();
            let here = search.index[&node.key()];
            if search.low[here] == here {
                let mut members = Vec::new();
                loop {
                    let member = search.stack.pop().expect("the node is on the stack");
                    search.on_stack.remove(&member.key());
                    members.push(member);
                    if member == node {
                        break;
                    }
                }
                let reach = self.component_reach(&members, &search.edges);
                for member in members {
                    self.reach_memo[member.scope()][member.slot()] = Some(Arc::clone(&reach));
                }
            }
            if let Some(&(parent, _)) = search.frames.last() {
                let up = search.index[&parent.key()];
                search.low[up] = search.low[up].min(search.low[here]);
            }
        }
        self.memoized_reach(root).cloned()
    }

    /// Start visiting `node`: number it, read its edges, push its frame.
    fn visit_reach(&mut self, search: &mut Search, node: Node) -> Option<()> {
        let edges = self.reach_edges(node)?;
        debug_assert_eq!(
            self.scopes.len(),
            self.reach_scopes,
            "reading a node's edges lowers nothing"
        );
        let at = search.low.len();
        search.index.insert(node.key(), at);
        search.low.push(at);
        search.edges.insert(node.key(), edges);
        search.stack.push(node);
        search.on_stack.insert(node.key());
        search.frames.push((node, 0));
        Some(())
    }

    /// The nodes a lookup through `node` continues in; `None` when a cache
    /// it reads is being filled right now.
    fn reach_edges(&mut self, node: Node) -> Option<Vec<Node>> {
        match node {
            Node::Lookup(s) => {
                let filling =
                    |misses: Option<&FillMisses>| matches!(misses, Some(FillMisses::Filling(_)));
                if filling(self.base_misses.get(s)) || filling(self.import_misses.get(s)) {
                    return None;
                }
                let mut edges: Vec<Node> =
                    self.base_scopes(s).into_iter().map(Node::Lookup).collect();
                let imports = self.import_scopes(s);
                edges.extend(imports.iter().map(|entry| {
                    if entry.recursive {
                        Node::Tree(entry.scope)
                    } else {
                        Node::Lookup(entry.scope)
                    }
                }));
                Some(edges)
            }
            Node::Tree(s) => {
                let mut subs: Vec<usize> = self.scopes[s]
                    .names
                    .values()
                    .flatten()
                    .filter_map(|binding| binding.sub_scope)
                    .collect();
                subs.sort_unstable();
                subs.dedup();
                let mut edges = Vec::with_capacity(subs.len() + 1);
                edges.push(Node::Lookup(s));
                edges.extend(subs.into_iter().map(Node::Tree));
                Some(edges)
            }
        }
    }

    /// The reach shared by the members of one component: their own names
    /// and, beyond, the reach of every node they continue in outside the
    /// component, which the memo already holds.
    fn component_reach(&mut self, members: &[Node], edges: &IdMap<usize, Vec<Node>>) -> Arc<Reach> {
        let mut own = Vec::new();
        let mut own_misses = Vec::new();
        let mut children: Vec<Arc<Reach>> = Vec::new();
        for &member in members {
            if let Node::Lookup(s) = member {
                self.own_names_into(s, &mut own);
                self.fill_misses_into(s, &mut own_misses);
            }
            for child in &edges[&member.key()] {
                if members.contains(child) {
                    continue;
                }
                let reach = self
                    .memoized_reach(*child)
                    .expect("a node outside the component is in the memo");
                if !children.iter().any(|known| Arc::ptr_eq(known, reach)) {
                    children.push(Arc::clone(reach));
                }
            }
        }
        if own.is_empty() && own_misses.is_empty() {
            if let [only] = children.as_slice() {
                return Arc::clone(only);
            }
        }
        own.sort_unstable();
        own.dedup();
        let mut misses = own_misses;
        for child in &children {
            super::note_misses(&mut misses, &child.misses);
        }
        let beyond = (!children.is_empty()).then(|| self.beyond(children));
        Arc::new(Reach {
            own: own.into_boxed_slice(),
            beyond,
            misses,
        })
    }

    /// The names beyond a node whose edges lead to `children`: one set per
    /// distinct set of children.
    fn beyond(&mut self, children: Vec<Arc<Reach>>) -> Arc<IdSet<u64>> {
        let mut key: Vec<usize> = children
            .iter()
            .map(|child| Arc::as_ptr(child) as usize)
            .collect();
        key.sort_unstable();
        let key = key.into_boxed_slice();
        if let Some((_, beyond)) = self.reach_beyond.get(&key) {
            return Arc::clone(beyond);
        }
        let beyond = match children.as_slice() {
            // Everything beyond the only child is beyond this node too.
            [only] if only.own.is_empty() && only.beyond.is_some() => {
                Arc::clone(only.beyond.as_ref().expect("checked"))
            }
            _ => {
                let mut names = IdSet::default();
                for child in &children {
                    names.extend(child.own.iter().copied());
                    if let Some(beyond) = &child.beyond {
                        names.extend(beyond.iter().copied());
                    }
                }
                Arc::new(names)
            }
        };
        self.reach_beyond
            .insert(key, (children, Arc::clone(&beyond)));
        beyond
    }

    /// The names a lookup in scope `s` finds without leaving it.
    fn own_names_into(&self, s: usize, names: &mut Vec<u64>) {
        let scope = &self.scopes[s];
        names.extend(scope.names.iter().map(|(name, _)| name_hash(name)));
        names.extend(
            scope
                .effective_names
                .iter()
                .map(|(name, _)| name_hash(name)),
        );
        names.extend(scope.aliases.iter().map(|(name, _, _)| name_hash(name)));
        names.extend(
            scope
                .implied_ends
                .iter()
                .map(|(name, _, _)| name_hash(name)),
        );
        names.extend(scope.member_imports.iter().filter_map(|entry| {
            entry
                .target
                .segments
                .last()
                .map(|segment| name_hash(&segment.value))
        }));
    }

    /// The root misses behind the lookup caches of scope `s`.
    fn fill_misses_into(&self, s: usize, misses: &mut Vec<String>) {
        for table in [&self.base_misses, &self.import_misses] {
            if let Some(FillMisses::Missed(names)) = table.get(s) {
                super::note_misses(misses, names.iter());
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{check, json::ResolvedModel, model::Model, prepared::PreparedLibrary};

    /// What a build makes of a model, as far as pruning could change it:
    /// the graph, the findings, the sorted root misses and the unresolved
    /// and ambiguous counts.
    type Outcome = (String, Vec<String>, Vec<String>, usize, usize);

    fn outcome_of(model: &Model) -> Outcome {
        let r = ResolvedModel::build(model);
        let mut misses: Vec<String> = r.b.root_misses.iter().cloned().collect();
        misses.sort();
        let findings: Vec<String> = check::validate_model(model)
            .into_iter()
            .chain(check::validate_semantics(model))
            .map(|(unit, d)| format!("{unit}:{}:{}", d.span.start, d.message))
            .collect();
        (
            crate::json::model_to_compact_json(model).to_string(),
            findings,
            misses,
            r.b.unresolved.len(),
            r.b.ambiguous.len(),
        )
    }

    /// Build `model()` with and without pruning: the graph, the findings
    /// and the unresolved and ambiguous counts must agree, and the pruned
    /// build's root misses must hold the plain build's.
    fn same_with_and_without_pruning(model: impl Fn() -> Model) -> (Outcome, Outcome) {
        let run = |pruning: bool| {
            PRUNING.with(|p| p.set(pruning));
            let outcome = outcome_of(&model());
            PRUNING.with(|p| p.set(true));
            outcome
        };
        let (pruned, plain) = (run(true), run(false));
        assert_eq!(pruned.1, plain.1, "findings");
        assert!(
            plain.2.iter().all(|miss| pruned.2.contains(miss)),
            "root misses {:?} hold {:?}",
            pruned.2,
            plain.2
        );
        assert_eq!(
            (pruned.3, pruned.4),
            (plain.3, plain.4),
            "unresolved/ambiguous"
        );
        assert_eq!(pruned.0, plain.0, "graph");
        (pruned, plain)
    }

    fn model_of(sources: &[(&str, &str)]) -> Model {
        let mut model = Model::new();
        for (name, text) in sources {
            model.add_source(*name, text);
        }
        model
    }

    #[test]
    fn pruned_lookups_resolve_like_full_walks() {
        let (pruned, plain) = same_with_and_without_pruning(|| {
            model_of(&[(
                "m.sysml",
                "package Signals { package Body { attribute def Speed :> ScalarValues::Real; part def Engine { attribute rpm : ScalarValues::Real; part :>> parts; } } package Cabin { alias Temp for Body::Speed; part def Seat :> Body::Engine { attribute :>> rpm = 1; } } private import Missing::*; }
                 package Views { import Signals::**; import Signals::Body::*; part def Car { part engine : Engine; attribute speed : Speed; attribute temp : Temp; attribute nothing : Absent; part seat : Cabin::Seat; } connection def Link; connection link : Link connect Car::engine to Car::seat { ref :>> source; } }
                 package Cyclic { package A { import B::*; part def X; } package B { import A::*; part def Y :> X; } import A::**; part y : Y; part z : Z; }",
            )])
        });
        assert_eq!(pruned.2, plain.2, "the same root misses");
        assert!(pruned.3 >= 2, "the absent names are unresolved");
    }

    #[test]
    fn pruned_lookups_resolve_like_full_walks_across_units() {
        same_with_and_without_pruning(|| {
            model_of(&[
                (
                    "lib.sysml",
                    "package L { import Q::**; package Q { package Inner { part def Deep { attribute d : ScalarValues::Integer; } } private part def Hidden; } part def Base { attribute a; } }",
                ),
                (
                    "u.sysml",
                    "package U { import L::**; part def D :> Deep { attribute :>> d = 2; attribute b : Base; attribute h : Hidden; attribute m : Nope; } part def E :> L::Base { attribute :>> a = 3; } }",
                ),
            ])
        });
    }

    /// A skipped walk notes the root misses of its whole closure, where a
    /// walk under public access would not have entered a non-public import:
    /// the misses a library's recording keeps behind an outcome hold those
    /// of the plain build, and nothing else differs.
    #[test]
    fn a_skipped_walk_notes_the_misses_behind_a_private_import_too() {
        let source = "package S { private import Priv::*; part def Own; } package Priv { import Missing::*; part def P; } package U { import S::*; part own : Own; part x : Nope; }";
        same_with_and_without_pruning(|| model_of(&[("m.sysml", source)]));
        let recorded = |pruning: bool| {
            PRUNING.with(|p| p.set(pruning));
            let mut base = Model::new();
            base.add_library_source("lib.sysml", source);
            base.record_library_cache();
            let prepared = base.prepare_library().unwrap();
            let recording = prepared
                .recording
                .as_ref()
                .expect("a recording preparation records");
            let misses: Vec<Vec<String>> = recording
                .outcome_misses
                .iter()
                .map(|misses| {
                    let mut misses = misses.clone();
                    misses.sort();
                    misses
                })
                .collect();
            PRUNING.with(|p| p.set(true));
            (recording.outcomes.clone(), misses)
        };
        let (pruned, plain) = (recorded(true), recorded(false));
        assert_eq!(pruned.0, plain.0, "the same outcomes");
        assert_eq!(pruned.1.len(), plain.1.len());
        let mut widened = 0;
        for (pruned, plain) in pruned.1.iter().zip(&plain.1) {
            assert!(
                plain.iter().all(|miss| pruned.contains(miss)),
                "{pruned:?} hold {plain:?}"
            );
            if pruned != plain {
                assert!(pruned.contains(&"Missing".to_string()), "{pruned:?}");
                widened += 1;
            }
        }
        assert!(
            widened >= 1,
            "the lookup of the absent name noted the private import's miss"
        );
    }

    /// A build on a prepared library, replaying its recording, resolves
    /// the same with and without pruning — whether the library was
    /// prepared with or without it.
    #[test]
    fn builds_on_a_prepared_library_resolve_like_full_walks() {
        let library = "library package L { import M::**; package M { part def Deep { attribute d; } private part def Hidden; } part def Base { attribute a; } private import Missing::*; }";
        let user = "package U { import L::**; part def D :> Deep { attribute :>> d = 1; attribute b : Base; attribute h : Hidden; attribute m : Nope; } part def E :> L::Base { attribute :>> a = 2; } }";
        let prepare = |pruning: bool| {
            PRUNING.with(|p| p.set(pruning));
            let mut base = Model::new();
            base.add_library_source("lib.sysml", library);
            let prepared = base.prepare_library().unwrap();
            let prepared =
                Arc::new(PreparedLibrary::from_bytes(&prepared.to_bytes(5).unwrap(), 5).unwrap());
            PRUNING.with(|p| p.set(true));
            prepared
        };
        let mut outcomes = Vec::new();
        for prepared in [prepare(true), prepare(false)] {
            let (pruned, plain) = same_with_and_without_pruning(|| {
                let mut model = Model::new();
                Arc::clone(&prepared).install(&mut model).unwrap();
                model.add_source("u.sysml", user);
                model
            });
            assert!(pruned.3 >= 1, "the absent name is unresolved");
            outcomes.push((pruned, plain));
        }
        assert_eq!(
            outcomes[0].0.0, outcomes[1].0.0,
            "the same graph on either library"
        );
        assert_eq!(
            outcomes[0].0.1, outcomes[1].0.1,
            "the same findings on either library"
        );
    }

    /// A base whose resolution runs inside the fill of its own scope's
    /// caches meets its scope through a recursive import: the search gives
    /// up for that lookup, and the build resolves as without pruning.
    #[test]
    fn a_search_that_meets_a_cache_being_filled_gives_up_for_that_lookup() {
        let source = "package Outer { package P { part def A :> Q::X { attribute :>> xa = 1; attribute n : None; } } package Q { import R::**; } package R { import Outer::**; part def X { attribute xa; } } }";
        same_with_and_without_pruning(|| model_of(&[("m.sysml", source)]));
        let mut model = Model::new();
        model.add_source("m.sysml", source);
        let mut r = ResolvedModel::build(&model);
        let a = r.resolve_qualified("Outer::P::A").expect("A").0;
        let scope = r.b.elem_scope.get(&a).copied().expect("A has a body");
        let reach =
            r.b.reach(Node::Lookup(scope))
                .expect("made after the build");
        assert!(reach.may_have(name_hash("xa")), "inherits xa");
    }

    /// The reach of a recursive import holds the nested names and the
    /// inherited ones, and lacks what nothing reaches.
    #[test]
    fn the_reach_of_a_tree_holds_nested_and_inherited_names() {
        let mut model = Model::new();
        model.add_source(
            "m.sysml",
            "package P { part def A { attribute x; } package N { part def B :> A { attribute y; } } } package U { import P::**; part b : B; }",
        );
        let mut r = ResolvedModel::build(&model);
        let p = r.resolve_qualified("P").expect("P").0;
        let scope = r.b.elem_scope.get(&p).copied().expect("P has a body");
        let reach = r.b.reach(Node::Tree(scope)).expect("made");
        for name in ["A", "N", "B", "x", "y"] {
            assert!(reach.may_have(name_hash(name)), "{name} reachable");
        }
        for name in ["U", "b", "absent"] {
            assert!(!reach.may_have(name_hash(name)), "{name} not reachable");
        }
        let lookup = r.b.reach(Node::Lookup(scope)).expect("made");
        assert!(lookup.may_have(name_hash("A")) && !lookup.may_have(name_hash("y")));
    }

    /// Mutually importing packages reach each other's names, through one
    /// shared reach.
    #[test]
    fn cyclic_imports_share_one_reach() {
        let mut model = Model::new();
        model.add_source(
            "m.sysml",
            "package A { import B::*; part def X; } package B { import A::*; part def Y; }",
        );
        let mut r = ResolvedModel::build(&model);
        let scopes: Vec<usize> = ["A", "B"]
            .iter()
            .map(|name| {
                let e = r.resolve_qualified(name).expect(name).0;
                r.b.elem_scope.get(&e).copied().expect("a body")
            })
            .collect();
        let reaches: Vec<Arc<Reach>> = scopes
            .iter()
            .map(|&s| r.b.reach(Node::Lookup(s)).expect("made"))
            .collect();
        assert!(Arc::ptr_eq(&reaches[0], &reaches[1]), "one component");
        assert!(reaches[0].may_have(name_hash("X")) && reaches[0].may_have(name_hash("Y")));
    }

    /// Types with the same bases share the names beyond them; the reaches
    /// are the same whichever order the memo is filled in.
    #[test]
    fn reaches_share_what_lies_beyond_and_do_not_depend_on_the_order_made() {
        let source = "package P { part def A { attribute x; } part def B :> A { attribute y; } part def C :> A { attribute z; } package N { import P::*; part def D :> B, C; part def E :> B, C { attribute w; } } import N::**; }";
        let reaches = |reverse: bool| {
            let mut model = Model::new();
            model.add_source("m.sysml", source);
            let mut r = ResolvedModel::build(&model);
            let mut scopes: Vec<usize> = (r.b.scope_floor..r.b.scopes.len()).collect();
            if reverse {
                scopes.reverse();
            }
            let mut names: Vec<(usize, Vec<u64>, Vec<u64>)> = Vec::new();
            for s in scopes {
                let lookup = r.b.reach(Node::Lookup(s)).expect("made").names();
                let tree = r.b.reach(Node::Tree(s)).expect("made").names();
                names.push((s, lookup, tree));
            }
            names.sort();
            let beyond = |r: &mut ResolvedModel, name: &str| {
                let e = r.resolve_qualified(name).expect(name).0;
                let s = r.b.elem_scope.get(&e).copied().expect("a body");
                let reach = r.b.reach(Node::Lookup(s)).expect("made");
                reach.beyond.clone().expect("has bases")
            };
            let (b, c) = (beyond(&mut r, "P::B"), beyond(&mut r, "P::C"));
            assert!(Arc::ptr_eq(&b, &c), "B and C share what lies beyond A");
            let (d, e) = (beyond(&mut r, "P::N::D"), beyond(&mut r, "P::N::E"));
            assert!(
                Arc::ptr_eq(&d, &e),
                "D and E share what lies beyond B and C"
            );
            names
        };
        assert_eq!(reaches(false), reaches(true));
    }
}
