//! Structured graph emission (the browser host's native renderer
//! input). The same structure-view
//! semantics as the PlantUML tree emitter — shared [`classify`] keeps
//! the two backends agreeing about what is a node, a compartment row,
//! or invisible — but as data: nodes with element identity, source
//! spans, and rows; edges with kinds. Layout is the consumer's job.
//!
//! Shape:
//! ```json
//! {
//!   "view": "tree",
//!   "nodes": [{
//!     "id", "qname"?, "label", "stereo", "metaclass",
//!     "kind": "package" | "node" | "enum",
//!     "nodeKind"?: "def" | "usage" | "ref",  // notation shape triad
//!     "prefixes"?: ["abstract", …],          // header prefix keywords
//!     "portion"?: "timeslice" | "snapshot",
//!     "aliases"?: ["name", …],               // «alias» list
//!     "parent"?: <package node id>,
//!     "file"?, "line"?, "col"?,          // declaration site
//!     "lib"?: true,                       // library element (show_lib)
//!     "direction"?, "conjugated"?: true,  // ports
//!     "rows": [{ "id", "qname"?, "label", "inherited"?: true,
//!                "prefixes"?: [...], "detail"?: "ordered subsets x",
//!                "file"?, "line"?, "col"? }]
//!   }],
//!   "edges": [{ "kind": "composition" | "membership" | "typing" |
//!               "specialization" | "import" | "dependency" |
//!               "satisfy" | "verify" | "perform" | "exhibit" |
//!               "include" | "assert" | "frame" | "event" | "portion",
//!               "rel"?: "subclassification" | "subsetting" |
//!                       "redefinition" | "typing",   // specialization split
//!               "importKind"?: "membership" | "namespace" | "recursive",
//!               "visibility"?: "private" | "protected",   // imports
//!               "portionKind"?: "timeslice" | "snapshot",
//!               "sourcePath"?, "targetPath"?,  // projected feature paths
//!               "sourceRole"?, "sourceMultiplicity"?,   // connector ends
//!               "targetRole"?, "targetMultiplicity"?,
//!               "sourceAdornments"?, "targetAdornments"?: ["ordered", …],
//!               "source", "target" }]
//! }
//! ```
//!
//! Summary emission ([`VizOptions::summary`], tree view): a container
//! (a package, or an owner card with drawn members) outside the open
//! set is one node whose subtree is hidden, carrying
//! `"summary": { "open": false, "members", "containers", "leaves",
//! "notes", "hidden", "truncated", "edgesIn", "edgesOut" }` — `notes`
//! counts the notes on hidden elements below it and `hidden` the hidden
//! drawable elements below it (the cards the full picture would add); an open container carries the
//! same object with `"open": true` and `truncated` = direct members
//! beyond the leaf budget (hidden and counted like a closed one's).
//! Every reference edge with an endpoint that stands in for a hidden
//! element is a bundle `{ "kind", "source", "target", "count" }` with no
//! identity; edges between drawn nodes keep their shape. Notes beyond
//! the per-cluster budget fold into `"noteCount"` on their target (a
//! container's own overflow, distinct from `summary.notes` below it).

use std::collections::{HashMap, HashSet};

use serde_json::{Value as Json, json};
use sysmlv2_model::json::{ElementRef, ResolvedModel};

use crate::behavior::{ACTIONS, CONTROL_NODES, FLOWS, STATES, node_label, transition_edge_label};
use crate::interconnect::{BLOCK_USAGES, CONNECTORS, KERML_BLOCKS};
use crate::{Kind, SummaryOptions, View, VizOptions, classify, roots_of, stereotype, usage_label};

/// Why [`graph`] drew nothing.
#[derive(Clone, PartialEq, Eq, Debug)]
#[non_exhaustive]
pub enum GraphError {
    /// The view has no structured-graph emitter yet; it is reachable
    /// through [`crate::plantuml`].
    UnsupportedView(View),
}

impl std::fmt::Display for GraphError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            GraphError::UnsupportedView(view) => {
                write!(f, "no structured-graph emitter for view: {view}")
            }
        }
    }
}

impl std::error::Error for GraphError {}

/// Emit the structured graph for a view. Tree, interconnection, state
/// and action so far — other views stay on the PlantUML path until they
/// grow native renderers.
pub fn graph(
    r: &mut ResolvedModel,
    root: Option<ElementRef>,
    opts: &VizOptions,
) -> Result<Json, GraphError> {
    let tops = roots_of(r, root, opts);
    let mut aliases: HashMap<ElementRef, Vec<String>> = HashMap::new();
    for (name, target) in r.alias_members() {
        aliases.entry(target).or_default().push(name);
    }
    match opts.view {
        View::Tree => {
            let notes = if opts.show_notes || opts.summary.is_some() {
                r.annotation_notes()
            } else {
                Vec::new()
            };
            let summary = opts.summary.as_ref().map(|s| SummaryState::new(&notes, s));
            let mut g = GraphEmitter {
                r,
                opts,
                aliases,
                nodes: Vec::new(),
                edges: Vec::new(),
                drawn: HashMap::new(),
                rendered: Vec::new(),
                summary,
            };
            for e in tops {
                g.render(e, None);
            }
            g.reference_edges();
            let note_budget = g.summary.as_ref().map(|s| s.note_budget);
            emit_note_nodes(
                g.r,
                opts,
                notes,
                &g.drawn,
                &mut g.nodes,
                &mut g.edges,
                note_budget,
            );
            g.finish_summary();
            Ok(json!({ "view": opts.view.as_str(), "nodes": g.nodes, "edges": g.edges }))
        }
        View::Interconnection => {
            let mut g = IcGraphEmitter {
                r,
                opts,
                aliases,
                nodes: Vec::new(),
                edges: Vec::new(),
                drawn: HashMap::new(),
                typed_port: HashMap::new(),
                connectors: Vec::new(),
                content: HashMap::new(),
            };
            for e in tops {
                g.render(e, None);
            }
            g.connector_edges();
            let notes = if opts.show_notes {
                g.r.annotation_notes()
            } else {
                Vec::new()
            };
            emit_note_nodes(g.r, opts, notes, &g.drawn, &mut g.nodes, &mut g.edges, None);
            Ok(json!({ "view": opts.view.as_str(), "nodes": g.nodes, "edges": g.edges }))
        }
        View::State | View::Action => {
            let mut g = BehaviorGraphEmitter {
                r,
                view: opts.view,
                nodes: Vec::new(),
                edges: Vec::new(),
                drawn: HashMap::new(),
                edge_members: Vec::new(),
                pseudo: HashMap::new(),
            };
            for e in tops {
                g.collect(e, None);
            }
            g.emit_edges();
            Ok(json!({ "view": opts.view.as_str(), "nodes": g.nodes, "edges": g.edges }))
        }
        view => Err(GraphError::UnsupportedView(view)),
    }
}

/// Note nodes + attachment edges for every doc/comment body whose
/// annotated element is on the diagram — the graph twin of
/// [`crate::emit_notes`]. A note carries its annotation element's
/// identity (selectable, source-navigable); its edge is the structural
/// kind `note`.
fn emit_note_nodes(
    r: &mut ResolvedModel,
    opts: &VizOptions,
    notes: Vec<(ElementRef, ElementRef, Option<String>, String)>,
    drawn: &HashMap<ElementRef, String>,
    nodes: &mut Vec<Json>,
    edges: &mut Vec<Json>,
    note_budget: Option<usize>,
) {
    if !opts.show_notes {
        return;
    }
    // Node id → FIRST position with that id (overlapping roots emit an
    // element twice; the note keeps following the first, as the linear
    // search did), for the parent lookup and the folded-count patch
    // under a budget.
    let mut index: HashMap<String, usize> = HashMap::new();
    for (i, n) in nodes.iter().enumerate() {
        if let Some(id) = n["id"].as_str() {
            index.entry(id.to_string()).or_insert(i);
        }
    }
    let mut per_cluster: HashMap<String, usize> = HashMap::new();
    for (note, target, name, body) in notes {
        let Some(target_id) = drawn.get(&target) else {
            continue;
        };
        // The note joins its target's cluster (package box) so layout
        // keeps them together; the target itself may be a cluster.
        let parent = index
            .get(target_id)
            .and_then(|&i| nodes[i]["parent"].as_str())
            .map(str::to_string);
        if let Some(budget) = note_budget {
            // Notes beyond the per-cluster budget fold into a count on
            // their target instead of a card each.
            let slot = per_cluster
                .entry(parent.clone().unwrap_or_default())
                .or_insert(0);
            if *slot >= budget {
                if let Some(&i) = index.get(target_id) {
                    let count = nodes[i]["noteCount"].as_u64().unwrap_or(0) + 1;
                    nodes[i]["noteCount"] = json!(count);
                }
                continue;
            }
            *slot += 1;
        }
        let id = r.element_id(note).to_string();
        let mut obj = serde_json::Map::new();
        obj.insert("id".into(), json!(id));
        if let Some(parent) = parent {
            obj.insert("parent".into(), json!(parent));
        }
        if let Some(qn) = r.element_qualified_name(note) {
            obj.insert("qname".into(), json!(qn));
        }
        if let Some((file, line, col)) = r.declaration_position(note) {
            let file = file.to_string();
            obj.insert("file".into(), json!(file));
            obj.insert("line".into(), json!(line));
            obj.insert("col".into(), json!(col));
        }
        let stereo = match r.element_type(note) {
            "Documentation" => "doc",
            _ => "comment",
        };
        obj.insert(
            "label".into(),
            json!(sysmlv2_model::json::doc_display_text(&body)),
        );
        obj.insert(
            "stereo".into(),
            json!(name.unwrap_or_else(|| stereo.to_string())),
        );
        obj.insert("metaclass".into(), json!(r.element_type(note)));
        obj.insert("kind".into(), json!("note"));
        obj.insert("rows".into(), json!([]));
        nodes.push(Json::Object(obj));
        edges.push(json!({ "kind": "note", "source": id, "target": target_id }));
    }
}

struct GraphEmitter<'a> {
    r: &'a mut ResolvedModel,
    opts: &'a VizOptions,
    /// Element → its `alias … for` names (user units).
    aliases: HashMap<ElementRef, Vec<String>>,
    nodes: Vec<Json>,
    edges: Vec<Json>,
    /// Element → node id, for every element drawn as a node.
    drawn: HashMap<ElementRef, String>,
    /// Node-rendered elements (usage-likeness), for the second pass.
    rendered: Vec<(ElementRef, bool)>,
    /// Summary-mode bookkeeping (large scopes); `None` is the full emission.
    summary: Option<SummaryState>,
}

/// Counts a container node carries in summary mode.
#[derive(Clone, Debug, Default)]
struct SummaryCounts {
    open: bool,
    members: usize,
    containers: usize,
    leaves: usize,
    notes: usize,
    /// Drawable elements hidden below the container, at every depth.
    hidden: usize,
    truncated: usize,
    edges_in: usize,
    edges_out: usize,
}

/// Summary-mode state of the tree emitter (see [`SummaryOptions`]).
struct SummaryState {
    open: HashSet<ElementRef>,
    /// Open containers whose members all draw, whatever the leaf budget.
    unbounded: HashSet<ElementRef>,
    note_budget: usize,
    leaf_budget: usize,
    /// Notes per annotated element, for the counts under closed containers.
    notes_by_target: HashMap<ElementRef, usize>,
    /// Hidden element → id of the emitted container standing in for it.
    hidden: HashMap<ElementRef, String>,
    /// Hidden elements in walk order with their usage-likeness, for the
    /// reference pass that aggregates their edges onto the container.
    hidden_order: Vec<(ElementRef, bool)>,
    /// Container node id → its counts, patched onto the node at the end.
    counts: HashMap<String, SummaryCounts>,
    /// Reference edges with a hidden end: (source node, target node,
    /// kind), bundled with a count by [`GraphEmitter::finish_summary`].
    bundle: Vec<(String, String, String)>,
}

impl SummaryState {
    fn new(
        notes: &[(ElementRef, ElementRef, Option<String>, String)],
        opts: &SummaryOptions,
    ) -> SummaryState {
        let mut notes_by_target: HashMap<ElementRef, usize> = HashMap::new();
        for (_, target, _, _) in notes {
            *notes_by_target.entry(*target).or_insert(0) += 1;
        }
        SummaryState {
            open: opts.open.iter().copied().collect(),
            unbounded: opts.unbounded.iter().copied().collect(),
            note_budget: opts.note_budget,
            leaf_budget: opts.leaf_budget,
            notes_by_target,
            hidden: HashMap::new(),
            hidden_order: Vec::new(),
            counts: HashMap::new(),
            bundle: Vec::new(),
        }
    }
}

impl GraphEmitter<'_> {
    /// Members of `e` that would draw as nodes: everything but metadata
    /// and skipped kinds; on a non-package, compartment lines are rows,
    /// not members.
    fn drawable_children(&mut self, e: ElementRef, is_package: bool) -> Vec<ElementRef> {
        // Enumerations draw their literals as rows and nothing else.
        if matches!(
            self.r.element_type(e),
            "EnumerationDefinition" | "EnumerationUsage"
        ) {
            return Vec::new();
        }
        let metas = self.r.metadata_of(e);
        let mut out = Vec::new();
        for m in self.r.owned_members(e) {
            if metas.contains(&m) {
                continue;
            }
            match classify(self.r, self.opts.show_metadata, m) {
                Kind::Skip => {}
                Kind::Line if !is_package => {}
                _ => out.push(m),
            }
        }
        out
    }

    /// Hide `e` and its drawable subtree under the container `cid`:
    /// every hidden element maps to the container for the reference
    /// pass, and the notes below it join the container's count. Returns
    /// how many drawable members `e` has (nonzero: a container).
    fn hide_subtree(&mut self, e: ElementRef, cid: &str, counts: &mut SummaryCounts) -> usize {
        let kind = classify(self.r, self.opts.show_metadata, e);
        let is_usage = matches!(kind, Kind::UsageNode | Kind::Line);
        let is_package = matches!(kind, Kind::Package);
        let notes = self
            .summary
            .as_ref()
            .and_then(|s| s.notes_by_target.get(&e).copied())
            .unwrap_or(0);
        counts.notes += notes;
        counts.hidden += 1;
        if let Some(s) = self.summary.as_mut() {
            // Overlapping roots reach an element twice; its references
            // bundle once.
            if s.hidden.insert(e, cid.to_string()).is_none() {
                s.hidden_order.push((e, is_usage));
            }
        }
        let children = self.drawable_children(e, is_package);
        let n = children.len();
        for c in children {
            self.hide_subtree(c, cid, counts);
        }
        n
    }

    /// Summary mode: emit the members of container `id` (element `e`)
    /// — closed: every member hidden and counted; open: members drawn
    /// up to the leaf budget, the rest hidden and counted as truncated.
    /// Returns false when not in summary mode (the caller draws as
    /// usual).
    fn summary_members(&mut self, e: ElementRef, id: &str, is_package: bool) -> bool {
        let Some(open) = self.summary.as_ref().map(|s| s.open.contains(&e)) else {
            return false;
        };
        let children = self.drawable_children(e, is_package);
        // An empty package is a leaf, not an openable box.
        if !children.is_empty() {
            self.summary_children(e, id, open, children, Some(id));
        }
        true
    }

    /// Summary mode: draw or hide the drawable `children` of the
    /// container `id` and record its counts. Open: members draw (as
    /// `parent`'s children) up to the leaf budget, the rest hide as
    /// `truncated`; closed: everything hides. A drawn member is a
    /// container when it recorded counts of its own; a hidden one when
    /// it had drawable members. Returns the members that drew.
    fn summary_children(
        &mut self,
        e: ElementRef,
        id: &str,
        open: bool,
        children: Vec<ElementRef>,
        parent: Option<&str>,
    ) -> Vec<ElementRef> {
        // An unbounded container (the per-container override) draws
        // every member; the rest share the leaf budget.
        let leaf_budget = self.summary.as_ref().map_or(usize::MAX, |s| {
            if s.unbounded.contains(&e) {
                usize::MAX
            } else {
                s.leaf_budget
            }
        });
        let mut counts = SummaryCounts {
            open,
            ..SummaryCounts::default()
        };
        let mut emitted = 0usize;
        let mut drawn = Vec::new();
        for c in children {
            counts.members += 1;
            if open && emitted < leaf_budget {
                self.render(c, parent);
                emitted += 1;
                drawn.push(c);
                let container = self.drawn.get(&c).is_some_and(|cid| {
                    self.summary
                        .as_ref()
                        .is_some_and(|s| s.counts.contains_key(cid))
                });
                if container {
                    counts.containers += 1;
                } else {
                    counts.leaves += 1;
                }
            } else {
                if open {
                    counts.truncated += 1;
                }
                if self.hide_subtree(c, id, &mut counts) > 0 {
                    counts.containers += 1;
                } else {
                    counts.leaves += 1;
                }
            }
        }
        if let Some(s) = self.summary.as_mut() {
            s.counts.insert(id.to_string(), counts);
        }
        drawn
    }

    /// The emitted node an element resolves to: its own node when drawn
    /// (`false`), else (summary mode) the container standing in for it
    /// (`true` — an edge to it is a bundle, not a relationship).
    fn visible_id(&self, e: ElementRef) -> Option<(String, bool)> {
        if let Some(id) = self.drawn.get(&e) {
            return Some((id.clone(), false));
        }
        self.summary
            .as_ref()
            .and_then(|s| s.hidden.get(&e).map(|id| (id.clone(), true)))
    }

    /// A reference edge: as itself between drawn nodes, or — when either
    /// end stands in for hidden elements — counted into the bundle
    /// between the two container nodes (summary mode only).
    fn emit_ref(&mut self, remapped: bool, src: &str, tgt: &str, kind: &str, edge: Json) {
        if remapped {
            if let Some(s) = self.summary.as_mut() {
                s.bundle
                    .push((src.to_string(), tgt.to_string(), kind.to_string()));
            }
        } else {
            self.edges.push(edge);
        }
    }

    /// Summary mode, after every edge is in: edges touching a container
    /// node collapse to one per (source, target, kind) with a `count`
    /// (identity dropped — a bundle is not one relationship), self-loops
    /// on a container vanish, the counts land on the container nodes.
    fn finish_summary(&mut self) {
        let Some(s) = self.summary.as_mut() else {
            return;
        };
        let mut aggregated: Vec<((String, String, String), usize)> = Vec::new();
        let mut slot: HashMap<(String, String, String), usize> = HashMap::new();
        for key in s.bundle.drain(..) {
            // Both ends inside one container: interior, not a bundle.
            if key.0 == key.1 {
                continue;
            }
            match slot.get(&key) {
                Some(&i) => aggregated[i].1 += 1,
                None => {
                    slot.insert(key.clone(), aggregated.len());
                    aggregated.push((key, 1));
                }
            }
        }
        for ((src, tgt, kind), count) in aggregated {
            if let Some(c) = s.counts.get_mut(&src) {
                c.edges_out += count;
            }
            if let Some(c) = s.counts.get_mut(&tgt) {
                c.edges_in += count;
            }
            self.edges
                .push(json!({ "kind": kind, "source": src, "target": tgt, "count": count }));
        }
        for n in self.nodes.iter_mut() {
            let Some(id) = n["id"].as_str() else {
                continue;
            };
            let Some(c) = s.counts.get(id) else {
                continue;
            };
            n["summary"] = json!({
                "open": c.open,
                "members": c.members,
                "containers": c.containers,
                "leaves": c.leaves,
                "notes": c.notes,
                "hidden": c.hidden,
                "truncated": c.truncated,
                "edgesIn": c.edges_in,
                "edgesOut": c.edges_out,
            });
        }
    }

    fn id_of(&self, e: ElementRef) -> String {
        self.r.element_id(e).to_string()
    }

    /// Identity + declaration-site fields shared by nodes and rows.
    fn identity(&mut self, e: ElementRef) -> serde_json::Map<String, Json> {
        let mut m = serde_json::Map::new();
        m.insert("id".into(), json!(self.id_of(e)));
        if let Some(qn) = self.r.element_qualified_name(e) {
            m.insert("qname".into(), json!(qn));
        }
        if let Some((file, line, col)) = self.r.declaration_position(e) {
            let file = file.to_string();
            m.insert("file".into(), json!(file));
            m.insert("line".into(), json!(line));
            m.insert("col".into(), json!(col));
        }
        m
    }

    fn value_suffix(&mut self, e: ElementRef) -> Option<String> {
        if !self.opts.show_values {
            return None;
        }
        crate::value_suffix(self.r, e)
    }

    fn row(&mut self, m: ElementRef, inherited: bool) -> Option<Json> {
        let mut label = usage_label(self.r, m);
        if let Some(value) = self.value_suffix(m) {
            label.push(' ');
            label.push_str(&value);
        }
        if label.trim().is_empty() {
            return None;
        }
        let mut section = section_of(self.r.element_type(m));
        // Directed features render their direction in the label, and
        // directed reference rows (action parameters) group under one
        // "parameters" compartment instead of the generic references.
        if let Some(dir) = self.r.declared_direction(m) {
            let dir = dir.to_string();
            if section == "references" {
                section = "parameters".to_string();
            }
            label.insert(0, ' ');
            label.insert_str(0, &dir);
        }
        let mut obj = self.identity(m);
        obj.insert("label".into(), json!(label));
        obj.insert("section".into(), json!(section));
        if inherited {
            obj.insert("inherited".into(), json!(true));
        }
        let prefixes = self.r.prefix_keywords(m);
        if !prefixes.is_empty() {
            obj.insert("prefixes".into(), json!(prefixes));
        }
        // The notation's row tail: `ordered nonunique` properties and
        // written `subsets`/`redefines` clauses. An anonymous
        // redefining row already borrows the redefined name into its
        // label — no clause for those.
        let mut detail: Vec<String> = Vec::new();
        if self.r.is_ordered(m) {
            detail.push("ordered".into());
        }
        if !self.r.is_unique(m) {
            detail.push("nonunique".into());
        }
        if self.r.element_name(m).is_some() {
            for (kind, t) in self.r.explicit_specializations(m) {
                let word = match kind {
                    "Subsetting" => "subsets",
                    "Redefinition" => "redefines",
                    _ => continue,
                };
                let Some(n) = self.r.element_name(t).map(str::to_string) else {
                    continue;
                };
                detail.push(format!("{word} {n}"));
            }
        }
        if !detail.is_empty() {
            obj.insert("detail".into(), json!(detail.join(" ")));
        }
        Some(Json::Object(obj))
    }

    /// Rows + node children of `e` (the graph twin of the PlantUML
    /// emitter's member split, over the same [`classify`] verdicts).
    fn split_members(&mut self, e: ElementRef) -> (Vec<Json>, Vec<ElementRef>) {
        let mut rows = Vec::new();
        let mut children = Vec::new();
        let mut own_names: Vec<String> = Vec::new();
        let metas = self.r.metadata_of(e);
        for m in self.r.owned_members(e) {
            if metas.contains(&m) {
                continue;
            }
            match classify(self.r, self.opts.show_metadata, m) {
                Kind::Line => {
                    if let Some(n) = crate::display_name(self.r, m) {
                        own_names.push(n);
                    }
                    rows.extend(self.row(m, false));
                }
                Kind::Skip => {}
                _ => children.push(m),
            }
        }
        if self.opts.show_inherited {
            let mut supers = self.r.typings(e);
            for t in self.r.explicit_supertypes(e) {
                if !supers.contains(&t) {
                    supers.push(t);
                }
            }
            for t in supers {
                for m in self.r.owned_members(t) {
                    if !matches!(classify(self.r, self.opts.show_metadata, m), Kind::Line) {
                        continue;
                    }
                    let shadowed = self
                        .r
                        .element_name(m)
                        .is_some_and(|n| own_names.iter().any(|o| o == n));
                    if !shadowed {
                        rows.extend(self.row(m, true));
                    }
                }
            }
        }
        (rows, children)
    }

    fn render(&mut self, e: ElementRef, parent: Option<&str>) {
        match classify(self.r, self.opts.show_metadata, e) {
            Kind::Package => self.render_package(e, parent),
            Kind::TypeNode | Kind::EnumNode => self.render_node(e, parent, false),
            Kind::UsageNode | Kind::Line => self.render_node(e, parent, true),
            Kind::Skip => {}
        }
    }

    fn render_package(&mut self, e: ElementRef, parent: Option<&str>) {
        let id = self.id_of(e);
        let name = self.r.element_name(e).unwrap_or("(package)").to_string();
        let mut obj = self.identity(e);
        obj.insert("label".into(), json!(name));
        obj.insert("kind".into(), json!("package"));
        obj.insert("stereo".into(), json!("package"));
        obj.insert("metaclass".into(), json!(self.r.element_type(e)));
        if let Some(names) = self.aliases.get(&e) {
            obj.insert("aliases".into(), json!(names));
        }
        obj.insert("rows".into(), json!([]));
        if let Some(p) = parent {
            obj.insert("parent".into(), json!(p));
        }
        self.nodes.push(Json::Object(obj));
        self.drawn.insert(e, id.clone());
        self.rendered.push((e, false));
        if self.summary_members(e, &id, true) {
            return;
        }
        let metas = self.r.metadata_of(e);
        for m in self.r.owned_members(e) {
            if !metas.contains(&m) {
                self.render(m, Some(&id));
            }
        }
    }

    fn render_node(&mut self, e: ElementRef, parent: Option<&str>, is_usage: bool) {
        let id = self.id_of(e);
        let ty = self.r.element_type(e).to_string();
        let stereo = if ty == "EnumerationDefinition" {
            "enum def".to_string()
        } else {
            stereotype(&ty)
        };
        let label = if is_usage {
            usage_label(self.r, e)
        } else {
            self.r.element_name(e).unwrap_or("").to_string()
        };
        let mut label = if label.trim().is_empty() {
            format!("({stereo})")
        } else {
            label
        };
        // A usage drawn as its own node keeps the `= value` suffix its
        // compartment-row form would carry.
        if is_usage {
            if let Some(value) = self.value_suffix(e) {
                label.push(' ');
                label.push_str(&value);
            }
        }
        // Enum literals are rows; other nodes split their members. Both
        // enum spellings count: `enum def Phase` owns EnumerationUsage
        // literals, the usage form `enum Phase { … }` owns bare
        // ReferenceUsage members that play the same role.
        let enumish = ty == "EnumerationDefinition" || ty == "EnumerationUsage";
        let (rows, children) = if enumish {
            let mut lits = Vec::new();
            for m in self.r.owned_members(e) {
                let literal = self.r.is_enum_value(m)
                    || (ty == "EnumerationUsage" && self.r.element_type(m) == "ReferenceUsage");
                if !literal {
                    continue;
                }
                let Some(name) = self.r.element_name(m).map(str::to_string) else {
                    continue;
                };
                let mut obj = self.identity(m);
                obj.insert("label".into(), json!(name));
                obj.insert("section".into(), json!("literals"));
                lits.push(Json::Object(obj));
            }
            (lits, Vec::new())
        } else {
            self.split_members(e)
        };

        let mut obj = self.identity(e);
        obj.insert("label".into(), json!(label));
        obj.insert("kind".into(), json!(if enumish { "enum" } else { "node" }));
        obj.insert("stereo".into(), json!(stereo));
        obj.insert("metaclass".into(), json!(ty));
        notation_fields(self.r, &mut obj, e, is_usage);
        if let Some(names) = self.aliases.get(&e) {
            obj.insert("aliases".into(), json!(names));
        }
        obj.insert("rows".into(), Json::Array(rows));
        if let Some(p) = parent {
            obj.insert("parent".into(), json!(p));
        }
        self.nodes.push(Json::Object(obj));
        self.drawn.insert(e, id.clone());
        self.rendered.push((e, is_usage));

        // Summary mode: an owner card is a container — closed, its
        // members hide under it with counts; open, they draw as sibling
        // cards up to the budget. Ownership edges to drawn members are
        // emitted below for the open case.
        if !children.is_empty() && self.summary.is_some() {
            let open = self.summary.as_ref().is_some_and(|s| s.open.contains(&e));
            let drawn_children = self.summary_children(e, &id, open, children, parent);
            for child in drawn_children {
                self.ownership_edge(&id, child);
            }
            return;
        }

        for child in children {
            self.render(child, parent);
            self.ownership_edge(&id, child);
        }
    }

    /// The composition / membership edge from an owner card to a drawn
    /// member (nothing when the member did not draw).
    fn ownership_edge(&mut self, id: &str, child: ElementRef) {
        if let Some(child_id) = self.drawn.get(&child).cloned() {
            let kind = match classify(self.r, self.opts.show_metadata, child) {
                Kind::UsageNode | Kind::Line => "composition",
                _ => "membership",
            };
            let mut obj = serde_json::Map::new();
            obj.insert("kind".into(), json!(kind));
            obj.insert("source".into(), json!(id));
            obj.insert("target".into(), json!(child_id));
            // The notation splits composite (filled diamond) from
            // non-composite (hollow diamond) feature membership —
            // the graph twin of the PlantUML `*--` vs `o--` pick.
            if kind == "composition" && self.r.is_composite(child) == Some(false) {
                obj.insert("composite".into(), json!(false));
            }
            self.edges.push(Json::Object(obj));
        }
    }

    /// Second pass: typing / specialization / import edges between
    /// drawn nodes (plus on-demand library nodes under `show_lib`),
    /// «keyword» reference edges for the shorthand usages, and
    /// dependency edges. In summary mode the hidden elements take the
    /// same pass with their container as the source, and
    /// [`Self::finish_summary`] bundles what touches a container.
    fn reference_edges(&mut self) {
        // Collection is over, so the pass takes the list rather than
        // copying it to keep the emitter free to mutate.
        for (e, is_usage) in std::mem::take(&mut self.rendered) {
            let id = self.drawn[&e].clone();
            self.reference_edges_of(e, is_usage, &id, false);
        }
        let hidden: Vec<(ElementRef, bool, String)> = self
            .summary
            .as_ref()
            .map(|s| {
                s.hidden_order
                    .iter()
                    .map(|&(e, u)| (e, u, s.hidden[&e].clone()))
                    .collect()
            })
            .unwrap_or_default();
        for (e, is_usage, cid) in hidden {
            self.reference_edges_of(e, is_usage, &cid, true);
        }
        self.dependency_edges();
    }

    /// One element's reference edges from node `id` (`hidden`: the
    /// element stands behind a container, so every edge is a bundle).
    fn reference_edges_of(&mut self, e: ElementRef, is_usage: bool, id: &str, hidden: bool) {
        {
            let typings = if is_usage {
                self.r.typings(e)
            } else {
                Vec::new()
            };
            for target in &typings {
                if let Some((tid, remapped)) = self.target_id(*target) {
                    let edge = json!({ "kind": "typing", "source": id, "target": tid });
                    self.emit_ref(hidden || remapped, id, &tid, "typing", edge);
                }
            }
            // Kept under the umbrella kind "specialization" (consumer
            // compatibility); `rel` carries the notation's split.
            for (rel, target) in self.r.explicit_specializations(e) {
                if typings.contains(&target) {
                    continue;
                }
                // A timeslice/snapshot's subsetting is the notation's
                // portion-relationship, not a plain subsetting arrow.
                if rel == "Subsetting" {
                    if let Some(p) = self.r.portion_kind(e).map(str::to_string) {
                        if let Some((tid, remapped)) = self.target_id(target) {
                            let edge = json!({
                                "kind": "portion", "portionKind": p,
                                "directed": true,
                                "source": id, "target": tid,
                            });
                            self.emit_ref(hidden || remapped, id, &tid, "portion", edge);
                        }
                        continue;
                    }
                }
                let rel = match rel {
                    "Subclassification" => "subclassification",
                    "Subsetting" => "subsetting",
                    "Redefinition" => "redefinition",
                    "FeatureTyping" => "typing",
                    _ => continue,
                };
                if let Some((tid, remapped)) = self.target_id(target) {
                    let edge = json!({
                        "kind": "specialization", "rel": rel,
                        "source": id, "target": tid,
                    });
                    self.emit_ref(hidden || remapped, id, &tid, "specialization", edge);
                }
            }
            if self.opts.show_imported {
                for (target, is_ns, recursive, visibility) in self.r.import_details(e) {
                    if let Some((tid, remapped)) = self.visible_id(target) {
                        let import_kind = if recursive {
                            "recursive"
                        } else if is_ns {
                            "namespace"
                        } else {
                            "membership"
                        };
                        let mut obj = serde_json::Map::new();
                        obj.insert("kind".into(), json!("import"));
                        obj.insert("importKind".into(), json!(import_kind));
                        // «private import» spells the visibility inside
                        // the guillemets; public stays unspelled.
                        if visibility != "public" {
                            obj.insert("visibility".into(), json!(visibility));
                        }
                        obj.insert("source".into(), json!(id));
                        obj.insert("target".into(), json!(tid));
                        self.emit_ref(hidden || remapped, id, &tid, "import", Json::Object(obj));
                    }
                }
            }
            // «keyword» edges: the shorthand usage node → its referenced
            // target (satisfy-edge, perform-edge, …), carrying the
            // shorthand element's identity.
            let ty = self.r.element_type(e);
            if let Some(kind) = REF_EDGE_KINDS
                .iter()
                .find(|(t, _)| *t == ty)
                .map(|(_, k)| *k)
            {
                for chain in self.r.referenced_features(e) {
                    let Some((tid, remapped)) =
                        chain.iter().rev().find_map(|l| self.visible_id(*l))
                    else {
                        continue;
                    };
                    let mut obj = self.identity(e);
                    obj.insert("kind".into(), json!(kind));
                    obj.insert("metaclass".into(), json!(ty));
                    obj.insert("directed".into(), json!(true));
                    obj.insert("source".into(), json!(id));
                    obj.insert("target".into(), json!(tid));
                    self.emit_ref(hidden || remapped, id, &tid, kind, Json::Object(obj));
                }
            }
        }
    }

    /// Dependency elements between drawn nodes: one directed edge per
    /// client × supplier pair, carrying the dependency's identity.
    fn dependency_edges(&mut self) {
        for d in self.r.elements_of_metaclass("Dependency") {
            let (clients, suppliers) = self.r.dependency_ends(d);
            let mut base = self.identity(d);
            base.insert("kind".into(), json!("dependency"));
            base.insert("metaclass".into(), json!("Dependency"));
            base.insert("directed".into(), json!(true));
            if let Some(n) = self.r.element_name(d) {
                let n = n.to_string();
                base.insert("label".into(), json!(n));
            }
            for c in &clients {
                let Some((cid, rc)) = self.visible_id(*c) else {
                    continue;
                };
                for s in &suppliers {
                    let Some((sid, rs)) = self.visible_id(*s) else {
                        continue;
                    };
                    let mut obj = base.clone();
                    obj.insert("source".into(), json!(cid));
                    obj.insert("target".into(), json!(sid));
                    self.emit_ref(rc || rs, &cid, &sid, "dependency", Json::Object(obj));
                }
            }
        }
    }

    /// The node an edge target draws to: its node when rendered; under
    /// `show_lib`, an on-demand marked node for a library element.
    fn target_id(&mut self, target: ElementRef) -> Option<(String, bool)> {
        if let Some(hit) = self.visible_id(target) {
            return Some(hit);
        }
        if !self.opts.show_lib || !self.r.is_library_element(target) {
            return None;
        }
        let id = self.id_of(target);
        let ty = self.r.element_type(target).to_string();
        let label = self
            .r
            .element_qualified_name(target)
            .or_else(|| self.r.element_name(target).map(str::to_string))
            .unwrap_or_else(|| format!("({ty})"));
        let mut obj = self.identity(target);
        obj.insert("label".into(), json!(label));
        obj.insert("kind".into(), json!("node"));
        obj.insert("stereo".into(), json!(stereotype(&ty)));
        obj.insert("metaclass".into(), json!(ty));
        notation_fields(self.r, &mut obj, target, ty.ends_with("Usage"));
        obj.insert("lib".into(), json!(true));
        obj.insert("rows".into(), json!([]));
        self.nodes.push(Json::Object(obj));
        self.drawn.insert(target, id.clone());
        Some((id, false))
    }
}

// ---------------------------------------------------------------------------
// Interconnection view
// ---------------------------------------------------------------------------

/// The interconnection graph: blocks nest (parts inside parts inside
/// packages), ports are small child nodes — definition ports render
/// per usage under a synthetic `<usage-id>~<port-id>` node id, but
/// carry the definition port's identity for editing — and connector
/// members become **edges with element identity** (id, qname when
/// named, declaration span, kind), which is what makes an edge
/// selectable and deletable in a client.
struct IcGraphEmitter<'a> {
    r: &'a mut ResolvedModel,
    opts: &'a VizOptions,
    /// Element → its `alias … for` names (user units).
    aliases: HashMap<ElementRef, Vec<String>>,
    nodes: Vec<Json>,
    edges: Vec<Json>,
    drawn: HashMap<ElementRef, String>,
    typed_port: HashMap<(ElementRef, ElementRef), String>,
    connectors: Vec<ElementRef>,
    /// Memo of [`Self::has_content`] per element.
    content: HashMap<ElementRef, bool>,
}

enum IcKind {
    Package,
    Block { usage: bool },
    Port,
    Connector,
    Skip,
}

impl IcGraphEmitter<'_> {
    fn id_of(&self, e: ElementRef) -> String {
        self.r.element_id(e).to_string()
    }

    fn identity(&mut self, e: ElementRef) -> serde_json::Map<String, Json> {
        let mut m = serde_json::Map::new();
        m.insert("id".into(), json!(self.id_of(e)));
        if let Some(qn) = self.r.element_qualified_name(e) {
            m.insert("qname".into(), json!(qn));
        }
        if let Some((file, line, col)) = self.r.declaration_position(e) {
            let file = file.to_string();
            m.insert("file".into(), json!(file));
            m.insert("line".into(), json!(line));
            m.insert("col".into(), json!(col));
        }
        m
    }

    fn classify(&mut self, e: ElementRef) -> IcKind {
        let ty = self.r.element_type(e);
        if !self.opts.show_metadata && matches!(ty, "MetadataUsage" | "MetadataFeature") {
            return IcKind::Skip;
        }
        match ty {
            "Package" | "LibraryPackage" => IcKind::Package,
            "PortUsage" => IcKind::Port,
            _ if CONNECTORS.contains(&ty) => IcKind::Connector,
            _ if BLOCK_USAGES.contains(&ty) => IcKind::Block { usage: true },
            _ if (ty.ends_with("Definition") || KERML_BLOCKS.contains(&ty))
                && self.has_content(e) =>
            {
                IcKind::Block { usage: false }
            }
            _ => IcKind::Skip,
        }
    }

    /// Does `e`'s subtree contribute interconnection content? (The
    /// PlantUML emitter's gate, verbatim, memoized the same way.)
    fn has_content(&mut self, e: ElementRef) -> bool {
        if let Some(&known) = self.content.get(&e) {
            return known;
        }
        let mut found = false;
        for m in self.r.owned_members(e) {
            let ty = self.r.element_type(m);
            if ty == "PortUsage" || CONNECTORS.contains(&ty) || BLOCK_USAGES.contains(&ty) {
                found = true;
                break;
            }
            if (ty == "Package"
                || ty == "LibraryPackage"
                || ty.ends_with("Definition")
                || KERML_BLOCKS.contains(&ty))
                && self.has_content(m)
            {
                found = true;
                break;
            }
        }
        self.content.insert(e, found);
        found
    }

    fn render(&mut self, e: ElementRef, parent: Option<&str>) {
        match self.classify(e) {
            IcKind::Package => self.render_package(e, parent),
            IcKind::Block { usage } => self.render_block(e, parent, usage),
            IcKind::Port => self.render_port(e, parent, None),
            IcKind::Connector => self.connectors.push(e),
            IcKind::Skip => {}
        }
    }

    fn render_package(&mut self, e: ElementRef, parent: Option<&str>) {
        if !self.has_content(e) {
            return;
        }
        let id = self.id_of(e);
        let name = self.r.element_name(e).unwrap_or("(package)").to_string();
        let mut obj = self.identity(e);
        obj.insert("label".into(), json!(name));
        obj.insert("kind".into(), json!("package"));
        obj.insert("stereo".into(), json!("package"));
        obj.insert("metaclass".into(), json!(self.r.element_type(e)));
        if let Some(names) = self.aliases.get(&e) {
            obj.insert("aliases".into(), json!(names));
        }
        obj.insert("rows".into(), json!([]));
        if let Some(p) = parent {
            obj.insert("parent".into(), json!(p));
        }
        self.nodes.push(Json::Object(obj));
        self.drawn.insert(e, id.clone());
        let metas = self.r.metadata_of(e);
        for m in self.r.owned_members(e) {
            if !metas.contains(&m) {
                self.render(m, Some(&id));
            }
        }
    }

    fn render_block(&mut self, e: ElementRef, parent: Option<&str>, is_usage: bool) {
        let id = self.id_of(e);
        let ty = self.r.element_type(e).to_string();
        let stereo = stereotype(&ty);
        let label = if is_usage {
            usage_label(self.r, e)
        } else {
            self.r.element_name(e).unwrap_or("").to_string()
        };
        let label = if label.trim().is_empty() {
            format!("({stereo})")
        } else {
            label
        };
        let mut obj = self.identity(e);
        obj.insert("label".into(), json!(label));
        obj.insert("kind".into(), json!("block"));
        obj.insert("stereo".into(), json!(stereo));
        obj.insert("metaclass".into(), json!(ty));
        notation_fields(self.r, &mut obj, e, is_usage);
        if let Some(names) = self.aliases.get(&e) {
            obj.insert("aliases".into(), json!(names));
        }
        obj.insert("rows".into(), json!([]));
        if let Some(p) = parent {
            obj.insert("parent".into(), json!(p));
        }
        self.nodes.push(Json::Object(obj));
        self.drawn.insert(e, id.clone());

        let metas = self.r.metadata_of(e);
        for m in self.r.owned_members(e) {
            if metas.contains(&m) {
                continue;
            }
            match self.classify(m) {
                IcKind::Connector => self.connectors.push(m),
                IcKind::Port => self.render_port(m, Some(&id), None),
                IcKind::Skip => {}
                _ => self.render(m, Some(&id)),
            }
        }
        // Ports the usage inherits through its written heritage render on
        // the usage, shadowing applied (the resolver's own walk). Implied
        // bases stay out (every part inherits the standard library's
        // generic `ownedPorts` through its implied base), and so do the
        // library's abstract port usages reached by a written
        // `:> Parts::Part` — neither is structure the model declares. A
        // concrete port declared by a library definition the usage is
        // typed by still arrives.
        if is_usage {
            let inherited: Vec<ElementRef> = self
                .r
                .inherited_features(e, false)
                .into_iter()
                .filter(|&m| self.r.element_type(m) == "PortUsage")
                .filter(|&m| !(self.r.is_library_element(m) && self.r.is_abstract(m)))
                .collect();
            for p in inherited {
                self.render_port(p, Some(&id), Some(e));
            }
        }
    }

    /// One port node. `on` = the usage a definition port renders on —
    /// such a node gets a synthetic per-usage id but the definition
    /// port's identity fields (rename/reveal act on the definition).
    fn render_port(&mut self, p: ElementRef, parent: Option<&str>, on: Option<ElementRef>) {
        let node_id = match on {
            None => self.id_of(p),
            Some(usage) => {
                let id = format!("{}~{}", self.id_of(usage), self.id_of(p));
                self.typed_port.insert((usage, p), id.clone());
                id
            }
        };
        let label = usage_label(self.r, p);
        let label = if label.trim().is_empty() {
            "(port)".to_string()
        } else {
            label
        };
        let mut obj = self.identity(p);
        obj.insert("id".into(), json!(node_id));
        obj.insert("label".into(), json!(label));
        obj.insert("kind".into(), json!("port"));
        obj.insert("stereo".into(), json!("port"));
        obj.insert("metaclass".into(), json!("PortUsage"));
        notation_fields(self.r, &mut obj, p, true);
        if let Some(dir) = self.r.declared_direction(p) {
            let dir = dir.to_string();
            obj.insert("direction".into(), json!(dir));
        }
        let conjugated = self
            .r
            .typings(p)
            .iter()
            .any(|&t| self.r.element_type(t) == "ConjugatedPortDefinition");
        if conjugated {
            obj.insert("conjugated".into(), json!(true));
        }
        obj.insert("rows".into(), json!([]));
        if let Some(pa) = parent {
            obj.insert("parent".into(), json!(pa));
        }
        self.nodes.push(Json::Object(obj));
        if on.is_none() {
            self.drawn.insert(p, node_id);
        }
    }

    fn connector_edges(&mut self) {
        // Per resolved end — the notation places role, multiplicity,
        // and c-adornment keywords at each end.
        struct End {
            node: String,
            role: Option<String>,
            path: Option<String>,
            mult: Option<String>,
            adorn: Vec<String>,
        }
        for c in std::mem::take(&mut self.connectors) {
            let ends = self.r.connector_end_targets(c);
            let mut nodes: Vec<End> = Vec::new();
            for end in &ends {
                let projected = if end.spelling.is_none() {
                    crate::interconnect::project_end(
                        self.r,
                        &end.chain,
                        &self.drawn,
                        &self.typed_port,
                    )
                } else {
                    None
                };
                let Some((node, prefix)) = projected else {
                    nodes.clear();
                    break;
                };
                let path =
                    (prefix < end.chain.len()).then(|| crate::chain_label(self.r, &end.chain));
                let role = self
                    .r
                    .element_name(end.feature)
                    .filter(|n| !n.starts_with('$'))
                    .map(str::to_string);
                let mult = crate::multiplicity_suffix(self.r, end.feature);
                let adorn = end_adornments(self.r, end.feature);
                nodes.push(End {
                    node,
                    path,
                    role,
                    mult,
                    adorn,
                });
            }
            if nodes.len() < 2 {
                continue;
            }
            let ty = self.r.element_type(c).to_string();
            let is_flow = matches!(
                ty.as_str(),
                "FlowUsage" | "SuccessionFlowUsage" | "Flow" | "SuccessionFlow"
            );
            let kind = match ty.as_str() {
                _ if is_flow => "flow",
                "BindingConnectorAsUsage" | "BindingConnector" => "binding",
                "InterfaceUsage" => "interface",
                "AllocationUsage" => "allocation",
                _ => "connect",
            };
            let mut label_parts: Vec<String> = Vec::new();
            if let Some(n) = self.r.element_name(c) {
                label_parts.push(n.to_string());
            }
            if is_flow {
                if let Some(p) = crate::payload_label(self.r, c) {
                    label_parts.push(p);
                }
            }
            let label = label_parts.join(" ");
            let mut base = self.identity(c);
            base.insert("kind".into(), json!(kind));
            base.insert("metaclass".into(), json!(ty));
            if is_flow {
                base.insert("directed".into(), json!(true));
            }
            if !label.is_empty() {
                base.insert("label".into(), json!(label));
            }
            for w in nodes.windows(2) {
                let mut obj = base.clone();
                obj.insert("source".into(), json!(w[0].node));
                obj.insert("target".into(), json!(w[1].node));
                if let Some(path) = &w[0].path {
                    obj.insert("sourcePath".into(), json!(path));
                }
                if let Some(path) = &w[1].path {
                    obj.insert("targetPath".into(), json!(path));
                }
                if let Some(role) = &w[0].role {
                    obj.insert("sourceRole".into(), json!(role));
                }
                if let Some(mult) = &w[0].mult {
                    obj.insert("sourceMultiplicity".into(), json!(mult));
                }
                if let Some(role) = &w[1].role {
                    obj.insert("targetRole".into(), json!(role));
                }
                if let Some(mult) = &w[1].mult {
                    obj.insert("targetMultiplicity".into(), json!(mult));
                }
                if !w[0].adorn.is_empty() {
                    obj.insert("sourceAdornments".into(), json!(w[0].adorn));
                }
                if !w[1].adorn.is_empty() {
                    obj.insert("targetAdornments".into(), json!(w[1].adorn));
                }
                self.edges.push(Json::Object(obj));
            }
        }
    }
}

// ---------------------------------------------------------------------------
// State / action views
// ---------------------------------------------------------------------------

/// The behavior graphs: state/action-family elements as (nested)
/// nodes — control nodes marked for special shapes, state subactions
/// as rows with their own identity — plus `[*]` pseudostates as
/// per-scope synthetic nodes, and transitions / successions / flows as
/// edges carrying their element identity (a named transition is
/// renamable and deletable like any member).
struct BehaviorGraphEmitter<'a> {
    r: &'a mut ResolvedModel,
    view: View,
    nodes: Vec<Json>,
    edges: Vec<Json>,
    drawn: HashMap<ElementRef, String>,
    /// Edge members with the node id of their owning composite (edge
    /// resolution + pseudostate scoping happen after all nodes exist).
    edge_members: Vec<(ElementRef, Option<String>)>,
    /// (scope node id or "", initial?) → synthesized pseudostate id.
    pseudo: HashMap<(String, bool), String>,
}

impl BehaviorGraphEmitter<'_> {
    fn id_of(&self, e: ElementRef) -> String {
        self.r.element_id(e).to_string()
    }

    fn identity(&mut self, e: ElementRef) -> serde_json::Map<String, Json> {
        let mut m = serde_json::Map::new();
        m.insert("id".into(), json!(self.id_of(e)));
        if let Some(qn) = self.r.element_qualified_name(e) {
            m.insert("qname".into(), json!(qn));
        }
        if let Some((file, line, col)) = self.r.declaration_position(e) {
            let file = file.to_string();
            m.insert("file".into(), json!(file));
            m.insert("line".into(), json!(line));
            m.insert("col".into(), json!(col));
        }
        m
    }

    fn is_node(&self, ty: &str) -> bool {
        match self.view {
            View::State => STATES.contains(&ty),
            _ => ACTIONS.contains(&ty) || CONTROL_NODES.contains(&ty),
        }
    }

    fn is_edge(&self, ty: &str) -> bool {
        match self.view {
            View::State => {
                ty == "TransitionUsage" || ty == "SuccessionAsUsage" || ty == "Succession"
            }
            _ => ty == "SuccessionAsUsage" || ty == "Succession" || FLOWS.contains(&ty),
        }
    }

    /// Top-down search through transparent containers (packages,
    /// parts): view nodes render; stray edge members keep their scope.
    fn collect(&mut self, e: ElementRef, scope: Option<&str>) {
        let ty = self.r.element_type(e);
        if self.is_node(ty) {
            self.render_node(e, scope);
            return;
        }
        if self.is_edge(ty) {
            self.edge_members.push((e, scope.map(str::to_string)));
            return;
        }
        for m in self.r.owned_members(e) {
            self.collect(m, scope);
        }
    }

    fn render_node(&mut self, e: ElementRef, parent: Option<&str>) {
        let id = self.id_of(e);
        let ty = self.r.element_type(e).to_string();
        let control = CONTROL_NODES.contains(&ty.as_str());
        let stereo = match ty.as_str() {
            "ForkNode" => "fork".to_string(),
            "JoinNode" => "join".to_string(),
            "DecisionNode" | "MergeNode" => "choice".to_string(),
            _ => stereotype(&ty),
        };
        let is_def = ty.ends_with("Definition") || ty == "Behavior";
        let label = node_label(self.r, e, is_def);
        let label = if label.trim().is_empty() {
            format!("({stereo})")
        } else {
            label
        };

        // Subaction description lines (state view) become rows carrying
        // the subaction's identity.
        let mut rows: Vec<Json> = Vec::new();
        if self.view == View::State {
            for (kind, action) in self.r.state_subactions(e) {
                let l = node_label(self.r, action, false);
                if l.trim().is_empty() {
                    continue;
                }
                let mut obj = self.identity(action);
                obj.insert("label".into(), json!(format!("{kind} / {l}")));
                rows.push(Json::Object(obj));
            }
        }

        let mut obj = self.identity(e);
        obj.insert("label".into(), json!(label));
        obj.insert(
            "kind".into(),
            json!(if control { "control" } else { "state" }),
        );
        obj.insert("stereo".into(), json!(stereo));
        obj.insert("metaclass".into(), json!(ty));
        if !control {
            notation_fields(self.r, &mut obj, e, !is_def);
        }
        obj.insert("rows".into(), Json::Array(rows));
        if let Some(p) = parent {
            obj.insert("parent".into(), json!(p));
        }
        self.nodes.push(Json::Object(obj));
        self.drawn.insert(e, id.clone());

        for m in self.r.owned_members(e) {
            let mty = self.r.element_type(m);
            if self.is_node(mty) {
                self.render_node(m, Some(&id));
            } else if self.is_edge(mty) {
                self.edge_members.push((m, Some(id.clone())));
            }
        }
        // Directed parameters render as border chips on their action's
        // frame (the notation's param-l/r/t/b elements) — and being
        // drawn, they resolve as flow endpoints.
        if self.view == View::Action && !control {
            for m in self.r.owned_members(e) {
                let Some(dir) = self.r.declared_direction(m).map(str::to_string) else {
                    continue;
                };
                let mty = self.r.element_type(m).to_string();
                if self.is_node(&mty) || self.is_edge(&mty) {
                    continue;
                }
                let label = usage_label(self.r, m);
                if label.trim().is_empty() {
                    continue;
                }
                let param_id = self.id_of(m);
                let mut obj = self.identity(m);
                obj.insert("label".into(), json!(label));
                obj.insert("kind".into(), json!("param"));
                obj.insert("stereo".into(), json!("parameter"));
                obj.insert("metaclass".into(), json!(mty));
                obj.insert("direction".into(), json!(dir));
                obj.insert("rows".into(), json!([]));
                obj.insert("parent".into(), json!(id));
                self.nodes.push(Json::Object(obj));
                self.drawn.insert(m, param_id);
            }
        }
    }

    /// The id of the deepest rendered link of a feature chain.
    fn chain_node(&self, chain: &[ElementRef]) -> Option<String> {
        chain.iter().rev().find_map(|l| self.drawn.get(l).cloned())
    }

    /// The `[*]` pseudostate of a scope, synthesized on first use.
    fn pseudo_node(
        &mut self,
        scope: &Option<String>,
        initial: bool,
        owner: Option<ElementRef>,
    ) -> String {
        let body = owner
            .map(|e| self.id_of(e))
            .or_else(|| scope.clone())
            .unwrap_or_else(|| "root".to_string());
        let key = (body.clone(), initial);
        if let Some(id) = self.pseudo.get(&key) {
            return id.clone();
        }
        let id = format!("{}~{}", body, if initial { "initial" } else { "final" });
        let mut obj = serde_json::Map::new();
        obj.insert("id".into(), json!(id));
        obj.insert("label".into(), json!(""));
        obj.insert("kind".into(), json!("pseudo"));
        obj.insert(
            "stereo".into(),
            json!(if initial { "initial" } else { "final" }),
        );
        obj.insert("metaclass".into(), json!(""));
        obj.insert("rows".into(), json!([]));
        if let Some(p) = scope {
            obj.insert("parent".into(), json!(p));
        }
        self.nodes.push(Json::Object(obj));
        self.pseudo.insert(key, id.clone());
        id
    }

    fn emit_edges(&mut self) {
        // Collection is over, so the pass takes the list rather than
        // copying it to keep the emitter free to mutate.
        let edge_members = std::mem::take(&mut self.edge_members);
        let members: Vec<_> = edge_members.iter().map(|(e, _)| *e).collect();
        let contexts = crate::behavior::edge_contexts(self.r, &members, self.view);
        for (e, scope) in edge_members {
            let owner = self.r.owner(e);
            let ty = self.r.element_type(e).to_string();
            if ty == "TransitionUsage" {
                let parts = self.r.transition_parts(e);
                let (Some(src), Some(tgt)) = (
                    parts.source.and_then(|s| self.drawn.get(&s).cloned()),
                    parts.target.and_then(|t| self.drawn.get(&t).cloned()),
                ) else {
                    continue;
                };
                let label = transition_edge_label(self.r, &parts);
                let mut obj = self.identity(e);
                obj.insert("kind".into(), json!("transition"));
                obj.insert("metaclass".into(), json!(ty));
                obj.insert("directed".into(), json!(true));
                if !label.is_empty() {
                    obj.insert("label".into(), json!(label));
                }
                obj.insert("source".into(), json!(src));
                obj.insert("target".into(), json!(tgt));
                self.edges.push(Json::Object(obj));
                continue;
            }
            let is_flow = FLOWS.contains(&ty.as_str());
            let ends = self.r.connector_end_targets(e);
            if ends.len() < 2 {
                continue;
            }
            let pseudo_name = |r: &mut ResolvedModel,
                               end: &sysmlv2_model::json::ConnectorEndTarget|
             -> Option<bool> {
                let name = end
                    .chain
                    .last()
                    .and_then(|&l| r.element_name(l).map(str::to_string))
                    .or_else(|| end.spelling.clone());
                match name.as_deref() {
                    Some("start") => Some(true),
                    Some("done") => Some(false),
                    _ => None,
                }
            };
            let target_end = ends.last().cloned().expect("two ends checked");
            let inline_target =
                (!is_flow && target_end.chain.is_empty() && target_end.spelling.is_none())
                    .then(|| {
                        contexts
                            .get(&e)
                            .and_then(|c| c.target)
                            .and_then(|t| self.drawn.get(&t).cloned())
                    })
                    .flatten();
            let target = match self.chain_node(&target_end.chain).or(inline_target) {
                Some(t) => t,
                None => match pseudo_name(self.r, &target_end) {
                    Some(initial) => self.pseudo_node(&scope, initial, owner),
                    None => continue,
                },
            };
            let source_end = ends.first().cloned().expect("two ends checked");
            let source = if source_end.chain.is_empty() && source_end.spelling.is_none() {
                match contexts.get(&e).and_then(|c| c.source) {
                    Some(crate::behavior::FlowAnchor::Node(n)) => match self.drawn.get(&n) {
                        Some(id) => id.clone(),
                        None => continue,
                    },
                    Some(crate::behavior::FlowAnchor::Pseudo(initial)) => {
                        self.pseudo_node(&scope, initial, owner)
                    }
                    None => continue,
                }
            } else {
                match self.chain_node(&source_end.chain) {
                    Some(s) => s,
                    None => match pseudo_name(self.r, &source_end) {
                        Some(initial) => self.pseudo_node(&scope, initial, owner),
                        None => continue,
                    },
                }
            };
            let mut label = self.r.element_name(e).unwrap_or("").to_string();
            if is_flow && label.is_empty() {
                if let Some(p) = crate::payload_label(self.r, e) {
                    label = p;
                }
            }
            let mut obj = self.identity(e);
            obj.insert(
                "kind".into(),
                json!(if is_flow { "flow" } else { "succession" }),
            );
            obj.insert("metaclass".into(), json!(ty));
            obj.insert("directed".into(), json!(true));
            if !label.trim().is_empty() {
                obj.insert("label".into(), json!(label));
            }
            obj.insert("source".into(), json!(source));
            obj.insert("target".into(), json!(target));
            self.edges.push(Json::Object(obj));
        }
    }
}

/// Usage metaclasses that are referential by construction — their
/// non-composite default is not the notation's dashed "reference"
/// shape (which marks a declared `ref` on a composite-by-default
/// usage). `ReferenceUsage` itself IS the declared-`ref` spelling.
const REFERENTIAL_BY_NATURE: &[&str] = &[
    "AttributeUsage",
    "EnumerationUsage",
    "BindingConnectorAsUsage",
    "SuccessionAsUsage",
    "EventOccurrenceUsage",
    "ExhibitStateUsage",
    "IncludeUseCaseUsage",
    "PerformActionUsage",
];

/// The notation's shape triad for one node: definition (sharp rect),
/// usage (rounded), reference (dashed rounded).
fn node_kind_of(r: &mut ResolvedModel, e: ElementRef, is_usage: bool) -> &'static str {
    if !is_usage {
        return "def";
    }
    let ty = r.element_type(e);
    if ty == "ReferenceUsage" {
        return "ref";
    }
    if REFERENTIAL_BY_NATURE.contains(&ty) {
        return "usage";
    }
    if ty == "PortUsage" {
        // Ports are referential by default except as sub-ports, so only
        // nested ports can spell the dashed reference form (the spec
        // restricts dotted ports to nested ports for the same reason).
        let nested = r
            .owner(e)
            .is_some_and(|o| matches!(r.element_type(o), "PortDefinition" | "PortUsage"));
        if !nested {
            return "usage";
        }
    }
    // Non-composite reads as a declared `ref` only where the
    // composite-by-default rule applied — a featured usage with no
    // direction/`end` declaration (package-level usages are
    // unfeatured and non-composite by construction).
    if r.is_composite(e) == Some(false)
        && r.is_featured_usage(e) == Some(true)
        && r.declared_direction(e).is_none()
        && !r.prefix_keywords(e).contains(&"end")
    {
        "ref"
    } else {
        "usage"
    }
}

/// Insert the notation fields shared by every element node: the
/// def/usage/ref shape triad, header prefix keywords, and the
/// portion kind («timeslice»/«snapshot» headers).
fn notation_fields(
    r: &mut ResolvedModel,
    obj: &mut serde_json::Map<String, Json>,
    e: ElementRef,
    is_usage: bool,
) {
    obj.insert("nodeKind".into(), json!(node_kind_of(r, e, is_usage)));
    let mut prefixes = r.prefix_keywords(e);
    // Enumerations are variations by construction (their literals are
    // the variants) — the notation header spells just «enum def».
    if matches!(
        r.element_type(e),
        "EnumerationDefinition" | "EnumerationUsage"
    ) {
        prefixes.retain(|k| *k != "variation");
    }
    if !prefixes.is_empty() {
        obj.insert("prefixes".into(), json!(prefixes));
    }
    if let Some(p) = r.portion_kind(e).map(str::to_string) {
        obj.insert("portion".into(), json!(p));
    }
}

/// The notation's connector-end adornment keywords (`c-adornment`):
/// properties, direction, and written subsets/redefines.
fn end_adornments(r: &mut ResolvedModel, f: ElementRef) -> Vec<String> {
    let mut out: Vec<String> = Vec::new();
    if r.is_ordered(f) {
        out.push("ordered".into());
    }
    if !r.is_unique(f) {
        out.push("nonunique".into());
    }
    for k in r.prefix_keywords(f) {
        if matches!(k, "abstract" | "derived" | "constant") {
            out.push(k.into());
        }
    }
    if let Some(d) = r.declared_direction(f) {
        let d = d.to_string();
        out.push(d);
    }
    for (kind, t) in r.explicit_specializations(f) {
        let Some(name) = r.element_name(t).map(str::to_string) else {
            continue;
        };
        match kind {
            "Subsetting" => out.push(format!("subsets {name}")),
            "Redefinition" => out.push(format!("redefines {name}")),
            _ => {}
        }
    }
    out
}

/// Shorthand-usage metaclasses whose reference target renders as a
/// «keyword» edge (the notation's satisfy-edge, perform-edge, … —
/// graphical elaborations of the shorthand node's reference).
const REF_EDGE_KINDS: &[(&str, &str)] = &[
    ("SatisfyRequirementUsage", "satisfy"),
    ("RequirementVerificationUsage", "verify"),
    ("PerformActionUsage", "perform"),
    ("ExhibitStateUsage", "exhibit"),
    ("IncludeUseCaseUsage", "include"),
    ("AssertConstraintUsage", "assert"),
    ("FramedConcernUsage", "frame"),
    ("EventOccurrenceUsage", "event"),
];

/// A row's compartment heading, from its member's metaclass: the
/// standard families get their conventional plural names, everything
/// else derives one from the metaclass (`AllocationUsage` →
/// "allocations"), so no member renders without context.
fn section_of(metaclass: &str) -> String {
    match metaclass {
        "AttributeUsage" => "attributes".to_string(),
        "ReferenceUsage" => "references".to_string(),
        "ItemUsage" => "items".to_string(),
        "PartUsage" => "parts".to_string(),
        "PortUsage" => "ports".to_string(),
        "EnumerationUsage" => "literals".to_string(),
        "ConstraintUsage" | "AssertConstraintUsage" => "constraints".to_string(),
        "RequirementUsage" | "SatisfyRequirementUsage" => "requirements".to_string(),
        "ActionUsage" | "PerformActionUsage" => "actions".to_string(),
        "StateUsage" | "ExhibitStateUsage" => "states".to_string(),
        "CalculationUsage" => "calculations".to_string(),
        "Feature" => "features".to_string(),
        other => {
            let base = other
                .strip_suffix("Usage")
                .or_else(|| other.strip_suffix("Definition"))
                .unwrap_or(other);
            let mut s = String::new();
            for (i, c) in base.chars().enumerate() {
                if i == 0 {
                    s.extend(c.to_lowercase());
                } else {
                    s.push(c);
                }
            }
            s.push('s');
            s
        }
    }
}
