//! State and action views, in the PlantUML state-diagram
//! dialect (the one dialect that nests composites and draws control
//! pseudostates).
//!
//! The **state** view renders state definitions/usages as (composite)
//! `state` nodes, entry/do/exit subactions as description lines,
//! transitions as `-->` edges labelled `trigger [guard] / effect`, and
//! member successions — an empty source end (`entry; then S`) becomes
//! the `[*]` initial edge of its composite.
//!
//! The **action** view renders action-family usages as `state` nodes
//! (control nodes map to the built-in `<<fork>>`/`<<join>>`/`<<choice>>`
//! shapes), successions as solid edges, and flows as dashed edges
//! labelled with their payload.
//!
//! Everything else — packages, parts, non-view definitions — is a
//! transparent container: it renders nothing but its subtree is still
//! searched (`exhibit state` inside a part, a state def inside a
//! package). The state-diagram dialect has no `package` block, so
//! containers leave no trace.

use std::collections::HashMap;
use std::fmt::Write as _;

use sysmlv2_model::json::{BodyFlowMember, ElementRef, ResolvedModel};
use sysmlv2_syntax::ast::Dialect;

use crate::{View, VizOptions, chain_label, escape, frame, inline_label, stereotype, usage_label};

/// State-view node metaclasses.
pub(crate) const STATES: &[&str] = &["StateDefinition", "StateUsage", "ExhibitStateUsage"];

/// Action-view node metaclasses (control nodes are handled separately).
pub(crate) const ACTIONS: &[&str] = &[
    "ActionDefinition",
    "Behavior",
    "ActionUsage",
    "PerformActionUsage",
    "AcceptActionUsage",
    "SendActionUsage",
    "AssignmentActionUsage",
    "TerminateActionUsage",
    "IfActionUsage",
    "WhileLoopActionUsage",
    "ForLoopActionUsage",
    "Step",
];

pub(crate) const CONTROL_NODES: &[&str] = &["ForkNode", "JoinNode", "DecisionNode", "MergeNode"];

/// Flow metaclasses drawn as dashed edges in the action view.
pub(crate) const FLOWS: &[&str] = &["FlowUsage", "SuccessionFlowUsage", "Flow", "SuccessionFlow"];

pub(crate) fn emit(
    r: &mut ResolvedModel,
    tops: &[ElementRef],
    opts: &VizOptions,
    view: View,
) -> String {
    let mut em = Emitter {
        r,
        opts,
        view,
        alias: HashMap::new(),
        body: String::new(),
        edges: String::new(),
    };
    for &e in tops {
        em.collect(e);
    }
    let (body, edges) = (em.body, em.edges);
    let header = crate::style_header(opts, &["state"]);
    frame(opts, &header, &body, &edges)
}

struct Emitter<'a> {
    r: &'a mut ResolvedModel,
    opts: &'a VizOptions,
    view: View,
    alias: HashMap<ElementRef, String>,
    body: String,
    /// Edges outside any composite (from transparent containers).
    edges: String,
}

impl Emitter<'_> {
    fn alias_for(&mut self, e: ElementRef) -> String {
        if let Some(a) = self.alias.get(&e) {
            return a.clone();
        }
        let a = format!("n{}", self.alias.len() + 1);
        self.alias.insert(e, a.clone());
        a
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
            _ => {
                ty == "TransitionUsage"
                    || ty == "SuccessionAsUsage"
                    || ty == "Succession"
                    || FLOWS.contains(&ty)
            }
        }
    }

    /// Top-down search through transparent containers: view nodes
    /// render, stray edge members (in a container, outside any rendered
    /// node) go to the global edge buffer.
    fn collect(&mut self, e: ElementRef) {
        let ty = self.r.element_type(e);
        if self.is_node(ty) {
            self.render_node(e, 0);
            return;
        }
        if self.is_edge(ty) {
            let mut edges = String::new();
            self.emit_edge(e, 0, &mut edges);
            self.edges.push_str(&edges);
            return;
        }
        for m in self.r.owned_members(e) {
            self.collect(m);
        }
    }

    fn indent_into(buf: &mut String, depth: usize) {
        for _ in 0..depth {
            buf.push_str("  ");
        }
    }

    fn indent(&mut self, depth: usize) {
        Self::indent_into(&mut self.body, depth);
    }

    fn node_label(&mut self, e: ElementRef, is_def: bool) -> String {
        node_label(self.r, e, is_def)
    }

    fn node_stereotype(ty: &str) -> String {
        match ty {
            "ForkNode" => "fork".to_string(),
            "JoinNode" => "join".to_string(),
            "DecisionNode" | "MergeNode" => "choice".to_string(),
            _ => stereotype(ty),
        }
    }

    fn render_node(&mut self, e: ElementRef, depth: usize) {
        let alias = self.alias_for(e);
        let ty = self.r.element_type(e);
        let stereo = Self::node_stereotype(ty);
        let is_def = ty.ends_with("Definition") || ty == "Behavior";
        let label = self.node_label(e, is_def);
        let label = if label.trim().is_empty() {
            format!("({stereo})")
        } else {
            label
        };

        // Members in declaration order, with `first X;` markers
        // interleaved: the *flow anchor* tracks the last node member (or
        // the marked initial), so a bare `then x;` succession sources
        // from what precedes it, and an inline node declaration
        // (`then fork;`, `then action sum { … }`) resolves the pending
        // succession that introduced it. Successions never move the
        // anchor — consecutive `then`s after a fork all fan out from it.
        let flow = self.r.body_flow_members(e);
        let mut has_members = false;
        for fm in &flow {
            if let BodyFlowMember::Member(m) = fm {
                let mty = self.r.element_type(*m).to_string();
                if self.is_node(&mty) {
                    // Pre-register the alias so forward edge references
                    // (`then joinNode;` before `join joinNode;`) land.
                    self.alias_for(*m);
                    has_members = true;
                } else if self.is_edge(&mty) {
                    has_members = true;
                }
            }
        }

        let stereos = crate::stereo_text(self.r, self.opts, e, &stereo);
        let link = crate::link_suffix(self.r, self.opts, e);
        self.indent(depth);
        let _ = write!(
            self.body,
            "state \"{}\" as {alias} {stereos}{link}",
            escape(&label)
        );
        if !has_members {
            self.body.push('\n');
        } else {
            self.body.push_str(" {\n");
            let mut edges = String::new();
            let mut prev: Option<String> = None;
            let mut pending: Vec<(String, String)> = Vec::new();
            let mut last_transition_source: Option<ElementRef> = None;
            for fm in flow {
                match fm {
                    BodyFlowMember::Initial(elem, spell) => {
                        let name = elem
                            .and_then(|t| self.r.element_name(t).map(str::to_string))
                            .or(spell);
                        prev = match name.as_deref() {
                            Some("start" | "done") | None => None,
                            _ => elem.and_then(|t| self.alias.get(&t).cloned()),
                        };
                    }
                    BodyFlowMember::Member(m) => {
                        let mty = self.r.element_type(m).to_string();
                        if self.is_node(&mty) {
                            self.render_node(m, depth + 1);
                            let a = self.alias_for(m);
                            for (src, suffix) in pending.drain(..) {
                                Self::indent_into(&mut edges, depth + 1);
                                let _ = writeln!(edges, "{src} --> {a}{suffix}");
                            }
                            prev = Some(a);
                        } else if mty == "TransitionUsage" {
                            self.emit_transition_with(
                                m,
                                depth + 1,
                                &mut edges,
                                prev.as_deref(),
                                &mut last_transition_source,
                            );
                        } else if self.is_edge(&mty) {
                            self.emit_edge_with(
                                m,
                                depth + 1,
                                &mut edges,
                                prev.as_deref(),
                                Some(&mut pending),
                            );
                        }
                    }
                }
            }
            self.body.push_str(&edges);
            self.indent(depth);
            self.body.push_str("}\n");
        }

        if self.view == View::State {
            self.emit_subaction_lines(e, &alias, depth);
        }
    }

    /// `alias : entry / label` description lines, after the node. An
    /// anonymous subaction block (`do action { step1; step2; }`) lists
    /// its steps instead of disappearing.
    fn emit_subaction_lines(&mut self, e: ElementRef, alias: &str, depth: usize) {
        for (kind, action) in self.r.state_subactions(e) {
            let mut label = self.node_label(action, false);
            if label.trim().is_empty() {
                let mut steps: Vec<String> = Vec::new();
                for m in self.r.owned_members(action) {
                    let ty = self.r.element_type(m);
                    if !(ACTIONS.contains(&ty) || ty == "ReferenceUsage") {
                        continue;
                    }
                    let l = node_label(self.r, m, false);
                    if !l.trim().is_empty() {
                        steps.push(l);
                    }
                }
                label = steps.join("; ");
            }
            if label.trim().is_empty() {
                continue;
            }
            self.indent(depth);
            let _ = writeln!(self.body, "{alias} : {kind} / {}", inline_label(&label));
        }
    }

    /// The alias of the deepest rendered link of a feature chain.
    fn chain_alias(&self, chain: &[ElementRef]) -> Option<String> {
        chain
            .iter()
            .rev()
            .find_map(|link| self.alias.get(link).cloned())
    }

    /// Stray edges found outside any rendered node have no flow-order
    /// context: no anchor, inline-target successions dropped.
    fn emit_edge(&mut self, e: ElementRef, depth: usize, out: &mut String) {
        let ty = self.r.element_type(e).to_string();
        if ty == "TransitionUsage" {
            let mut last = None;
            self.emit_transition_with(e, depth, out, None, &mut last);
            return;
        }
        self.emit_edge_with(e, depth, out, None, None);
    }

    fn emit_edge_with(
        &mut self,
        e: ElementRef,
        depth: usize,
        out: &mut String,
        prev: Option<&str>,
        pending: Option<&mut Vec<(String, String)>>,
    ) {
        let ty = self.r.element_type(e);
        let is_flow = FLOWS.contains(&ty);
        let ends = self.r.connector_end_targets(e);
        if ends.len() < 2 {
            return;
        }
        // The library's `start`/`done` occurrence features are the
        // textual spellings of the initial/final pseudostates — matched
        // by resolved name or, without the library loaded, by the
        // written spelling of the unresolved end.
        let pseudo = |em: &mut Self, end: &sysmlv2_model::json::ConnectorEndTarget| {
            let name = end
                .chain
                .last()
                .and_then(|&l| em.r.element_name(l).map(str::to_string))
                .or_else(|| end.spelling.clone());
            name.filter(|n| n == "start" || n == "done")
                .map(|_| "[*]".to_string())
        };
        let source = match ends.first() {
            Some(end) if end.chain.is_empty() && end.spelling.is_none() => {
                // A bare source (`then x;`): the current flow anchor, or
                // the initial pseudostate when nothing precedes.
                Some(prev.unwrap_or("[*]").to_string())
            }
            Some(end) => self.chain_alias(&end.chain).or_else(|| pseudo(self, end)),
            None => None,
        };
        let Some(source) = source else { return };
        let arrow = if is_flow { "-[dashed]->" } else { "-->" };
        let mut label = self.r.element_name(e).unwrap_or("").to_string();
        if is_flow && label.is_empty() {
            if let Some(p) = crate::payload_label(self.r, e) {
                label = p;
            }
        }
        let suffix = if label.trim().is_empty() {
            String::new()
        } else {
            format!(" : {}", inline_label(&label))
        };
        let target_end = ends.last().cloned().expect("two ends checked above");
        let target = self
            .chain_alias(&target_end.chain)
            .or_else(|| pseudo(self, &target_end));
        let Some(target) = target else {
            // An inline node declaration follows (`then fork;`,
            // `then action sum { … }`): defer until it renders.
            if !is_flow && target_end.chain.is_empty() && target_end.spelling.is_none() {
                if let Some(pending) = pending {
                    pending.push((source, suffix));
                }
            }
            return;
        };
        Self::indent_into(out, depth);
        let _ = writeln!(out, "{source} {arrow} {target}{suffix}");
    }

    /// `src --> tgt : trigger [guard] / effect`. A transition with no
    /// spelled source (`else slow;`, a bare guarded shorthand) falls
    /// back to the previous transition's source, then the flow anchor —
    /// the `if g then a; else b;` idiom branches from one node.
    fn emit_transition_with(
        &mut self,
        e: ElementRef,
        depth: usize,
        out: &mut String,
        prev: Option<&str>,
        last_source: &mut Option<ElementRef>,
    ) {
        let parts = self.r.transition_parts(e);
        if parts.source.is_some() {
            *last_source = parts.source;
        }
        let source = parts
            .source
            .or(*last_source)
            .and_then(|s| self.alias.get(&s).cloned())
            .or_else(|| prev.map(str::to_string));
        let Some(source) = source else {
            return;
        };
        let Some(target) = parts.target.and_then(|t| self.alias.get(&t).cloned()) else {
            return;
        };
        let label = transition_edge_label(self.r, &parts);
        let suffix = if label.is_empty() {
            String::new()
        } else {
            format!(" : {label}")
        };
        Self::indent_into(out, depth);
        let _ = writeln!(out, "{source} --> {target}{suffix}");
    }
}

/// The node label: usage shape, falling back to the referenced
/// feature chain (`perform greet`, `exhibit s`).
pub(crate) fn node_label(r: &mut ResolvedModel, e: ElementRef, is_def: bool) -> String {
    let label = if is_def {
        r.element_name(e).unwrap_or("").to_string()
    } else {
        usage_label(r, e)
    };
    if !label.trim().is_empty() {
        return label;
    }
    for chain in r.referenced_features(e) {
        let l = chain_label(r, &chain);
        if !l.is_empty() {
            return l;
        }
    }
    String::new()
}

/// The accepted payload's type (or name): `accept Overheat` →
/// `Overheat`.
fn trigger_label(r: &mut ResolvedModel, trigger: ElementRef) -> Option<String> {
    let payload = r.owned_members(trigger).into_iter().find(|&m| {
        matches!(
            r.element_type(m),
            "ReferenceUsage" | "PayloadFeature" | "ItemUsage"
        )
    })?;
    let typings: Vec<String> = r
        .typings(payload)
        .into_iter()
        .filter_map(|t| r.element_name(t).map(str::to_string))
        .collect();
    if !typings.is_empty() {
        return Some(typings.join(", "));
    }
    r.element_name(payload).map(str::to_string)
}

fn effect_label(r: &mut ResolvedModel, effect: ElementRef) -> String {
    let label = node_label(r, effect, false);
    if !label.trim().is_empty() {
        return inline_label(&label);
    }
    // An anonymous effect still says what it does («send», …).
    stereotype(r.element_type(effect))
}

/// `trigger [guard] / effect` — the shared transition edge label.
pub(crate) fn transition_edge_label(
    r: &mut ResolvedModel,
    parts: &sysmlv2_model::json::TransitionParts,
) -> String {
    let mut pieces: Vec<String> = Vec::new();
    if let Some(trigger) = parts.trigger {
        if let Some(t) = trigger_label(r, trigger) {
            pieces.push(t);
        }
    }
    if let Some(guard) = &parts.guard {
        let text = sysmlv2_syntax::print::print_expr_source(guard, Dialect::Sysml);
        pieces.push(format!("[{}]", inline_label(&text)));
    }
    if let Some(effect) = parts.effect {
        let label = effect_label(r, effect);
        if !label.is_empty() {
            pieces.push(format!("/ {label}"));
        }
    }
    pieces.join(" ")
}
