//! Interconnection view and MIXED view: parts as nested
//! `rectangle` blocks with ports on their boundaries, connector-family
//! usages as edges between their resolved ends.
//!
//! Ports declared on a part's *definition* render on each usage box
//! (`connect tank.fuelOut to …` connects through the usage, so the
//! port must exist per usage) — those nodes are aliased by the
//! (usage, definition-port) pair. Connector ends resolve to the deepest
//! rendered link of their written feature chain; an end whose chain
//! never touches a rendered node drops its edge.
//!
//! **Interconnection** keeps the diagram structural: definitions render
//! only when they own interconnection content, and behavior members
//! leave no trace — a pure-definition model is the tree view's
//! business.
//!
//! **Mixed** puts everything on one canvas: every definition and usage
//! renders (states/actions as stereotyped rectangles, cases as
//! `usecase` nodes, actor members as `actor` nodes), and on top of the
//! connector edges it draws successions, transitions (labelled
//! `trigger [guard] / effect`), typing (`..>`) / specialization
//! (`--|>`) edges, and `«include»`/`«perform»`/`«exhibit»` reference
//! edges. Attribute-family members stay off both diagrams — the
//! component dialect has no compartments; the tree view carries them.

use std::collections::HashMap;
use std::fmt::Write as _;

use sysmlv2_model::json::{ElementRef, ResolvedModel};

use crate::{
    VizOptions, behavior, escape, frame, inline_label, link_suffix, stereo_text, stereotype,
    style_header, usage_label,
};

/// Connector-family metaclasses rendered as edges, not nodes.
pub(crate) const CONNECTORS: &[&str] = &[
    "ConnectionUsage",
    "InterfaceUsage",
    "AllocationUsage",
    "FlowUsage",
    "SuccessionFlowUsage",
    "BindingConnectorAsUsage",
    "Connector",
    "BindingConnector",
    "Flow",
    "SuccessionFlow",
];

/// Usage metaclasses rendered as `rectangle` blocks in both modes.
pub(crate) const BLOCK_USAGES: &[&str] = &[
    "PartUsage",
    "ItemUsage",
    "OccurrenceUsage",
    "ReferenceUsage",
    "Usage",
];

/// KerML classifier metaclasses that may own interconnection content.
pub(crate) const KERML_BLOCKS: &[&str] = &[
    "Classifier",
    "Class",
    "Structure",
    "AssociationStructure",
    "Association",
    "Behavior",
    "Function",
    "DataType",
    "Type",
];

/// Case-family metaclasses — `usecase` nodes in the mixed view.
const CASES: &[&str] = &[
    "UseCaseDefinition",
    "UseCaseUsage",
    "CaseDefinition",
    "CaseUsage",
    "AnalysisCaseDefinition",
    "AnalysisCaseUsage",
    "VerificationCaseDefinition",
    "VerificationCaseUsage",
];

/// Reference-edge usages: node plus a stereotyped `..>` to the target.
const REF_EDGES: &[(&str, &str)] = &[
    ("IncludeUseCaseUsage", "include"),
    ("PerformActionUsage", "perform"),
    ("ExhibitStateUsage", "exhibit"),
];

enum Kind {
    /// `package` block (rendered only when its subtree has content;
    /// mixed renders every package).
    Package,
    /// `rectangle` node; part-family usages (label = usage shape).
    Block,
    /// `rectangle` node; definitions (label = name; content-gated in
    /// the interconnection view).
    Def,
    /// `usecase` node (mixed only).
    Usecase,
    /// `port` / `portin` / `portout` on the owning block.
    Port,
    /// Edge between resolved ends.
    Connector,
    /// Succession/transition edge (mixed only).
    BehaviorEdge,
    Skip,
}

pub(crate) fn emit(
    r: &mut ResolvedModel,
    tops: &[ElementRef],
    opts: &VizOptions,
    mixed: bool,
) -> String {
    let mut em = Emitter {
        r,
        opts,
        mixed,
        alias: HashMap::new(),
        typed_port_alias: HashMap::new(),
        body: String::new(),
        edges: String::new(),
        connectors: Vec::new(),
        behavior_edges: Vec::new(),
        rendered: Vec::new(),
        content: HashMap::new(),
    };
    for &e in tops {
        em.render(e, 0);
    }
    em.emit_connector_edges();
    if mixed {
        em.emit_behavior_edges();
        em.emit_reference_edges();
    }
    let Emitter {
        r,
        alias,
        body,
        mut edges,
        ..
    } = em;
    crate::emit_notes(r, opts, &alias, &mut edges);
    let containers: &[&str] = if mixed {
        &["rectangle", "usecase"]
    } else {
        &["rectangle"]
    };
    let header = style_header(opts, containers);
    frame(opts, &header, &body, &edges)
}

struct Emitter<'a> {
    r: &'a mut ResolvedModel,
    opts: &'a VizOptions,
    mixed: bool,
    alias: HashMap<ElementRef, String>,
    /// Ports inherited from a usage's definition, aliased per
    /// (usage, definition port) — the same port renders on every usage
    /// of the definition.
    typed_port_alias: HashMap<(ElementRef, ElementRef), String>,
    body: String,
    edges: String,
    connectors: Vec<ElementRef>,
    /// Successions and transitions (mixed).
    behavior_edges: Vec<ElementRef>,
    /// Every node drawn (mixed reference-edge pass).
    rendered: Vec<ElementRef>,
    /// Memo of [`Self::has_content`] per element.
    content: HashMap<ElementRef, bool>,
}

impl Emitter<'_> {
    fn next_alias(&self) -> String {
        format!("n{}", self.alias.len() + self.typed_port_alias.len() + 1)
    }

    fn alias_for(&mut self, e: ElementRef) -> String {
        if let Some(a) = self.alias.get(&e) {
            return a.clone();
        }
        let a = self.next_alias();
        self.alias.insert(e, a.clone());
        a
    }

    fn classify(&mut self, e: ElementRef) -> Kind {
        let ty = self.r.element_type(e);
        if !self.opts.show_metadata && matches!(ty, "MetadataUsage" | "MetadataFeature") {
            return Kind::Skip;
        }
        match ty {
            "Package" | "LibraryPackage" => Kind::Package,
            "PortUsage" => Kind::Port,
            "SuccessionAsUsage" | "Succession" | "TransitionUsage" => {
                if self.mixed {
                    Kind::BehaviorEdge
                } else {
                    Kind::Skip
                }
            }
            _ if CONNECTORS.contains(&ty) => Kind::Connector,
            _ if BLOCK_USAGES.contains(&ty) => Kind::Block,
            _ if !self.mixed => {
                if (ty.ends_with("Definition") || KERML_BLOCKS.contains(&ty)) && self.has_content(e)
                {
                    Kind::Def
                } else {
                    Kind::Skip
                }
            }
            // Mixed: everything else definition- or usage-shaped joins
            // the canvas.
            _ if CASES.contains(&ty) => Kind::Usecase,
            "AttributeUsage" | "EnumerationUsage" => Kind::Skip,
            _ if ty.ends_with("Definition") || KERML_BLOCKS.contains(&ty) => Kind::Def,
            _ if ty.ends_with("Usage")
                || matches!(ty, "ForkNode" | "JoinNode" | "DecisionNode" | "MergeNode") =>
            {
                Kind::Block
            }
            _ => Kind::Skip,
        }
    }

    /// Does `e`'s subtree contribute interconnection content (a part,
    /// port, or connector)? Memoized: the gate runs from `classify` for
    /// every definition and again from `render_package`, so without the
    /// memo each subtree would be re-walked once per ancestor level.
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

    fn indent(&mut self, depth: usize) {
        for _ in 0..depth {
            self.body.push_str("  ");
        }
    }

    fn render(&mut self, e: ElementRef, depth: usize) {
        match self.classify(e) {
            Kind::Package => self.render_package(e, depth),
            Kind::Block => self.render_block(e, depth, true),
            Kind::Def => self.render_block(e, depth, false),
            Kind::Usecase => self.render_usecase(e, depth),
            // A port not nested in a rendered block still needs a node.
            Kind::Port => self.render_top_port(e, depth),
            Kind::Connector => self.connectors.push(e),
            Kind::BehaviorEdge => self.behavior_edges.push(e),
            Kind::Skip => {}
        }
    }

    fn render_package(&mut self, e: ElementRef, depth: usize) {
        if !self.mixed && !self.has_content(e) {
            return;
        }
        let alias = self.alias_for(e);
        let name = escape(self.r.element_name(e).unwrap_or("(package)"));
        let members = self.r.owned_members(e);
        let metas = self.r.metadata_of(e);
        self.indent(depth);
        let _ = writeln!(self.body, "package \"{name}\" as {alias} {{");
        for m in members {
            // Prefix metadata renders as the owner's stereotype.
            if metas.contains(&m) {
                continue;
            }
            self.render(m, depth + 1);
        }
        self.indent(depth);
        self.body.push_str("}\n");
        self.rendered.push(e);
    }

    /// The node keyword for a block: `rectangle` everywhere; actor
    /// members read better as PlantUML actors (mixed).
    fn block_keyword(&self, e: ElementRef) -> &'static str {
        if self.mixed && self.r.owning_membership_type(e) == Some("ActorMembership") {
            "actor"
        } else {
            "rectangle"
        }
    }

    fn render_block(&mut self, e: ElementRef, depth: usize, is_usage: bool) {
        let alias = self.alias_for(e);
        let ty = self.r.element_type(e);
        let stereo = stereotype(ty);
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

        // Ports and nested blocks go inside the braces; connectors and
        // behavior members are collected for the edge passes.
        let members = self.r.owned_members(e);
        let metas = self.r.metadata_of(e);
        let mut inner: Vec<ElementRef> = Vec::new();
        for m in members {
            if metas.contains(&m) {
                continue;
            }
            match self.classify(m) {
                Kind::Connector => self.connectors.push(m),
                Kind::BehaviorEdge => self.behavior_edges.push(m),
                Kind::Skip => {}
                _ => inner.push(m),
            }
        }
        // Ports declared on the usage's definition render on the usage.
        let inherited = if is_usage {
            self.inherited_ports(e)
        } else {
            Vec::new()
        };

        let keyword = self.block_keyword(e);
        let stereo = if keyword == "actor" {
            "actor".to_string()
        } else {
            stereo
        };
        let stereos = stereo_text(self.r, self.opts, e, &stereo);
        let link = link_suffix(self.r, self.opts, e);
        self.indent(depth);
        let _ = write!(
            self.body,
            "{keyword} \"{}\" as {alias} {stereos}{link}",
            escape(&label)
        );
        self.rendered.push(e);
        if inner.is_empty() && inherited.is_empty() {
            self.body.push('\n');
            return;
        }
        self.body.push_str(" {\n");
        for m in inner {
            match self.classify(m) {
                Kind::Port => self.render_port(m, None, depth + 1),
                _ => self.render(m, depth + 1),
            }
        }
        for p in inherited {
            self.render_port(p, Some(e), depth + 1);
        }
        self.indent(depth);
        self.body.push_str("}\n");
    }

    /// A case-family node (mixed): `usecase` cannot nest, so members
    /// render as siblings under a composition edge.
    fn render_usecase(&mut self, e: ElementRef, depth: usize) {
        let alias = self.alias_for(e);
        let ty = self.r.element_type(e);
        let stereo = stereotype(ty);
        let label = if ty.ends_with("Definition") {
            self.r.element_name(e).unwrap_or("").to_string()
        } else {
            usage_label(self.r, e)
        };
        let label = if label.trim().is_empty() {
            format!("({stereo})")
        } else {
            label
        };
        let stereos = stereo_text(self.r, self.opts, e, &stereo);
        let link = link_suffix(self.r, self.opts, e);
        self.indent(depth);
        let _ = writeln!(
            self.body,
            "usecase \"{}\" as {alias} {stereos}{link}",
            escape(&label)
        );
        self.rendered.push(e);
        for m in self.r.owned_members(e) {
            match self.classify(m) {
                Kind::Connector => self.connectors.push(m),
                Kind::BehaviorEdge => self.behavior_edges.push(m),
                Kind::Skip | Kind::Port => {}
                _ => {
                    self.render(m, depth);
                    if let Some(child_alias) = self.alias.get(&m).cloned() {
                        let _ = writeln!(self.edges, "{alias} *-- {child_alias}");
                    }
                }
            }
        }
    }

    /// Ports `e` inherits through its *written* heritage (typings and
    /// specializations, transitively), shadowing applied — the resolver's
    /// own walk ([`ResolvedModel::inherited_features`]). Two kinds stay
    /// out: implied bases (every part inherits the standard library's
    /// generic `ownedPorts` through its implied base), and the library's
    /// *abstract* port usages when a written `:> Parts::Part` reaches
    /// them — neither is structure the model declares. Concrete ports
    /// declared by a definition that happens to live in a loaded library
    /// still arrive, because the typing that reaches them is written.
    fn inherited_ports(&mut self, e: ElementRef) -> Vec<ElementRef> {
        self.r
            .inherited_features(e, false)
            .into_iter()
            .filter(|&m| self.r.element_type(m) == "PortUsage")
            .filter(|&m| !(self.r.is_library_element(m) && self.r.is_abstract(m)))
            .collect()
    }

    /// One port node. `on` is the usage box a definition port renders
    /// on (`None` for a port owned by the block itself).
    fn render_port(&mut self, p: ElementRef, on: Option<ElementRef>, depth: usize) {
        let alias = match on {
            None => self.alias_for(p),
            Some(owner) => {
                if let Some(a) = self.typed_port_alias.get(&(owner, p)) {
                    a.clone()
                } else {
                    let a = self.next_alias();
                    self.typed_port_alias.insert((owner, p), a.clone());
                    a
                }
            }
        };
        let keyword = match self.r.declared_direction(p) {
            Some("in") => "portin",
            Some("out") => "portout",
            _ => "port",
        };
        let label = usage_label(self.r, p);
        let label = if label.trim().is_empty() {
            "(port)".to_string()
        } else {
            label
        };
        self.indent(depth);
        let _ = writeln!(self.body, "{keyword} \"{}\" as {alias}", escape(&label));
        if on.is_none() {
            self.rendered.push(p);
        }
    }

    /// A top-level port (no owning block): PlantUML allows `port` only
    /// inside a block, so it becomes a stereotyped rectangle.
    fn render_top_port(&mut self, e: ElementRef, depth: usize) {
        let alias = self.alias_for(e);
        let label = usage_label(self.r, e);
        let label = if label.trim().is_empty() {
            "(port)".to_string()
        } else {
            label
        };
        let link = link_suffix(self.r, self.opts, e);
        self.indent(depth);
        let _ = writeln!(
            self.body,
            "rectangle \"{}\" as {alias} <<port>>{link}",
            escape(&label)
        );
        self.rendered.push(e);
    }

    fn end_alias(&mut self, chain: &[ElementRef]) -> Option<String> {
        project_end(self.r, chain, &self.alias, &self.typed_port_alias).map(|(id, _)| id)
    }

    fn emit_connector_edges(&mut self) {
        // Collection is over, so the pass takes the list rather than
        // copying it to keep the emitter free to mutate.
        for c in std::mem::take(&mut self.connectors) {
            let ends = self.r.connector_end_targets(c);
            let Some(aliases): Option<Vec<_>> = ends
                .iter()
                .map(|end| {
                    if end.spelling.is_some() {
                        return None;
                    }
                    project_end(self.r, &end.chain, &self.alias, &self.typed_port_alias)
                })
                .collect()
            else {
                continue;
            };
            if aliases.len() < 2 {
                continue;
            }
            let ty = self.r.element_type(c);
            let is_flow = matches!(
                ty,
                "FlowUsage" | "SuccessionFlowUsage" | "Flow" | "SuccessionFlow"
            );
            let (arrow, tag) = match ty {
                _ if is_flow => ("-->", None),
                "BindingConnectorAsUsage" | "BindingConnector" => ("..", Some("=")),
                "InterfaceUsage" => ("--", Some("«interface»")),
                "AllocationUsage" => ("..>", Some("«allocate»")),
                _ => ("--", None),
            };
            let mut parts: Vec<String> = Vec::new();
            if let Some(t) = tag {
                parts.push(t.to_string());
            }
            if let Some(n) = self.r.element_name(c) {
                parts.push(n.to_string());
            }
            if is_flow {
                if let Some(p) = crate::payload_label(self.r, c) {
                    parts.push(p);
                }
            }
            let label = parts.join(" ");
            let suffix = if label.is_empty() {
                String::new()
            } else {
                format!(" : {}", inline_label(&label))
            };
            for (at, w) in aliases.windows(2).enumerate() {
                let end_label = |at: usize, projected: &(String, usize)| {
                    if projected.1 < ends[at].chain.len() {
                        format!(
                            " \"{}\"",
                            escape(&crate::chain_label(self.r, &ends[at].chain))
                        )
                    } else {
                        String::new()
                    }
                };
                let source_label = end_label(at, &w[0]);
                let target_label = end_label(at + 1, &w[1]);
                let _ = writeln!(
                    self.edges,
                    "{}{source_label} {arrow}{target_label} {}{suffix}",
                    w[0].0, w[1].0
                );
            }
        }
    }

    /// Succession and transition edges (mixed). The component dialect
    /// has no `[*]` pseudostate, so unspelled ends drop their edge.
    fn emit_behavior_edges(&mut self) {
        for e in std::mem::take(&mut self.behavior_edges) {
            if self.r.element_type(e) == "TransitionUsage" {
                let parts = self.r.transition_parts(e);
                let (Some(src), Some(tgt)) = (
                    parts.source.and_then(|s| self.alias.get(&s).cloned()),
                    parts.target.and_then(|t| self.alias.get(&t).cloned()),
                ) else {
                    continue;
                };
                let label = behavior::transition_edge_label(self.r, &parts);
                let suffix = if label.is_empty() {
                    String::new()
                } else {
                    format!(" : {label}")
                };
                let _ = writeln!(self.edges, "{src} --> {tgt}{suffix}");
                continue;
            }
            let ends = self.r.connector_end_targets(e);
            if ends.len() < 2 {
                continue;
            }
            let (Some(src), Some(tgt)) = (
                ends.first().and_then(|end| self.end_alias(&end.chain)),
                ends.last().and_then(|end| self.end_alias(&end.chain)),
            ) else {
                continue;
            };
            let label = self.r.element_name(e).unwrap_or("").to_string();
            let suffix = if label.is_empty() {
                String::new()
            } else {
                format!(" : {}", inline_label(&label))
            };
            let _ = writeln!(self.edges, "{src} --> {tgt}{suffix}");
        }
    }

    /// Typing / specialization / stereotyped reference / import edges
    /// between rendered nodes (mixed).
    fn emit_reference_edges(&mut self) {
        for e in std::mem::take(&mut self.rendered) {
            let alias = self.alias[&e].clone();
            let ty = self.r.element_type(e);
            let is_usage = !ty.ends_with("Definition") && !KERML_BLOCKS.contains(&ty);
            let typings = if is_usage {
                self.r.typings(e)
            } else {
                Vec::new()
            };
            for target in &typings {
                if let Some(target_alias) = self.target_alias(*target) {
                    let _ = writeln!(self.edges, "{alias} ..> {target_alias}");
                }
            }
            for target in self.r.explicit_supertypes(e) {
                if typings.contains(&target) {
                    continue;
                }
                if let Some(target_alias) = self.target_alias(target) {
                    let _ = writeln!(self.edges, "{alias} --|> {target_alias}");
                }
            }
            if let Some((_, word)) = REF_EDGES.iter().find(|(t, _)| *t == ty) {
                for chain in self.r.referenced_features(e) {
                    if let Some(target_alias) =
                        chain.last().and_then(|t| self.alias.get(t).cloned())
                    {
                        let _ = writeln!(self.edges, "{alias} ..> {target_alias} : «{word}»");
                    }
                }
            }
            if self.opts.show_imported {
                for (target, _) in self.r.import_targets(e) {
                    if let Some(target_alias) = self.alias.get(&target).cloned() {
                        let _ = writeln!(self.edges, "{alias} ..> {target_alias} : «import»");
                    }
                }
            }
        }
    }

    /// The alias an edge target draws to: its node when rendered; under
    /// `show_lib`, an on-demand marked node for a library element.
    fn target_alias(&mut self, target: ElementRef) -> Option<String> {
        if let Some(a) = self.alias.get(&target) {
            return Some(a.clone());
        }
        if !self.opts.show_lib || !self.r.is_library_element(target) {
            return None;
        }
        let alias = self.alias_for(target);
        let name = self
            .r
            .element_name(target)
            .unwrap_or("(library)")
            .to_string();
        let stereo = stereotype(self.r.element_type(target));
        let _ = writeln!(
            self.body,
            "rectangle \"{}\" as {alias} <<{stereo}>> <<library>>",
            escape(&name)
        );
        Some(alias)
    }
}

/// Project a chain onto its deepest rendered occurrence. Crossing into a
/// type's member must not jump to that member's separate declaration box.
/// The returned prefix length lets callers retain the unrendered feature path.
pub(crate) fn project_end(
    r: &mut ResolvedModel,
    chain: &[ElementRef],
    drawn: &HashMap<ElementRef, String>,
    typed_ports: &HashMap<(ElementRef, ElementRef), String>,
) -> Option<(String, usize)> {
    let mut best = None;
    let mut context = None;
    for (i, &link) in chain.iter().enumerate() {
        if let Some(ctx) = context {
            if let Some(id) = typed_ports.get(&(ctx, link)) {
                // Per-usage port chips have no rendered descendants.
                return Some((id.clone(), i + 1));
            }
            if r.owner(link) != Some(ctx) {
                break;
            }
        }
        if let Some(id) = drawn.get(&link) {
            best = Some((id.clone(), i + 1));
        }
        context = Some(link);
    }
    best
}
