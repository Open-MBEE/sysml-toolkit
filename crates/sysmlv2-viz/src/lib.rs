//! PlantUML emission for SysML v2 / KerML models.
//!
//! Seven views over the resolved model, all deterministic (aliases in
//! declaration order) and all tolerant of unresolved references:
//!
//! - **Tree** (structure) — packages as `package` blocks,
//!   definitions and KerML classifiers as stereotyped `class` nodes,
//!   enum defs as `enum` nodes, usages as `name : Type [mult]` nodes
//!   under composition edges (attribute-family usages become
//!   compartment lines), plus specialization (`--|>`) and typing
//!   (`..>`) edges whenever both ends are on the diagram.
//! - **Interconnection** (`interconnect`) — parts as nested
//!   `rectangle` blocks with ports on their boundaries, and
//!   connector-family usages (connections, interfaces, bindings,
//!   allocations, flows) as edges between their resolved ends.
//! - **State** / **Action** (`behavior`) — state machines and
//!   action flows in the PlantUML state-diagram dialect: composite
//!   nodes, `[*]` entry, transitions labelled `trigger [guard] /
//!   effect`, successions, and dashed flow edges.
//! - **Sequence** (`sequence`) — lifelines for the parts that
//!   exchange messages, `->>` arrows for flow-family usages, ordered
//!   by the events' succession partial order.
//! - **Case** (`case`) — the use-case diagram: `usecase` nodes,
//!   actors, `<<subject>>` rectangles, objectives as notes,
//!   `«include»` edges.
//! - **Mixed** (`interconnect` with `mixed`) — everything on
//!   one canvas: structure, ports, connectors, behavior edges, cases,
//!   typing/specialization.
//!
//! Cross-view options ([`VizOptions`]): comment/doc bodies as
//! attached notes, prefix metadata as extra node stereotypes,
//! `^`-marked inherited compartment lines, referenced library types
//! as marked nodes, `«import»` edges, polyline/ortho routing, a
//! stereotype-keyed color palette, and `[[hyperlink]]` templates
//! (`{file}`/`{line}`/`{col}`/`{qname}`/`{id}`) carried into rendered
//! SVG.
//!
//! Library elements are never rendered as nodes by default (types
//! they provide still appear in labels); implied elements do not
//! exist in the resolved model's ownership walk, so nothing filters
//! them here.

mod behavior;
mod case;
mod graph;
mod interconnect;
mod sequence;

pub use graph::{GraphError, graph};

use std::collections::HashMap;
use std::fmt;
use std::fmt::Write as _;
use std::str::FromStr;

use serde::{Deserialize, Serialize};
use sysmlv2_model::eval::Value;
use sysmlv2_model::json::{ElementRef, ResolvedModel};

/// Diagram layout direction. PlantUML's default is top-to-bottom.
#[derive(Clone, Copy, PartialEq, Eq, Debug, Default)]
pub enum Direction {
    #[default]
    TopToBottom,
    LeftToRight,
}

/// Which diagram to emit (the Pilot Implementation's view repertoire).
///
/// The variants carry the spelling hosts use on a command line or in an
/// options object, through [`FromStr`], [`Display`](fmt::Display) and
/// serde:
///
/// ```
/// use sysmlv2_viz::View;
///
/// assert_eq!("ic".parse::<View>().unwrap(), View::Interconnection);
/// assert_eq!(View::Interconnection.to_string(), "interconnection");
/// ```
#[derive(Clone, Copy, PartialEq, Eq, Debug, Default, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum View {
    /// Structure ("tree") view: packages, definitions, usages.
    #[default]
    Tree,
    /// Parts, ports, and connector edges.
    #[serde(alias = "ic")]
    Interconnection,
    /// State machines: states, transitions, entry/do/exit.
    State,
    /// Action flows: actions, control nodes, successions, flows.
    Action,
    /// Lifelines and messages, ordered by event successions.
    #[serde(alias = "seq")]
    Sequence,
    /// Use cases: actors, subjects, objectives, includes.
    Case,
    /// Everything on one canvas: structure, ports, connectors,
    /// behaviors, cases, typing/specialization.
    Mixed,
}

impl View {
    /// The spelling of each view, canonical spellings only.
    const SPELLINGS: &'static [(&'static str, View)] = &[
        ("tree", View::Tree),
        ("interconnection", View::Interconnection),
        ("state", View::State),
        ("action", View::Action),
        ("sequence", View::Sequence),
        ("case", View::Case),
        ("mixed", View::Mixed),
    ];

    /// The short spellings hosts also accept, beside the canonical ones.
    const SHORTHANDS: &'static [(&'static str, View)] =
        &[("ic", View::Interconnection), ("seq", View::Sequence)];

    /// The canonical spelling — what [`Display`](fmt::Display), serde
    /// and the structured graph's `view` field write. Matched rather
    /// than looked up, so a view added without a spelling is a compile
    /// error instead of a silent misspelling of another one.
    pub fn as_str(self) -> &'static str {
        match self {
            View::Tree => "tree",
            View::Interconnection => "interconnection",
            View::State => "state",
            View::Action => "action",
            View::Sequence => "sequence",
            View::Case => "case",
            View::Mixed => "mixed",
        }
    }
}

impl fmt::Display for View {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.as_str())
    }
}

impl FromStr for View {
    type Err = ParseOptionError;

    fn from_str(s: &str) -> Result<View, ParseOptionError> {
        Self::SPELLINGS
            .iter()
            .chain(Self::SHORTHANDS)
            .find(|(spelling, _)| *spelling == s)
            .map(|(_, v)| *v)
            .ok_or_else(|| ParseOptionError::new("view", s, Self::SPELLINGS))
    }
}

/// Edge routing (PlantUML `skinparam linetype`).
///
/// Spelled the same way as [`View`] on every host surface.
#[derive(Clone, Copy, PartialEq, Eq, Debug, Default, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum LineStyle {
    /// PlantUML's default splines.
    #[default]
    Default,
    Polyline,
    Ortho,
}

impl LineStyle {
    const SPELLINGS: &'static [(&'static str, LineStyle)] = &[
        ("default", LineStyle::Default),
        ("polyline", LineStyle::Polyline),
        ("ortho", LineStyle::Ortho),
    ];

    /// The canonical spelling — what [`Display`](fmt::Display) and
    /// serde write. Matched rather than looked up, for the reason
    /// [`View::as_str`] gives.
    pub fn as_str(self) -> &'static str {
        match self {
            LineStyle::Default => "default",
            LineStyle::Polyline => "polyline",
            LineStyle::Ortho => "ortho",
        }
    }
}

impl fmt::Display for LineStyle {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.as_str())
    }
}

impl FromStr for LineStyle {
    type Err = ParseOptionError;

    fn from_str(s: &str) -> Result<LineStyle, ParseOptionError> {
        Self::SPELLINGS
            .iter()
            .find(|(spelling, _)| *spelling == s)
            .map(|(_, v)| *v)
            .ok_or_else(|| ParseOptionError::new("line style", s, Self::SPELLINGS))
    }
}

/// A spelling that names no member of one of the option enums —
/// the error of [`View`]'s and [`LineStyle`]'s [`FromStr`].
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct ParseOptionError {
    option: &'static str,
    spelling: String,
    expected: Vec<&'static str>,
}

impl ParseOptionError {
    fn new<T>(option: &'static str, spelling: &str, expected: &[(&'static str, T)]) -> Self {
        ParseOptionError {
            option,
            spelling: spelling.to_string(),
            expected: expected.iter().map(|(s, _)| *s).collect(),
        }
    }

    /// What was being named: `view`, `line style`.
    pub fn option(&self) -> &str {
        self.option
    }

    /// The spelling that named nothing.
    pub fn spelling(&self) -> &str {
        &self.spelling
    }

    /// The canonical spellings, in declaration order.
    pub fn expected(&self) -> &[&'static str] {
        &self.expected
    }
}

impl fmt::Display for ParseOptionError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "unknown {}: {}", self.option, self.spelling)?;
        match self.expected.split_last() {
            Some((last, [])) => write!(f, " (expected {last})"),
            Some((last, rest)) => write!(f, " (expected {}, or {last})", rest.join(", ")),
            None => Ok(()),
        }
    }
}

impl std::error::Error for ParseOptionError {}

/// Options for [`plantuml`]. `show_values` renders `= value` on
/// attribute lines when the attribute's value expression evaluates to a
/// scalar (evaluation failures are silently skipped; tree view only).
///
/// Build one from [`VizOptions::default`] and the `with_…` setters, so
/// that a later option does not break callers:
///
/// ```
/// use sysmlv2_viz::{View, VizOptions};
///
/// let opts = VizOptions::default()
///     .with_view(View::Case)
///     .with_show_notes(false);
/// assert_eq!(opts.view, View::Case);
/// assert!(!opts.show_notes);
/// ```
#[derive(Clone, Debug)]
#[non_exhaustive]
pub struct VizOptions {
    pub direction: Direction,
    pub show_values: bool,
    pub view: View,
    /// Attach comment/documentation bodies as `note` blocks (views in
    /// the class/component/use-case dialects).
    pub show_notes: bool,
    /// Show metadata: prefix metadata (`#M` / `@M`) joins the node's
    /// stereotype list; `false` also drops metadata usages as nodes.
    pub show_metadata: bool,
    /// Add inherited attribute compartment lines (one explicit
    /// typing/specialization hop, `^`-prefixed; tree view).
    pub show_inherited: bool,
    /// Render referenced standard-library types as (marked) nodes
    /// instead of label-only names.
    pub show_lib: bool,
    /// Draw `«import»` edges for import relationships whose two ends
    /// are on the diagram.
    pub show_imported: bool,
    pub line_style: LineStyle,
    /// Color nodes by metaclass family (a fixed palette keyed on the
    /// stereotype).
    pub std_color: bool,
    /// Hyperlink template for node declarations (`[[url]]` in the
    /// PlantUML, carried into SVG). Placeholders: `{file}`, `{line}`,
    /// `{col}` (declaration site), `{qname}`, `{id}`.
    pub link_template: Option<String>,
    /// When `root` is `None`, restrict the diagram to exactly these
    /// top-level elements (and their subtrees) instead of every
    /// top-level user element. `None` or empty = the whole model — the
    /// package/root filter behind the diagram panel's package selector.
    /// Ignored when a single `root` is passed (that scoping wins).
    pub roots: Option<Vec<ElementRef>>,
    /// Summary emission for large scopes (graph emitter, tree view):
    /// containers outside `open` emit as one node with counts, cross-
    /// container references aggregate, notes beyond a budget fold into
    /// counts. `None` is the full emission.
    pub summary: Option<SummaryOptions>,
}

/// Summary emission controls (see [`VizOptions::summary`]).
#[derive(Clone, Debug, Default)]
pub struct SummaryOptions {
    /// Containers whose direct members are emitted; every other container
    /// is one summary node. An entry under a closed ancestor is inert
    /// (the ancestor hides it); the scope roots must be listed to open.
    pub open: Vec<ElementRef>,
    /// Notes drawn as nodes per cluster; the rest become `noteCount` on
    /// their target.
    pub note_budget: usize,
    /// Direct members emitted per open container; the rest are counted as
    /// `truncated` and hidden under it.
    pub leaf_budget: usize,
    /// Open containers drawn whole: every direct member emits regardless
    /// of `leaf_budget` (a per-container override).
    pub unbounded: Vec<ElementRef>,
}

impl Default for VizOptions {
    fn default() -> VizOptions {
        VizOptions {
            direction: Direction::default(),
            show_values: true,
            view: View::default(),
            show_notes: true,
            show_metadata: true,
            show_inherited: false,
            show_lib: false,
            show_imported: false,
            line_style: LineStyle::default(),
            std_color: false,
            link_template: None,
            roots: None,
            summary: None,
        }
    }
}

/// One setter per option, each consuming and returning the options so
/// they chain from [`VizOptions::default`].
impl VizOptions {
    /// Configure summary emission for the structured tree graph.
    pub fn with_summary(mut self, summary: Option<SummaryOptions>) -> VizOptions {
        self.summary = summary;
        self
    }

    /// Layout direction.
    pub fn with_direction(mut self, direction: Direction) -> VizOptions {
        self.direction = direction;
        self
    }

    /// Render `= value` on attribute lines.
    pub fn with_show_values(mut self, on: bool) -> VizOptions {
        self.show_values = on;
        self
    }

    /// Which diagram to emit.
    pub fn with_view(mut self, view: View) -> VizOptions {
        self.view = view;
        self
    }

    /// Attach comment/documentation bodies as notes.
    pub fn with_show_notes(mut self, on: bool) -> VizOptions {
        self.show_notes = on;
        self
    }

    /// Show metadata as stereotypes and nodes.
    pub fn with_show_metadata(mut self, on: bool) -> VizOptions {
        self.show_metadata = on;
        self
    }

    /// Add inherited compartment lines.
    pub fn with_show_inherited(mut self, on: bool) -> VizOptions {
        self.show_inherited = on;
        self
    }

    /// Give referenced library types their own marked nodes.
    pub fn with_show_lib(mut self, on: bool) -> VizOptions {
        self.show_lib = on;
        self
    }

    /// Draw `«import»` edges.
    pub fn with_show_imported(mut self, on: bool) -> VizOptions {
        self.show_imported = on;
        self
    }

    /// Edge routing.
    pub fn with_line_style(mut self, line_style: LineStyle) -> VizOptions {
        self.line_style = line_style;
        self
    }

    /// Color nodes by metaclass family.
    pub fn with_std_color(mut self, on: bool) -> VizOptions {
        self.std_color = on;
        self
    }

    /// Hyperlink template for node declarations; `None` draws no links.
    pub fn with_link_template(mut self, link_template: Option<String>) -> VizOptions {
        self.link_template = link_template;
        self
    }

    /// Restrict the diagram to these top-level elements; `None` or
    /// empty is the whole model.
    pub fn with_roots(mut self, roots: Option<Vec<ElementRef>>) -> VizOptions {
        self.roots = roots;
        self
    }
}

/// What a *view usage* directs: the rendering style its `render` member
/// requests (when it maps onto a PlantUML view) and the diagram roots its
/// `expose`/`filter` members admit. Exposure reduces to the finest
/// exposed granularity — an exposed container whose members are also
/// individually exposed yields the members (so filtered-out siblings
/// stay off the diagram) — and connector end features and metadata
/// usages drop (they render through their owners). `None` when the
/// element is not a view usage.
pub fn view_directed(
    r: &mut ResolvedModel,
    view: ElementRef,
) -> Option<(Option<View>, Vec<ElementRef>)> {
    if r.element_type(view) != "ViewUsage" {
        return None;
    }
    let style = match r.view_rendering(view).as_deref() {
        Some("asTreeDiagram") => Some(View::Tree),
        Some("asInterconnectionDiagram") => Some(View::Interconnection),
        _ => None,
    };
    // Connector end features and metadata usages drop *before* the
    // granularity pass — they render through their owners, and an
    // exposed connector must not read as a container just because its
    // own ends were enumerated.
    let exposed: Vec<ElementRef> = r
        .view_exposed_elements(view)
        .into_iter()
        .filter(|&x| {
            r.element_type(x) != "MetadataUsage"
                && r.owning_membership_type(x) != Some("EndFeatureMembership")
        })
        .collect();
    let set: std::collections::HashSet<ElementRef> = exposed.iter().copied().collect();
    let mut coarse: std::collections::HashSet<ElementRef> = std::collections::HashSet::new();
    for &x in &exposed {
        let mut cur = r.owner(x);
        while let Some(o) = cur {
            if set.contains(&o) {
                coarse.insert(o);
            }
            cur = r.owner(o);
        }
    }
    let roots = exposed
        .into_iter()
        .filter(|x| !coarse.contains(x))
        .collect();
    Some((style, roots))
}

/// Emit the configured view of `root` (or of every top-level user
/// element when `root` is `None`) as PlantUML text.
pub fn plantuml(r: &mut ResolvedModel, root: Option<ElementRef>, opts: &VizOptions) -> String {
    let tops = roots_of(r, root, opts);
    match opts.view {
        View::Tree => tree(r, &tops, opts),
        View::Interconnection => interconnect::emit(r, &tops, opts, false),
        View::State => behavior::emit(r, &tops, opts, View::State),
        View::Action => behavior::emit(r, &tops, opts, View::Action),
        View::Sequence => sequence::emit(r, &tops, opts),
        View::Case => case::emit(r, &tops, opts),
        View::Mixed => interconnect::emit(r, &tops, opts, true),
    }
}

/// The diagram's top-level elements: a single `root` when given (its
/// subtree), else the caller's `opts.roots` selection when non-empty
/// (the package filter), else every top-level user element.
pub(crate) fn roots_of(
    r: &mut ResolvedModel,
    root: Option<ElementRef>,
    opts: &VizOptions,
) -> Vec<ElementRef> {
    match root {
        Some(e) => vec![e],
        None => match &opts.roots {
            Some(rs) if !rs.is_empty() => rs.clone(),
            _ => top_level_elements(r),
        },
    }
}

/// Top-level user elements: the owned members of each unit's root
/// namespace, plus any ownerless non-namespace stragglers.
fn top_level_elements(r: &mut ResolvedModel) -> Vec<ElementRef> {
    let all: Vec<ElementRef> = r.user_elements().collect();
    let mut tops = Vec::new();
    for e in all {
        if r.owner(e).is_some() {
            continue;
        }
        if r.element_type(e) == "Namespace" {
            tops.extend(r.owned_members(e));
        } else {
            tops.push(e);
        }
    }
    tops
}

/// Frame `body` + `edges` in `@startuml … @enduml` with the shared
/// header lines.
fn frame(opts: &VizOptions, header: &str, body: &str, edges: &str) -> String {
    let mut out = String::from("@startuml\n");
    if opts.direction == Direction::LeftToRight {
        out.push_str("left to right direction\n");
    }
    out.push_str(header);
    out.push_str(body);
    out.push_str(edges);
    out.push_str("@enduml\n");
    out
}

fn tree(r: &mut ResolvedModel, tops: &[ElementRef], opts: &VizOptions) -> String {
    let mut emitter = Emitter {
        r,
        opts,
        alias: HashMap::new(),
        body: String::new(),
        edges: String::new(),
        rendered: Vec::new(),
    };
    for e in tops {
        emitter.render(*e, 0);
    }
    emitter.emit_reference_edges();
    let Emitter {
        r,
        alias,
        body,
        mut edges,
        ..
    } = emitter;
    emit_notes(r, opts, &alias, &mut edges);
    let header = format!("hide empty members\n{}", style_header(opts, &["class"]));
    frame(opts, &header, &body, &edges)
}

/// How one owned member renders in the structure view.
pub(crate) enum Kind {
    /// `package` block; members recurse inside it.
    Package,
    /// `class` node with a stereotype; definitions and KerML
    /// classifier-family types.
    TypeNode,
    /// `enum` node; enumeration definitions.
    EnumNode,
    /// Child node with a composition edge from the owner.
    UsageNode,
    /// Compartment line on the owning node (attribute-family usages).
    Line,
    /// Not rendered (imports, comments, relationships, anonymous
    /// bookkeeping).
    Skip,
}

/// KerML classifier-family metaclasses that render as type nodes even
/// though their names do not end in `Definition`.
const KERML_TYPES: &[&str] = &[
    "Classifier",
    "Class",
    "Structure",
    "DataType",
    "Behavior",
    "Function",
    "Predicate",
    "Interaction",
    "Association",
    "AssociationStructure",
    "Metaclass",
    "Type",
];

/// Usage-family metaclasses that render as compartment lines on their
/// owner instead of standalone nodes.
const LINE_USAGES: &[&str] = &["AttributeUsage", "ReferenceUsage", "EnumerationUsage"];

/// Structure-view rendering role of one element — shared by the
/// PlantUML tree emitter and the structured graph emitter, so the two
/// backends can never disagree about what is a node, a compartment
/// line, or invisible.
pub(crate) fn classify(r: &ResolvedModel, show_metadata: bool, e: ElementRef) -> Kind {
    let ty = r.element_type(e);
    match ty {
        _ if !show_metadata && matches!(ty, "MetadataUsage" | "MetadataFeature") => Kind::Skip,
        "Package" | "LibraryPackage" => Kind::Package,
        "EnumerationDefinition" => Kind::EnumNode,
        _ if LINE_USAGES.contains(&ty) => Kind::Line,
        _ if ty.ends_with("Definition") => Kind::TypeNode,
        _ if ty.ends_with("Usage") => Kind::UsageNode,
        _ if KERML_TYPES.contains(&ty) => Kind::TypeNode,
        // KerML features: compartment line when it is a leaf, node when
        // it nests further features.
        "Feature" | "Step" | "Expression" => {
            if r.owned_features(e).is_empty() {
                Kind::Line
            } else {
                Kind::UsageNode
            }
        }
        _ => Kind::Skip,
    }
}

struct Emitter<'a> {
    r: &'a mut ResolvedModel,
    opts: &'a VizOptions,
    alias: HashMap<ElementRef, String>,
    body: String,
    edges: String,
    /// Every element drawn as a node, with whether it is usage-like —
    /// specialization/typing edges are emitted in a second pass so a
    /// target declared later in the model still gets its edge.
    rendered: Vec<(ElementRef, bool)>,
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

    fn classify(&self, e: ElementRef) -> Kind {
        classify(self.r, self.opts.show_metadata, e)
    }

    fn indent(&mut self, depth: usize) {
        for _ in 0..depth {
            self.body.push_str("  ");
        }
    }

    fn usage_label(&mut self, e: ElementRef) -> String {
        usage_label(self.r, e)
    }

    fn value_suffix(&mut self, e: ElementRef) -> Option<String> {
        if !self.opts.show_values {
            return None;
        }
        value_suffix(self.r, e)
    }

    /// Compartment lines for a node: attribute-family members plus
    /// enum literals; returns the members that need their own nodes.
    /// With `show_inherited`, members one explicit typing /
    /// specialization hop away add `^`-prefixed lines (own names
    /// shadow).
    fn split_members(&mut self, e: ElementRef) -> (Vec<String>, Vec<ElementRef>) {
        let mut lines = Vec::new();
        let mut children = Vec::new();
        let mut own_names: Vec<String> = Vec::new();
        let metas = self.r.metadata_of(e);
        for m in self.r.owned_members(e) {
            // Prefix metadata renders as the owner's stereotype.
            if metas.contains(&m) {
                continue;
            }
            match self.classify(m) {
                Kind::Line => {
                    if let Some(n) = display_name(self.r, m) {
                        own_names.push(n);
                    }
                    let mut line = self.usage_label(m);
                    if let Some(value) = self.value_suffix(m) {
                        line.push(' ');
                        line.push_str(&value);
                    }
                    if !line.trim().is_empty() {
                        lines.push(line);
                    }
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
                    if !matches!(self.classify(m), Kind::Line) {
                        continue;
                    }
                    let shadowed = self
                        .r
                        .element_name(m)
                        .is_some_and(|n| own_names.iter().any(|o| o == n));
                    if shadowed {
                        continue;
                    }
                    let line = self.usage_label(m);
                    if !line.trim().is_empty() {
                        lines.push(format!("^{line}"));
                    }
                }
            }
        }
        (lines, children)
    }

    fn render(&mut self, e: ElementRef, depth: usize) {
        match self.classify(e) {
            Kind::Package => self.render_package(e, depth),
            Kind::TypeNode => self.render_node(e, depth, false),
            Kind::UsageNode => self.render_node(e, depth, true),
            Kind::EnumNode => self.render_enum(e, depth),
            // A top-level attribute-family element still needs a node.
            Kind::Line => self.render_node(e, depth, true),
            Kind::Skip => {}
        }
    }

    fn render_package(&mut self, e: ElementRef, depth: usize) {
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
        self.rendered.push((e, false));
    }

    fn render_node(&mut self, e: ElementRef, depth: usize, is_usage: bool) {
        let alias = self.alias_for(e);
        let ty = self.r.element_type(e);
        let stereo = stereotype(ty);
        let label = if is_usage {
            self.usage_label(e)
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
        let (lines, children) = self.split_members(e);

        let stereos = stereo_text(self.r, self.opts, e, &stereo);
        let link = link_suffix(self.r, self.opts, e);
        self.indent(depth);
        let _ = write!(
            self.body,
            "class \"{}\" as {alias} {stereos}{link}",
            escape(&label)
        );
        if lines.is_empty() {
            self.body.push('\n');
        } else {
            self.body.push_str(" {\n");
            for line in &lines {
                self.indent(depth + 1);
                let _ = writeln!(self.body, "{}", sanitize_line(line));
            }
            self.indent(depth);
            self.body.push_str("}\n");
        }

        self.rendered.push((e, is_usage));

        for child in children {
            let child_alias = self.alias_for(child);
            self.render(child, depth);
            if matches!(self.classify(child), Kind::UsageNode | Kind::Line) {
                // Composite ownership draws the solid rhomb; a
                // referential usage (`ref part r : P;`,
                // `isComposite=false`) draws the hollow one — the
                // graphical notation must distinguish the two.
                let edge = if self.r.is_composite(child) == Some(false) {
                    "o--"
                } else {
                    "*--"
                };
                let _ = writeln!(self.edges, "{alias} {edge} {child_alias}");
            } else {
                let _ = writeln!(self.edges, "{alias} +-- {child_alias}");
            }
        }
    }

    fn render_enum(&mut self, e: ElementRef, depth: usize) {
        let alias = self.alias_for(e);
        let name = escape(self.r.element_name(e).unwrap_or("(enum)"));
        let members = self.r.owned_members(e);
        let literals: Vec<String> = members
            .iter()
            .filter(|m| self.r.is_enum_value(**m))
            .filter_map(|m| self.r.element_name(*m).map(str::to_string))
            .collect();
        let link = link_suffix(self.r, self.opts, e);
        self.indent(depth);
        let _ = write!(self.body, "enum \"{name}\" as {alias} <<enum def>>{link}");
        if literals.is_empty() {
            self.body.push('\n');
        } else {
            self.body.push_str(" {\n");
            for lit in &literals {
                self.indent(depth + 1);
                let _ = writeln!(self.body, "{}", sanitize_line(lit));
            }
            self.indent(depth);
            self.body.push_str("}\n");
        }
        self.rendered.push((e, false));
    }

    /// Second pass: specialization and typing edges between rendered
    /// nodes. Library and off-diagram targets are normally omitted
    /// (their names already appear in node labels) — `show_lib` gives
    /// referenced library types their own marked nodes instead.
    fn emit_reference_edges(&mut self) {
        // Collection is over, so the pass takes the list rather than
        // copying it to keep the emitter free to mutate.
        let rendered = std::mem::take(&mut self.rendered);
        for &(e, is_usage) in &rendered {
            let alias = self.alias[&e].clone();
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
            // FeatureTyping is a specialization in KerML: subtract the
            // typing targets so usage typing edges are not doubled.
            for target in self.r.explicit_supertypes(e) {
                if typings.contains(&target) {
                    continue;
                }
                if let Some(target_alias) = self.target_alias(target) {
                    let _ = writeln!(self.edges, "{alias} --|> {target_alias}");
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
        // Library nodes drawn on demand during the pass were appended
        // to the emptied list; the walked nodes go back in front of
        // them, so the node list stays complete and in draw order.
        let drawn_during = std::mem::replace(&mut self.rendered, rendered);
        self.rendered.extend(drawn_during);
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
            "class \"{}\" as {alias} <<{stereo}>> <<library>>",
            escape(&name)
        );
        self.rendered.push((target, false));
        Some(alias)
    }
}

/// A member's display name: its declared name, else the name of the
/// feature it explicitly redefines (followed one hop at a time — a
/// redefinition target may itself be unnamed), mirroring the effective
/// naming the interchange layer derives. Keeps anonymous redefining
/// members (`:>> x = v` spellings) labelled in compartments.
pub(crate) fn display_name(r: &mut ResolvedModel, e: ElementRef) -> Option<String> {
    let mut cur = e;
    for _ in 0..32 {
        if let Some(n) = r.element_name(cur) {
            return Some(n.to_string());
        }
        cur = *r.redefinition_targets(cur).first()?;
    }
    None
}

/// `name : Type1, Type2 [mult]` — the shared label shape for usages
/// and compartment lines. Library type names still appear even
/// though library elements are never rendered as nodes.
pub(crate) fn usage_label(r: &mut ResolvedModel, e: ElementRef) -> String {
    let mut label = display_name(r, e).unwrap_or_default();
    // Explicit typings, else the type derived through redefinition —
    // `part redefines brewing;` keeps the redefined feature's type in
    // its label (KerML derives the redefining feature's /type).
    let mut typings = r.typings(e);
    let mut cur = e;
    let mut hops = 0;
    while typings.is_empty() && hops < 8 {
        let targets = r.redefinition_targets(cur);
        let Some(&t) = targets.first() else { break };
        typings = r.typings(t);
        cur = t;
        hops += 1;
    }
    let type_names: Vec<String> = typings
        .iter()
        .filter_map(|t| r.element_name(*t).map(str::to_string))
        .collect();
    if !type_names.is_empty() {
        if !label.is_empty() {
            label.push(' ');
        }
        label.push_str(": ");
        label.push_str(&type_names.join(", "));
    }
    if let Some(mult) = multiplicity_suffix(r, e) {
        label.push(' ');
        label.push_str(&mult);
    }
    label
}

/// `= value` suffix for a compartment line: scalar results render
/// literally, element results (enum literals, referenced usages) by
/// name — an anonymous element or the feature itself (the unbound
/// case) says nothing. Shared by the PlantUML and graph backends.
pub(crate) fn value_suffix(r: &mut ResolvedModel, e: ElementRef) -> Option<String> {
    if !r.has_value(e) {
        return None;
    }
    let rendered = match r.evaluate(e).ok()? {
        Value::Boolean(b) => b.to_string(),
        Value::Integer(i) => i.to_string(),
        Value::Rational(r) => r.to_string(),
        Value::Real(f) => format!("{f}"),
        Value::String(s) => format!("\"{s}\""),
        Value::Quantity(n, unit) => {
            let magnitude = match *n {
                Value::Integer(i) => i.to_string(),
                Value::Rational(r) => r.to_string(),
                Value::Real(f) => format!("{f}"),
                _ => return None,
            };
            format!("{magnitude} [{}]", unit.display())
        }
        Value::Element(t) if t != e => r.element_name(t).map(str::to_string)?,
        // A placeholder (or the element itself) is the unbound case —
        // nothing worth labeling.
        _ => return None,
    };
    Some(format!("= {rendered}"))
}

pub(crate) fn multiplicity_suffix(r: &mut ResolvedModel, e: ElementRef) -> Option<String> {
    let (lo, hi) = r.declared_multiplicity(e)?;
    let fmt_bound = |b: f64| {
        if b.is_infinite() {
            "*".to_string()
        } else if b.fract() == 0.0 {
            format!("{}", b as i64)
        } else {
            format!("{b}")
        }
    };
    Some(if lo == hi {
        format!("[{}]", fmt_bound(lo))
    } else {
        format!("[{}..{}]", fmt_bound(lo), fmt_bound(hi))
    })
}

/// «part def»-style stereotype from a metaclass name.
pub(crate) fn stereotype(ty: &str) -> String {
    let mut words = Vec::new();
    let mut current = String::new();
    for ch in ty.chars() {
        if ch.is_uppercase() && !current.is_empty() {
            words.push(current.to_lowercase());
            current = String::new();
        }
        current.push(ch);
    }
    if !current.is_empty() {
        words.push(current.to_lowercase());
    }
    match words.last().map(String::as_str) {
        Some("definition") => {
            let n = words.len();
            words[n - 1] = "def".to_string();
        }
        // drop the suffix word — except for the bare `Usage`
        // metaclass (user-keyword usages), which would otherwise
        // leave an empty (and invalid) stereotype
        Some("usage") if words.len() > 1 => {
            words.pop();
        }
        _ => {}
    }
    words.join(" ")
}

/// The dotted spelling of a resolved feature chain (`a.b`) — edge-end
/// and reference labels.
pub(crate) fn chain_label(r: &ResolvedModel, chain: &[ElementRef]) -> String {
    chain
        .iter()
        .filter_map(|&link| r.element_name(link).map(str::to_string))
        .collect::<Vec<_>>()
        .join(".")
}

/// Single-line edge/description label text: newlines and runs of
/// whitespace collapse to one space.
pub(crate) fn inline_label(s: &str) -> String {
    s.split_whitespace().collect::<Vec<_>>().join(" ")
}

/// The flow/message payload label (`fuel : Fuel`), when one was written.
pub(crate) fn payload_label(r: &mut ResolvedModel, e: ElementRef) -> Option<String> {
    let payload = r
        .owned_members(e)
        .into_iter()
        .find(|&m| r.element_type(m) == "PayloadFeature")?;
    let label = usage_label(r, payload);
    (!label.trim().is_empty()).then(|| inline_label(&label))
}

/// Quoted-label escaping for the diagram language. A double quote would
/// end the label (it becomes two single quotes), a line break would end
/// the command and leave the rest of the label as a stray line of
/// diagram text (it becomes the `\n` escape the renderer honours inside
/// quotes), and a carriage return has no rendering at all (dropped).
///
/// A backslash is doubled, which is what makes the mapping reversible:
/// without it a name containing the two characters `\n` would reach the
/// renderer spelled exactly like one containing a line break.
pub(crate) fn escape(s: &str) -> String {
    let mut out = String::with_capacity(s.len());
    for ch in s.chars() {
        match ch {
            '\\' => out.push_str("\\\\"),
            '"' => out.push_str("''"),
            '\n' => out.push_str("\\n"),
            '\r' => {}
            c => out.push(c),
        }
    }
    out
}

/// Percent-encode the characters that would end or restructure a
/// `[[url]]` link: whitespace (ends the URL part), `]` (closes the
/// link), and braces (open a tooltip).
fn encode_link(url: &str) -> String {
    let mut out = String::with_capacity(url.len());
    for ch in url.chars() {
        match ch {
            ' ' => out.push_str("%20"),
            '\t' => out.push_str("%09"),
            '\n' => out.push_str("%0A"),
            '\r' => out.push_str("%0D"),
            ']' => out.push_str("%5D"),
            '{' => out.push_str("%7B"),
            '}' => out.push_str("%7D"),
            c => out.push(c),
        }
    }
    out
}

/// The STDCOLOR palette: stereotype → background color, one hue family
/// per metaclass family (definitions darker than their usages).
const PALETTE: &[(&str, &str)] = &[
    ("part def", "#BBDEFB"),
    ("part", "#E3F2FD"),
    ("item def", "#C5CAE9"),
    ("item", "#E8EAF6"),
    ("port def", "#FFF59D"),
    ("port", "#FFF9C4"),
    ("attribute def", "#DCEDC8"),
    ("enum def", "#F0F4C3"),
    ("action def", "#C8E6C9"),
    ("action", "#E8F5E9"),
    ("state def", "#FFE0B2"),
    ("state", "#FFF3E0"),
    ("use case def", "#E1BEE7"),
    ("use case", "#F3E5F5"),
    ("case def", "#D1C4E9"),
    ("case", "#EDE7F6"),
    ("requirement def", "#F8BBD0"),
    ("requirement", "#FCE4EC"),
    ("constraint def", "#FFCDD2"),
    ("constraint", "#FFEBEE"),
    ("connection def", "#B2EBF2"),
    ("interface def", "#B2DFDB"),
    ("subject", "#FFECB3"),
    ("library", "#ECEFF1"),
];

/// Style header lines for one view: line routing plus, under
/// `std_color`, stereotype-keyed background colors for the view's
/// container keywords (`class`, `rectangle`, `state`, `usecase`).
pub(crate) fn style_header(opts: &VizOptions, containers: &[&str]) -> String {
    let mut out = String::new();
    match opts.line_style {
        LineStyle::Default => {}
        LineStyle::Polyline => out.push_str("skinparam linetype polyline\n"),
        LineStyle::Ortho => out.push_str("skinparam linetype ortho\n"),
    }
    if opts.std_color {
        for c in containers {
            let _ = writeln!(out, "skinparam {c} {{");
            for (stereo, color) in PALETTE {
                let _ = writeln!(out, "  BackgroundColor<<{stereo}>> {color}");
            }
            out.push_str("}\n");
        }
    }
    out
}

/// ` [[url]]` for a node declaration, from the configured link
/// template. Elements without a declaration site (synthesized) link
/// nowhere.
pub(crate) fn link_suffix(r: &mut ResolvedModel, opts: &VizOptions, e: ElementRef) -> String {
    let Some(tpl) = &opts.link_template else {
        return String::new();
    };
    let mut url = tpl.clone();
    if url.contains("{file}") || url.contains("{line}") || url.contains("{col}") {
        let Some((file, line, col)) = r.declaration_position(e) else {
            return String::new();
        };
        let (file, line, col) = (file.to_string(), line.to_string(), col.to_string());
        url = url
            .replace("{file}", &file)
            .replace("{line}", &line)
            .replace("{col}", &col);
    }
    if url.contains("{qname}") {
        let qname = r.element_qualified_name(e).unwrap_or_default();
        url = url.replace("{qname}", &qname);
    }
    if url.contains("{id}") {
        url = url.replace("{id}", &r.element_id(e).to_string());
    }
    format!(" [[{}]]", encode_link(&url))
}

/// `<<stereo>>` plus one `<<Meta>>` per prefix metadata annotating `e`
/// (named by the metadata's typing) when metadata display is on.
pub(crate) fn stereo_text(
    r: &mut ResolvedModel,
    opts: &VizOptions,
    e: ElementRef,
    base: &str,
) -> String {
    let mut out = format!("<<{base}>>");
    if !opts.show_metadata {
        return out;
    }
    for m in r.metadata_of(e) {
        // `#M` types via MetadataTyping — a specialization kind, not a
        // FeatureTyping — so the supertype walk names it.
        let mut targets = r.typings(m);
        if targets.is_empty() {
            targets = r.explicit_supertypes(m);
        }
        let names: Vec<String> = targets
            .into_iter()
            .filter_map(|t| r.element_name(t).map(str::to_string))
            .collect();
        let name = if names.is_empty() {
            r.element_name(m).map(str::to_string)
        } else {
            Some(names.join(", "))
        };
        if let Some(n) = name {
            let _ = write!(out, " <<{n}>>");
        }
    }
    out
}

/// Floating notes for every comment/documentation body whose
/// annotated element is on the diagram (`alias` map), attached with
/// `..`. Note aliases are `c1…` — disjoint from the node `n…` space.
pub(crate) fn emit_notes(
    r: &mut ResolvedModel,
    opts: &VizOptions,
    alias: &HashMap<ElementRef, String>,
    out: &mut String,
) {
    if !opts.show_notes {
        return;
    }
    let mut k = 0usize;
    for (target, body) in r.annotation_bodies() {
        let Some(a) = alias.get(&target) else {
            continue;
        };
        k += 1;
        let _ = writeln!(out, "note \"{}\" as c{k}", note_text(&body));
        let _ = writeln!(out, "c{k} .. {a}");
    }
}

/// A note body as the text of a quoted single-line `note "…" as x`:
/// one `\n` escape per line break. The block form (`note as x` …
/// `end note`) is not used because the renderer ends it at any body
/// line spelling the terminator (`end note`, `endnote`, in any case,
/// after any indent) and reads the rest as diagram commands; inside
/// quotes no body text can end the note.
pub(crate) fn note_text(body: &str) -> String {
    body.lines().map(escape).collect::<Vec<_>>().join("\\n")
}

/// Compartment lines are unquoted PlantUML member syntax; strip the
/// characters that would change their parse (braces open a block,
/// leading `-`/`+`/`#` set visibility, a line break ends the member —
/// it becomes a space; a carriage return is dropped).
fn sanitize_line(s: &str) -> String {
    let cleaned: String = s
        .chars()
        .filter(|c| !matches!(c, '{' | '}' | '\r'))
        .map(|c| if c == '\n' { ' ' } else { c })
        .collect();
    let trimmed = cleaned.trim().to_string();
    match trimmed.chars().next() {
        Some('-') | Some('+') | Some('#') | Some('~') => format!("\\{trimmed}"),
        _ => trimmed,
    }
}
