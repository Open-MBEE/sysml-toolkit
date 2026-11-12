//! PlantUML emission for SysML v2 / KerML models.
//!
//! Eight views over the resolved model, all deterministic (aliases in
//! declaration order) and all tolerant of unresolved references:
//!
//! - **Tree** (structure) — packages as `package` blocks,
//!   definitions and KerML classifiers as stereotyped `class` nodes,
//!   enum defs as `enum` nodes, usages as `name : Type [mult]` nodes
//!   under composition edges (attribute-family usages become
//!   compartment lines, and so do members in a role of their own, led
//!   by its keyword: `subject v : Vehicle`, `require c { x < 2 }`,
//!   `entry warm`, `end car : Car`, and a port's directed features,
//!   `in fuel : Fuel`), plus specialization (`--|>`) and typing
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
//! - **Context** (`context`) — the system context diagram: the parts
//!   of a context as nodes around the most connected one, connectors as
//!   edges labelled by their definition, no ports.
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
mod context;
mod graph;
mod interconnect;
mod sequence;

pub use graph::{GraphError, graph, summary_would_draw, summary_would_draw_within};

use std::collections::{BTreeMap, HashMap, HashSet};
use std::fmt;
use std::fmt::Write as _;
use std::str::FromStr;

use serde::{Deserialize, Serialize};
use sysmlv2_model::eval::{UnitDisplay, Value};
use sysmlv2_model::json::{ElementRef, ResolvedModel};
use sysmlv2_syntax::ast::Dialect;

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
    /// System context: parts as nodes around the most connected one,
    /// connectors as labelled edges, no ports.
    Context,
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
        ("context", View::Context),
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
            View::Context => "context",
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
    /// Which units a `= value` quantity shows in:
    /// [`UnitDisplay::Si`] (the default) keeps the evaluator's units,
    /// [`UnitDisplay::AsWritten`] the units the value was written in
    /// (see [`ResolvedModel::value_as_written`]).
    pub value_units: UnitDisplay,
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
            value_units: UnitDisplay::Si,
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

    /// Show `= value` quantities in the units `units` chooses.
    pub fn with_value_units(mut self, units: UnitDisplay) -> VizOptions {
        self.value_units = units;
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

/// What a *view usage* directs: the rendering style its rendering
/// requests (when it maps onto a PlantUML view) — its own `render`
/// member's, else the one it inherits, as
/// [`ResolvedModel::view_rendering`] reads it — and the diagram roots its
/// `expose`/`filter` members admit. Exposure reduces to the finest
/// exposed granularity — an exposed container whose members are also
/// individually exposed yields the members (so filtered-out siblings
/// stay off the diagram) — and connector end features and metadata
/// usages drop (they render through their owners). So does a member the
/// view reaches only through inheritance: a type's visible members
/// include the ones it inherits, so exposing `amp : Amp` exposes `Amp`'s
/// ports too, and they render on `amp`'s own box rather than beside it.
/// `None` when the element is not a view usage.
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
    let exposed = r.view_exposed_elements(view);
    // Only a member no expose reaches through ownership can have arrived
    // through inheritance; the inheritance walk runs only when one did.
    let reach = ExposeReach::of(r, view);
    let unowned: HashSet<ElementRef> = exposed
        .iter()
        .copied()
        .filter(|&x| !reach.owns(r, x))
        .collect();
    let inherited = if unowned.is_empty() {
        HashSet::new()
    } else {
        reach.inherited_members(r, &exposed)
    };
    // Connector end features and metadata usages drop *before* the
    // granularity pass — they render through their owners, and an
    // exposed connector must not read as a container just because its
    // own ends were enumerated. Inherited members drop there as well, so
    // a definition the view exposes whole is not taken apart for them.
    let exposed: Vec<ElementRef> = exposed
        .into_iter()
        .filter(|&x| {
            r.element_type(x) != "MetadataUsage"
                && r.owning_membership_type(x) != Some("EndFeatureMembership")
                && !(unowned.contains(&x) && inherited.contains(&x))
        })
        .collect();
    let set: HashSet<ElementRef> = exposed.iter().copied().collect();
    let mut coarse: HashSet<ElementRef> = HashSet::new();
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

/// How a view's own `expose` relationships reach elements through
/// ownership. `expose x;` names `x`; `expose x::*;` lists the members
/// `x` owns; the `::**` forms also list everything owned below those,
/// and `expose x::**;` names `x` as well. A bracket filter wraps the
/// import that names the target in a package of its own, owned by the
/// expose, which the reach reads through.
#[derive(Default)]
struct ExposeReach {
    /// Elements an expose names.
    named: HashSet<ElementRef>,
    /// Namespaces whose owned members an expose lists, each with whether
    /// the listing descends into the namespaces it lists.
    listed: BTreeMap<ElementRef, bool>,
}

impl ExposeReach {
    fn of(r: &mut ResolvedModel, view: ElementRef) -> ExposeReach {
        let mut reach = ExposeReach::default();
        for rel in r.owned_relationships(view) {
            if !matches!(r.element_type(rel), "NamespaceExpose" | "MembershipExpose") {
                continue;
            }
            let Some(mut target) = import_target(r, rel) else {
                continue;
            };
            // A bracket filter's package: the import it holds names the
            // actual target.
            if r.owning_membership_type(target.0) == Some("NamespaceExpose") {
                let inner = r
                    .owned_relationships(target.0)
                    .into_iter()
                    .find_map(|inner| import_target(r, inner));
                let Some(inner) = inner else {
                    continue;
                };
                target = inner;
            }
            let (element, namespace, recursive) = target;
            if !namespace {
                reach.named.insert(element);
            }
            if namespace || recursive {
                *reach.listed.entry(element).or_default() |= recursive;
            }
        }
        reach
    }

    /// Whether an expose reaches `x` through ownership.
    fn owns(&self, r: &mut ResolvedModel, x: ElementRef) -> bool {
        if self.named.contains(&x) {
            return true;
        }
        let mut direct = true;
        let mut cur = r.owner(x);
        while let Some(o) = cur {
            if self.listed.get(&o).is_some_and(|&deep| deep || direct) {
                return true;
            }
            direct = false;
            cur = r.owner(o);
        }
        false
    }

    /// The members inherited by everything the exposure enumerates:
    /// each listed namespace (a plain `x::*` takes in `x`'s implied
    /// library heritage too), everything a descending listing owns —
    /// including what the view's conditions reject, whose admitted
    /// members stay exposed — and every exposed element, which covers
    /// namespaces reached through imports.
    fn inherited_members(
        &self,
        r: &mut ResolvedModel,
        exposed: &[ElementRef],
    ) -> HashSet<ElementRef> {
        let mut visits: Vec<(ElementRef, bool)> =
            self.listed.keys().map(|&ns| (ns, true)).collect();
        let mut below: Vec<ElementRef> = self
            .listed
            .iter()
            .filter(|&(_, &deep)| deep)
            .map(|(&ns, _)| ns)
            .collect();
        let mut seen: HashSet<ElementRef> = below.iter().copied().collect();
        while let Some(ns) = below.pop() {
            for member in r.owned_members(ns) {
                if seen.insert(member) {
                    visits.push((member, false));
                    below.push(member);
                }
            }
        }
        visits.extend(
            exposed
                .iter()
                .filter(|x| !seen.contains(x))
                .map(|&x| (x, false)),
        );
        let mut members = HashSet::new();
        for (e, implied) in visits {
            for membership in r.inherited_memberships(e, implied) {
                members.extend(r.membership_member(membership));
            }
        }
        members
    }
}

/// What an import-family relationship targets — a membership read
/// through to its member — with whether it lists the target's members
/// (`::*`) and whether it descends (`::**`).
fn import_target(r: &mut ResolvedModel, rel: ElementRef) -> Option<(ElementRef, bool, bool)> {
    let (namespace, key) = match r.element_type(rel) {
        "NamespaceImport" | "NamespaceExpose" => (true, "importedNamespace"),
        "MembershipImport" | "MembershipExpose" => (false, "importedMembership"),
        _ => return None,
    };
    let props = r.element_properties(rel);
    let recursive = props.get("isRecursive").and_then(|v| v.as_bool()) == Some(true);
    let target = r.element_by_id(props.get(key)?.get("@id")?.as_str()?)?;
    let target = r.membership_member(target).unwrap_or(target);
    Some((target, namespace, recursive))
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
        View::Context => context::emit(r, &tops, opts),
        View::Mixed => interconnect::emit(r, &tops, opts, true),
    }
}

/// The elements a diagram of `root` under `opts` starts from: `root`
/// when given, else `opts.roots` when non-empty, else every top-level
/// user element. Passed back as `opts.roots` with no `root`, they scope
/// the same diagram without being looked up again — for a host that
/// emits or counts one scope more than once.
pub fn scope_roots(
    r: &mut ResolvedModel,
    root: Option<ElementRef>,
    opts: &VizOptions,
) -> Vec<ElementRef> {
    roots_of(r, root, opts)
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
    /// Compartment line on the owning node: an attribute-family usage,
    /// a leaf KerML feature, and — whatever its metaclass — a member in
    /// a role of its own or a port's directed feature ([`classify`]).
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
/// line, or invisible. A member whose introduction gives it a [`Role`]
/// (`subject`, `require`, `entry`, a body's result expression, …) and a
/// port's directed feature are compartment lines of their owner, as
/// attributes are. The succession of a state's entry transition draws
/// nothing ([`is_entry_transition`]).
pub(crate) fn classify(r: &mut ResolvedModel, show_metadata: bool, e: ElementRef) -> Kind {
    let kind = classify_metaclass(r, show_metadata, e);
    let row = match kind {
        Kind::UsageNode | Kind::Line => {
            member_role(r, e).is_some() || port_feature_direction(r, e).is_some()
        }
        // A result expression is scaffolding everywhere else.
        Kind::Skip => member_role(r, e) == Some(Role::Result),
        _ => false,
    };
    if row {
        Kind::Line
    } else if matches!(kind, Kind::UsageNode) && is_entry_transition(r, e) {
        Kind::Skip
    } else {
        kind
    }
}

/// Whether `e` is the succession of a state's entry transition — `then
/// idle;` after `entry;`, which says which state the state machine
/// starts in: an anonymous succession a state owns, its source the
/// entry action before it rather than a written end (the grammar admits
/// such a `then` in a state's body only after its `entry`). The state
/// view draws it as the edge from the initial pseudostate; in the tree,
/// a node of its own could say neither, so it draws nothing there.
fn is_entry_transition(r: &mut ResolvedModel, e: ElementRef) -> bool {
    r.element_type(e) == "SuccessionAsUsage"
        && r.element_name(e).is_none()
        && r.owner(e)
            .is_some_and(|o| behavior::STATES.contains(&r.element_type(o)))
        && r.connector_end_targets(e)
            .first()
            .is_some_and(|end| end.chain.is_empty() && end.spelling.is_none())
}

/// [`classify`] by metaclass alone, before membership roles apply.
fn classify_metaclass(r: &ResolvedModel, show_metadata: bool, e: ElementRef) -> Kind {
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

/// How a member was introduced into its owner, when the introduction
/// itself is what the member is: the parameters and members a
/// requirement, case, calculation or concern declares through its own
/// memberships (`subject`, `actor`, `stakeholder`, `objective`,
/// `return`, `assume`, `require`, `frame`, `verify`), the result
/// expression a body ends with, an `include`d use case, a state's
/// `entry` / `do` / `exit` action, and an `end` feature that is not a
/// port. Such a member is a compartment row of its owner that says its
/// role, in a section of its own, rather than a node of its own.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum Role {
    Subject,
    Actor,
    Stakeholder,
    Objective,
    Return,
    Result,
    Assume,
    Require,
    Frame,
    Verify,
    Include,
    Entry,
    Do,
    Exit,
    End,
}

impl Role {
    /// The structured graph's spelling of the role — also the keyword
    /// that leads the member's compartment line, except a result's,
    /// which its expression spells alone.
    pub(crate) fn as_str(self) -> &'static str {
        match self {
            Role::Subject => "subject",
            Role::Actor => "actor",
            Role::Stakeholder => "stakeholder",
            Role::Objective => "objective",
            Role::Return => "return",
            Role::Result => "result",
            Role::Assume => "assume",
            Role::Require => "require",
            Role::Frame => "frame",
            Role::Verify => "verify",
            Role::Include => "include",
            Role::Entry => "entry",
            Role::Do => "do",
            Role::Exit => "exit",
            Role::End => "end",
        }
    }

    /// The compartment a row of this role is filed under.
    pub(crate) fn section(self) -> &'static str {
        match self {
            Role::Subject => "subject",
            Role::Actor => "actors",
            Role::Stakeholder => "stakeholders",
            Role::Objective => "objective",
            Role::Return => "return",
            Role::Result => "result",
            Role::Assume => "assume constraints",
            Role::Require => "require constraints",
            Role::Frame => "frames",
            Role::Verify => "verifies",
            Role::Include => "includes",
            Role::Entry | Role::Do | Role::Exit => "state actions",
            Role::End => "ends",
        }
    }

    /// A role whose owned member hides the inherited one, whatever their
    /// names, where a card shows inherited rows: a subject, objective,
    /// return parameter or result expression redefines the one its owner
    /// would inherit. A state's entry, do and exit actions are also one
    /// each ([`Self::one_of`]), but an owned one hides no inherited one.
    pub(crate) fn singular(self) -> bool {
        matches!(
            self,
            Role::Subject | Role::Objective | Role::Return | Role::Result
        )
    }

    /// A role an owner owns one member of at most: validation refuses a
    /// second subject (`validate…OnlyOneSubject`), objective, return or
    /// result (`validateFunctionResult…Membership`), and a second entry,
    /// do or exit action (`validateState…SubactionKind`). An empty member
    /// of such a role is still a row of the graph ([`RowParts::draws`]).
    pub(crate) fn one_of(self) -> bool {
        self.singular() || matches!(self, Role::Entry | Role::Do | Role::Exit)
    }
}

/// The [`Role`] that `e`'s introduction into its owner gives it — read
/// off its owning membership, its metaclass (`include`), or its `end`
/// flag. A satisfaction's members keep their own rendering: the subject
/// of `satisfy R by x` binds the satisfying feature rather than
/// declaring one.
pub(crate) fn member_role(r: &mut ResolvedModel, e: ElementRef) -> Option<Role> {
    let role = match r.owning_membership_type(e)? {
        "SubjectMembership" => Role::Subject,
        "ActorMembership" => Role::Actor,
        "StakeholderMembership" => Role::Stakeholder,
        "ObjectiveMembership" => Role::Objective,
        "ReturnParameterMembership" => Role::Return,
        "ResultExpressionMembership" => Role::Result,
        "RequirementConstraintMembership" => match r.owning_membership_kind(e) {
            Some("assumption") => Role::Assume,
            _ => Role::Require,
        },
        "FramedConcernMembership" => Role::Frame,
        "RequirementVerificationMembership" => Role::Verify,
        "StateSubactionMembership" => match r.owning_membership_kind(e) {
            Some("entry") => Role::Entry,
            Some("do") => Role::Do,
            Some("exit") => Role::Exit,
            _ => return None,
        },
        _ if r.element_type(e) == "IncludeUseCaseUsage" => Role::Include,
        // Port ends draw as the ports they are.
        _ if r.element_type(e) != "PortUsage" && r.prefix_keywords(e).contains(&"end") => Role::End,
        _ => return None,
    };
    let satisfied = r
        .owner(e)
        .is_some_and(|o| r.element_type(o) == "SatisfyRequirementUsage");
    (!satisfied).then_some(role)
}

/// The declared direction of a port's directed feature (`in item fuel`,
/// `out attribute pressure`), which is a row of the port's card in a
/// compartment of its own; `None` for every other member. A nested port
/// stays a port, and the directed features of anything but a port keep
/// the rows they have.
pub(crate) fn port_feature_direction(r: &mut ResolvedModel, e: ElementRef) -> Option<&'static str> {
    if r.element_type(e) == "PortUsage" {
        return None;
    }
    let direction = match r.declared_direction(e)? {
        "in" => "in",
        "out" => "out",
        "inout" => "inout",
        _ => return None,
    };
    let owner = r.owner(e)?;
    matches!(
        r.element_type(owner),
        "PortDefinition" | "PortUsage" | "ConjugatedPortDefinition"
    )
    .then_some(direction)
}

/// How many levels of nested rows a compartment line carries under it
/// (`attribute a { attribute b { attribute c; } }`, an objective's
/// `require` members): a line's members that are lines themselves, to
/// this depth.
pub(crate) const ROW_DEPTH_CAP: usize = 4;

/// What one compartment row says, shared by both backends: its
/// [`Role`], a port feature's direction, its label, and the expression
/// it carries.
pub(crate) struct RowParts {
    pub(crate) role: Option<Role>,
    /// [`port_feature_direction`].
    pub(crate) direction: Option<&'static str>,
    /// `name : Type [mult]`, with its `= value` suffix when asked for and
    /// shown; a reference written as a role member (`require fueled;`,
    /// `frame safety;`, `do refuel;`) names what it references; an
    /// anonymous state action that does something (`do send …`) says
    /// what it does; a result row has none (its expression is the row).
    /// Never led by a direction: a role or a port feature's direction
    /// says it.
    pub(crate) label: String,
    /// The expression an `assume` / `require` constraint's body is (none
    /// for a reference to one), and a result row's expression.
    pub(crate) expr: Option<String>,
}

impl RowParts {
    /// Whether the row draws: with a label, or — a role member, which may
    /// be anonymous — with an expression or rows of its own. An objective
    /// always draws, its keyword alone when it is empty (`objective { doc
    /// … }`): a case has one at most, and an empty one is still the one.
    pub(crate) fn keeps(&self, nests: bool) -> bool {
        !self.label.trim().is_empty()
            || self.role == Some(Role::Objective)
            || (self.role.is_some() && (self.expr.is_some() || nests))
    }

    /// Whether the graph draws the row: as [`Self::keeps`] has it, and an
    /// empty member of a [`Role::one_of`] role too, its keyword alone: a
    /// state's `entry;` (the initial step a succession leaves), an empty
    /// `do;` or `exit;`, an untyped `subject;`. It is still the one its
    /// owner has, and an editor tells which it has by their rows. The
    /// compartment text leaves an empty one out (but for the objective),
    /// as the notation prints a state's action by what it does.
    pub(crate) fn draws(&self, nests: bool) -> bool {
        self.keeps(nests) || self.role.is_some_and(Role::one_of)
    }
}

/// [`RowParts`] of the compartment row `e`; `values` asks for the `= value`
/// suffix (still subject to [`VizOptions::show_values`]).
pub(crate) fn row_parts(
    r: &mut ResolvedModel,
    opts: &VizOptions,
    e: ElementRef,
    values: bool,
) -> RowParts {
    let role = member_role(r, e);
    let direction = port_feature_direction(r, e);
    let mut label = if role == Some(Role::Result) {
        String::new()
    } else {
        usage_label(r, e)
    };
    // An `end` names no reference: a connector's own ends (`connect a to
    // b`, `first a then b`) are anonymous references, rows of nothing.
    let references = role.is_some_and(|role| !matches!(role, Role::Result | Role::End));
    if references && display_name(r, e).is_none() {
        if let Some(name) = referenced_name(r, e) {
            label = named_label(name, &label);
        }
    }
    if references && label.trim().is_empty() {
        label = state_action_label(r, e).unwrap_or_default();
    }
    if values && opts.show_values && role != Some(Role::Result) {
        if let Some(value) = value_suffix(r, e, opts.value_units) {
            label.push(' ');
            label.push_str(&value);
        }
    }
    let expr = role.and_then(|role| role_expr(r, e, role));
    RowParts {
        role,
        direction,
        label,
        expr,
    }
}

/// The name an anonymous role member or reference goes by: the feature
/// it references, as a dotted chain (`require fueled;` → `fueled`, `do
/// a.b;` → `a.b`), or — a reference that did not resolve in full — as
/// written, its names spelled as labels spell names (`do 'provide
/// power';` → `provide power`, `perform tank.drain;` → `tank.drain`).
pub(crate) fn referenced_name(r: &mut ResolvedModel, e: ElementRef) -> Option<String> {
    if let Some(spelling) = r.unresolved_referenced_feature(e) {
        let label = spelling_label(&spelling);
        return (!label.is_empty()).then_some(label);
    }
    for chain in r.referenced_features(e) {
        let label = chain_label(r, &chain);
        if !label.is_empty() {
            return Some(label);
        }
    }
    None
}

/// The feature chains `e` references (`perform a.b`, `exhibit s`), one
/// per reference, when its reference resolved in full. A chain cut short
/// at an unresolved link gives none: its resolved prefix (`tank` of
/// `perform tank.drain;`) is not what it references, so no edge goes
/// there; [`referenced_name`] reads it as written.
pub(crate) fn resolved_references(r: &mut ResolvedModel, e: ElementRef) -> Vec<Vec<ElementRef>> {
    if r.unresolved_referenced_feature(e).is_some() {
        return Vec::new();
    }
    r.referenced_features(e)
}

/// [`usage_label`] for a usage drawn as a node of its own. An anonymous
/// one whose reference did not resolve in full is named as written
/// (`perform 'warm up';` → `warm up`, `perform tank.drain;` →
/// `tank.drain`): no «keyword» edge can say what it references
/// ([`resolved_references`]), so its label does. One whose reference
/// resolved reads as before, as does a connector's end, which names no
/// reference resolved or not (`connect a.p to b.q`), as its row would
/// not.
pub(crate) fn node_usage_label(r: &mut ResolvedModel, e: ElementRef) -> String {
    let label = usage_label(r, e);
    if display_name(r, e).is_some() || r.owning_membership_type(e) == Some("EndFeatureMembership") {
        return label;
    }
    match r
        .unresolved_referenced_feature(e)
        .map(|s| spelling_label(&s))
    {
        Some(name) if !name.is_empty() => named_label(name, &label),
        _ => label,
    }
}

/// An anonymous member's `label` with the name it goes by standing where
/// its own name would, before the rest of the label (`include 'add
/// fuel'[0..*]` → `add fuel [0..*]`, `: Fuel` → `fuel : Fuel`).
fn named_label(name: String, label: &str) -> String {
    match label.chars().next() {
        None => name,
        Some(':') => format!("{name} {label}"),
        Some(_) => format!("{name}{label}"),
    }
}

/// A reference's written spelling with its names unquoted, as labels
/// spell names: `::` between the segments of a qualified name, `.`
/// between the links of a feature chain (`'provide power'` → `provide
/// power`, `tank.'fuel level'` → `tank.fuel level`).
fn spelling_label(spelling: &str) -> String {
    let mut links = Vec::new();
    let mut link = String::new();
    let mut quoted = false;
    let mut chars = spelling.chars();
    while let Some(c) = chars.next() {
        match c {
            '\\' if quoted => {
                link.push(c);
                link.extend(chars.next());
            }
            '\'' => {
                quoted = !quoted;
                link.push(c);
            }
            '.' if !quoted => links.push(std::mem::take(&mut link)),
            _ => link.push(c),
        }
    }
    links.push(link);
    links
        .iter()
        .map(|link| sysmlv2_syntax::name::split_canonical(link.trim()).join("::"))
        .collect::<Vec<_>>()
        .join(".")
}

/// The label of an anonymous state action that references nothing: what
/// it does — the steps of a block (`do action { sweep; polish; }` →
/// `sweep; polish`), or its kind (`do send …` → `send action`). An empty
/// one (`entry;`) has none. The graph's state-action rows and the
/// PlantUML state view's `entry / …` lines share it.
pub(crate) fn state_action_label(r: &mut ResolvedModel, e: ElementRef) -> Option<String> {
    if r.owning_membership_type(e) != Some("StateSubactionMembership") {
        return None;
    }
    let steps = inline_label(&behavior::subaction_steps(r, e));
    if !steps.is_empty() {
        return Some(steps);
    }
    let ty = r.element_type(e);
    (!matches!(ty, "ActionUsage" | "PerformActionUsage")).then(|| stereotype(ty))
}

/// The expression a role row carries, printed as written (units in their
/// brackets) on one line: an `assume` / `require` constraint's own body
/// expression, and a result row's expression — the result expression its
/// owner's body ends with.
fn role_expr(r: &mut ResolvedModel, e: ElementRef, role: Role) -> Option<String> {
    let body = match role {
        Role::Assume | Role::Require => e,
        Role::Result => r.owner(e)?,
        _ => return None,
    };
    let expr = r.result_expression(body)?;
    let dialect = r.unit_dialect(r.unit_of(e)).unwrap_or(Dialect::Sysml);
    let text = inline_label(&sysmlv2_syntax::print::print_expr_source(&expr, dialect));
    (!text.is_empty()).then_some(text)
}

/// The members row `e` nests under it: its owned members that are rows
/// themselves (an attribute's attributes, an objective's `require` and
/// `verify` members), metadata left out. An `assume` / `require` row
/// carries its body's result expression as its expression, not as a row;
/// a result row is its expression and nests nothing.
pub(crate) fn nested_row_members(
    r: &mut ResolvedModel,
    show_metadata: bool,
    e: ElementRef,
    role: Option<Role>,
) -> Vec<ElementRef> {
    if role == Some(Role::Result) {
        return Vec::new();
    }
    let carries_body = matches!(role, Some(Role::Assume | Role::Require));
    let metas = r.metadata_of(e);
    let mut out = Vec::new();
    for c in r.owned_members(e) {
        if metas.contains(&c) || !matches!(classify(r, show_metadata, c), Kind::Line) {
            continue;
        }
        if carries_body && member_role(r, c) == Some(Role::Result) {
            continue;
        }
        out.push(c);
    }
    out
}

/// The text of `e`'s compartment line in the PlantUML tree, its pieces
/// sanitized but the line not yet finished ([`finish_line`]): a plain
/// row reads as its label (`mass : Real = 3`), a port's directed feature
/// leads with its direction (`in fuel : Fuel`), and a role member with
/// its keyword (`subject vehicle : Vehicle`, `entry warm`, `end car :
/// Vehicle`), spelling the rows it nests and a constraint's expression
/// in braces (`require underLimit { vehicle.mass <= limit }`, `objective
/// { verify massReq }`); a result is spelled by its expression alone.
/// `None` when the row does not draw.
fn line_text(
    r: &mut ResolvedModel,
    opts: &VizOptions,
    e: ElementRef,
    values: bool,
    depth: usize,
) -> Option<String> {
    let parts = row_parts(r, opts, e, values);
    let Some(role) = parts.role else {
        if parts.label.trim().is_empty() {
            return None;
        }
        let text = clean_text(&parts.label);
        return Some(match parts.direction {
            Some(direction) => format!("{direction} {text}"),
            None => text,
        });
    };
    let mut body = Vec::new();
    if depth < ROW_DEPTH_CAP {
        for c in nested_row_members(r, opts.show_metadata, e, Some(role)) {
            if let Some(text) = line_text(r, opts, c, values, depth + 1) {
                body.push(text.trim().to_string());
            }
        }
    }
    if !parts.keeps(!body.is_empty()) {
        return None;
    }
    if role == Role::Result {
        return parts.expr.map(|expr| clean_text(&expr));
    }
    if let Some(expr) = &parts.expr {
        body.push(clean_text(expr));
    }
    let mut line = role.as_str().to_string();
    let label = clean_text(&parts.label);
    if !label.trim().is_empty() {
        line.push(' ');
        line.push_str(label.trim());
    }
    if !body.is_empty() {
        line.push_str(" { ");
        line.push_str(&body.join("; "));
        line.push_str(" }");
    }
    Some(line)
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

    fn classify(&mut self, e: ElementRef) -> Kind {
        classify(self.r, self.opts.show_metadata, e)
    }

    fn indent(&mut self, depth: usize) {
        for _ in 0..depth {
            self.body.push_str("  ");
        }
    }

    fn value_suffix(&mut self, e: ElementRef) -> Option<String> {
        if !self.opts.show_values {
            return None;
        }
        value_suffix(self.r, e, self.opts.value_units)
    }

    /// Compartment lines for a node, sanitized: attribute-family members,
    /// role members and a port's directed features (see [`line_text`]);
    /// returns the members that need their own nodes. With
    /// `show_inherited`, members one explicit typing / specialization hop
    /// away add `^`-prefixed lines without values (own names shadow, and
    /// so does an own member of a role the owner has one of).
    fn split_members(&mut self, e: ElementRef) -> (Vec<String>, Vec<ElementRef>) {
        let mut lines = Vec::new();
        let mut children = Vec::new();
        let mut own_names: Vec<String> = Vec::new();
        let mut own_roles: Vec<Role> = Vec::new();
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
                    own_roles.extend(member_role(self.r, m).filter(|role| role.singular()));
                    if let Some(text) = line_text(self.r, self.opts, m, true, 0) {
                        lines.push(finish_line(&text));
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
                    // by the names the lines read, borrowed ones included
                    let shadowed = display_name(self.r, m).is_some_and(|n| own_names.contains(&n))
                        || member_role(self.r, m).is_some_and(|role| own_roles.contains(&role));
                    if shadowed {
                        continue;
                    }
                    if let Some(text) = line_text(self.r, self.opts, m, false, 0) {
                        lines.push(finish_line(&format!("^{text}")));
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
            node_usage_label(self.r, e)
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
                let _ = writeln!(self.body, "{line}");
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
        // A nameless redefinition of a feature chain (`:>> chassis.mass`)
        // borrows the chain's spelling: the chain itself has no name.
        if let Some(links) = redefined_chain(r, cur) {
            return Some(links.join("."));
        }
        cur = *r.redefinition_targets(cur).first()?;
    }
    None
}

/// The redefined chain of a nameless redefining feature, as its links'
/// names (`["chassis", "mass"]`), when it redefines a feature chain and no
/// feature by name (`:>> total, chassis.mass` borrows `total`, as its
/// effective name does). A link without a name of its own borrows one
/// through its redefinitions, as a compartment line does.
pub(crate) fn redefined_chain(r: &mut ResolvedModel, e: ElementRef) -> Option<Vec<String>> {
    if r.element_name(e).is_some() || !r.redefinition_targets(e).is_empty() {
        return None;
    }
    let links = r.redefined_chains(e).into_iter().next()?;
    links
        .into_iter()
        .map(|link| {
            let mut cur = link;
            for _ in 0..32 {
                if let Some(n) = r.element_name(cur) {
                    return Some(n.to_string());
                }
                cur = *r.redefinition_targets(cur).first()?;
            }
            None
        })
        .collect()
}

/// Whether `e` is a nameless redefining feature — a compartment line that
/// borrows its redefined feature's name (or chain) for its label.
pub(crate) fn is_nameless_redefinition(r: &mut ResolvedModel, e: ElementRef) -> bool {
    r.element_name(e).is_none()
        && (!r.redefinition_targets(e).is_empty() || !r.redefined_chains(e).is_empty())
}

/// The types a label shows, and whether they were derived rather than
/// written: the explicit typings, else the first found through
/// redefinitions (`part redefines brewing;` keeps the redefined feature's
/// type, as KerML derives the redefining feature's /type). A nameless
/// redefinition also looks through subsettings and a chain's last link
/// (`:>> chassis.mass` finds `mass :> ISQ::mass` and its `MassValue`),
/// breadth-first; named features keep the redefinition walk alone, so
/// their labels do not change.
pub(crate) fn label_types(r: &mut ResolvedModel, e: ElementRef) -> (Vec<ElementRef>, bool) {
    let typings = r.typings(e);
    if !typings.is_empty() {
        return (typings, false);
    }
    let mut cur = e;
    for _ in 0..8 {
        let Some(&t) = r.redefinition_targets(cur).first() else {
            break;
        };
        let typings = r.typings(t);
        if !typings.is_empty() {
            return (typings, true);
        }
        cur = t;
    }
    // a named feature follows a chain it redefines (`part cb :>> chassis.body`)
    // but not its subsetting, as a name declares a feature of its own
    if r.element_name(e).is_some() {
        for chain in r.redefined_chains(e) {
            if let Some(&last) = chain.last() {
                let (typings, _) = label_types(r, last);
                if !typings.is_empty() {
                    return (typings, true);
                }
            }
        }
        return (Vec::new(), false);
    }
    let mut queue = std::collections::VecDeque::from([e]);
    let mut seen = HashSet::new();
    while let Some(f) = queue.pop_front() {
        if seen.len() >= 64 {
            break;
        }
        if !seen.insert(f) {
            continue;
        }
        if f != e {
            let typings = r.typings(f);
            if !typings.is_empty() {
                return (typings, true);
            }
        }
        for chain in r.redefined_chains(f) {
            if let Some(&last) = chain.last() {
                queue.push_back(last);
            }
        }
        for (kind, t) in r.explicit_specializations(f) {
            if kind == "Redefinition" || kind == "Subsetting" {
                queue.push_back(t);
            }
        }
    }
    (Vec::new(), false)
}

/// `name : Type1, Type2 [mult]` — the shared label shape for usages
/// and compartment lines. Library type names still appear even
/// though library elements are never rendered as nodes.
pub(crate) fn usage_label(r: &mut ResolvedModel, e: ElementRef) -> String {
    let mut label = display_name(r, e).unwrap_or_default();
    // Explicit typings, else the type derived (see `label_types`).
    let (typings, _) = label_types(r, e);
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
/// literally, quantities in the units `units` chooses, element results
/// (enum literals, referenced usages) by name. A binding to a feature
/// that has no value to give (`subject = result;`, `= vehicle.mass`
/// unvalued) reads as written instead ([`bound_reference`]); any other
/// value that does not evaluate, an anonymous element, and the feature
/// itself (the unbound case) say nothing. Shared by the PlantUML and
/// graph backends.
pub(crate) fn value_suffix(
    r: &mut ResolvedModel,
    e: ElementRef,
    units: UnitDisplay,
) -> Option<String> {
    if !r.has_value(e) {
        return None;
    }
    let rendered = evaluated_value(r, e, units).or_else(|| bound_reference(r, e))?;
    Some(format!("= {rendered}"))
}

/// The bound value of `e` as a reference to a feature (`result`,
/// `vehicle.mass`, `Ops::'fuel level'`), printed as written on one line;
/// `None` for any other expression.
fn bound_reference(r: &mut ResolvedModel, e: ElementRef) -> Option<String> {
    fn is_reference(expr: &sysmlv2_syntax::ast::Expr) -> bool {
        match &expr.kind {
            sysmlv2_syntax::ast::ExprKind::Ref(_) => true,
            sysmlv2_syntax::ast::ExprKind::ChainStep { target, .. } => is_reference(target),
            _ => false,
        }
    }
    let (_, expr) = r.value_expr(e)?;
    if !is_reference(&expr) {
        return None;
    }
    let dialect = r.unit_dialect(r.unit_of(e)).unwrap_or(Dialect::Sysml);
    let text = inline_label(&sysmlv2_syntax::print::print_expr_source(&expr, dialect));
    (!text.is_empty()).then_some(text)
}

/// `e`'s evaluated value as [`value_suffix`] spells it, when it has one
/// worth labeling.
fn evaluated_value(r: &mut ResolvedModel, e: ElementRef, units: UnitDisplay) -> Option<String> {
    let value = r.evaluate(e).ok()?;
    let value = match units {
        UnitDisplay::AsWritten => r.value_as_written(&value).unwrap_or(value),
        _ => value,
    };
    let rendered = match value {
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
    Some(rendered)
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
    finish_line(&clean_text(s))
}

/// The text of one piece of a compartment line ([`sanitize_line`]): no
/// braces — a role line's own braces are the only ones it has, always
/// balanced and never leading — and no line breaks.
fn clean_text(s: &str) -> String {
    s.chars()
        .filter(|c| !matches!(c, '{' | '}' | '\r'))
        .map(|c| if c == '\n' { ' ' } else { c })
        .collect()
}

/// A compartment line's text, trimmed, with a leading visibility
/// character escaped ([`sanitize_line`]).
fn finish_line(s: &str) -> String {
    let trimmed = s.trim().to_string();
    match trimmed.chars().next() {
        Some('-') | Some('+') | Some('#') | Some('~') => format!("\\{trimmed}"),
        _ => trimmed,
    }
}
