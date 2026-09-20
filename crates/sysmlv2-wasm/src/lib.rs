//! WASM/JS binding for the sysmlv2 stack: the browser
//! face of `sysmlv2_transform::Session` + `sysmlv2_viz`, mirroring the
//! Python binding's generation-guarded handle discipline.
//!
//! Boundary convention: scalars and handles cross as themselves;
//! everything structured crosses as **JSON strings** (sources in,
//! findings/units/values out). That keeps the crate free of JS-only
//! types, so the whole binding compiles and tests natively — the wasm
//! target changes the ABI, not the logic. The standard library arrives
//! as in-memory sources (`Library::sources`), never from a filesystem.
//!
//! Handle discipline: an [`Element`] is minted against one committed
//! state of a session (a *generation*). Loading a library rebuilds the
//! session and invalidates outstanding handles — using one afterwards
//! errors instead of silently denoting the wrong element.

use std::collections::HashMap;

use serde::{Deserialize, Serialize};
use serde_json::json;
use wasm_bindgen::prelude::*;

use sysmlv2_model::check::ConstraintVerdict;
use sysmlv2_model::eval::Value as EvalValue;
use sysmlv2_model::json::ElementRef;
use sysmlv2_solve::{PropagateConfig, PropagateOutcome};
use sysmlv2_syntax::parser::parse_expression;
use sysmlv2_syntax::span::LineIndex;
use sysmlv2_transform::{Indent, Library, Session as TSession, check_sources_with_library};

/// Stack reserved for the module, in bytes (16 MiB).
///
/// The toolkit's passes recurse, and each bounds itself by a depth that
/// stops unbounded input with a diagnostic instead of a crash: the parser
/// at [`sysmlv2_syntax::parser::MAX_NESTING`] levels of bodies and
/// expressions, the lift at [`sysmlv2_model::lift::MAX_LIFT_DEPTH`]
/// ownership steps. A bound only does that where the stack holds it. On
/// this target it would otherwise be the linker's default megabyte — too
/// little for either bound, and running out of stack here is a trap the
/// host cannot report as a finding, not an unwind.
///
/// So the module reserves its own, with room to spare: the deepest
/// optimized parse measures in single megabytes and the deepest lift
/// under three. `npm/build.mjs` reads this number and passes it to the
/// linker; `tests/stack.rs` holds the two together.
///
/// This is address space in the module's linear memory, not resident
/// pages, and it sits far below the memory cap the same build applies.
pub const WASM_STACK_BYTES: usize = 16777216;

/// The host console, for the panic hook below.
#[cfg(target_arch = "wasm32")]
#[wasm_bindgen]
extern "C" {
    #[wasm_bindgen(js_namespace = console, js_name = error)]
    fn console_error(message: &str);
}

/// Runs once when the module is instantiated: routes every panic
/// report to the host's `console.error`. On this target a panic has no
/// stderr to print to and then traps the instance — the host sees a
/// bare `RuntimeError: unreachable` — so without the hook the reason
/// is lost. The trapped instance is not recoverable (a session may be
/// half-mutated): a host that catches a `RuntimeError` must discard
/// the module instance and instantiate the module again.
#[cfg(target_arch = "wasm32")]
#[wasm_bindgen(start)]
pub fn install_panic_hook() {
    std::panic::set_hook(Box::new(|info| console_error(&info.to_string())));
}

/// `[{name, text}]` — the JSON shape sources cross the boundary in.
#[derive(Deserialize)]
struct SourceIn {
    name: String,
    text: String,
}

/// Resolve an edit target: a `::`-qualified name, or
/// `@<interchange-id>` for elements without one (anonymous connectors,
/// unnamed actions). Library elements are rejected here — they are
/// read-only, and letting one through would reach for source text the
/// session does not hold.
fn resolve_edit_target(inner: &mut TSession, name: &str) -> Result<ElementRef, String> {
    let e = if let Some(id) = name.strip_prefix('@') {
        inner
            .resolved()
            .element_by_id(id)
            .ok_or_else(|| format!("element not found: {name}"))?
    } else {
        inner
            .resolved()
            .resolve_qualified(name)
            .ok_or_else(|| format!("element not found: {name}"))?
    };
    if inner.resolved().is_library_element(e) {
        return Err(format!("{name} is a library element (read-only)"));
    }
    Ok(e)
}

/// One metadata usage as `viewInfo` reports it: its (first) type and
/// the evaluated values of the features its body declares.
struct MetadataValues {
    ty: Option<String>,
    values: Vec<(String, EvalValue)>,
}

fn parse_sources(json: &str) -> Result<Vec<(String, String)>, String> {
    let sources: Vec<SourceIn> =
        serde_json::from_str(json).map_err(|e| format!("sources must be [{{name, text}}]: {e}"))?;
    // A unit's name is its identity everywhere downstream (findings,
    // splices, the lifted root namespace), so an empty one is refused
    // at the boundary, by position, instead of failing deep inside a
    // later emission.
    if let Some(i) = sources.iter().position(|s| s.name.is_empty()) {
        return Err(format!(
            "sources must be [{{name, text}}]: source {i} has an empty name"
        ));
    }
    Ok(sources.into_iter().map(|s| (s.name, s.text)).collect())
}

fn parse_library(json: &str, snapshot: Option<Vec<u8>>) -> Result<Library, String> {
    let units = parse_sources(json)?;
    Ok(match snapshot {
        Some(bytes) => Library::sources_with_snapshot(units, bytes),
        None => Library::sources(units),
    })
}

fn parse_indent(s: Option<&str>) -> Result<Indent, String> {
    match s {
        None | Some("") => Ok(Indent::default()),
        Some("tabs") => Ok(Indent::Tabs),
        Some(n) => n
            .parse::<u8>()
            .ok()
            .filter(|n| (1..=16).contains(n))
            .map(Indent::Spaces)
            .ok_or_else(|| format!("indent must be \"tabs\" or a space count 1–16, got {n:?}")),
    }
}

/// One verified constraint's tally bucket and human verdict line — the
/// CLI's rendering minus the solver arms (the binding runs the
/// solverless tier, so a Z3 conclusion never occurs here). Wording
/// matches `sysmlv2 verify` exactly so the IDE and the CLI cannot
/// disagree.
fn verify_status(
    verdict: &ConstraintVerdict,
    propagate: Option<&PropagateOutcome>,
) -> (&'static str, String) {
    match verdict {
        ConstraintVerdict::Satisfied => ("satisfied", "satisfied".to_string()),
        ConstraintVerdict::Violated => ("violated", "VIOLATED".to_string()),
        ConstraintVerdict::Undecided(why) => match propagate {
            Some(PropagateOutcome::Satisfied) => (
                "satisfied",
                "satisfied (propagation: holds for all values in the narrowed ranges)".to_string(),
            ),
            Some(PropagateOutcome::Violated) => (
                "violated",
                "VIOLATED (propagation: false for all values in the narrowed ranges)".to_string(),
            ),
            Some(PropagateOutcome::Unsatisfiable) => (
                "violated",
                "VIOLATED (propagation: domains contract to empty — unsatisfiable)".to_string(),
            ),
            Some(PropagateOutcome::Unsupported(m)) => {
                ("undecided", format!("undecided ({why}; propagation: {m})"))
            }
            Some(PropagateOutcome::Undecided) | None => ("undecided", format!("undecided ({why})")),
            // A conclusion this build does not recognize stays undecided.
            Some(_) => ("undecided", format!("undecided ({why})")),
        },
    }
}

/// An opaque handle to one element of a session's resolved model.
#[wasm_bindgen]
#[derive(Clone, Copy)]
pub struct Element {
    e: ElementRef,
    gen: u64,
}

/// Diagram options as JSON, mirroring the Python `to_plantuml`
/// signature: `{element?, roots?, view?, horizontal?, showValues?,
/// showNotes?, showMetadata?, showInherited?, showLib?, showImported?,
/// lineStyle?, stdColor?, linkTemplate?}` — all optional, defaults
/// match Python. `roots` restricts an all-roots diagram to the named
/// top-level elements (ignored when `element` scopes to one subtree).
#[derive(Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct PlantumlOpts {
    element: Option<String>,
    #[serde(default)]
    roots: Option<Vec<String>>,
    /// Summary emission for large scopes (`toGraph`, tree view; ignored
    /// by `toPlantuml`): containers outside `open` emit as one node
    /// with counts. See `SummaryIn`.
    #[serde(default)]
    summary: Option<SummaryIn>,
    #[serde(default = "default_view")]
    view: String,
    #[serde(default)]
    horizontal: bool,
    #[serde(default = "yes")]
    show_values: bool,
    #[serde(default = "yes")]
    show_notes: bool,
    #[serde(default = "yes")]
    show_metadata: bool,
    #[serde(default)]
    show_inherited: bool,
    #[serde(default)]
    show_lib: bool,
    #[serde(default)]
    show_imported: bool,
    line_style: Option<String>,
    #[serde(default)]
    std_color: bool,
    link_template: Option<String>,
}

/// `{open: [selector…], noteBudget, leafBudget, unbounded: [selector…]}`:
/// which containers emit their members, how many notes draw as cards
/// per cluster, how many members draw per open container, and which
/// open containers draw every member regardless (a selector that does
/// not resolve is ignored).
#[derive(Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct SummaryIn {
    #[serde(default)]
    open: Vec<Selector>,
    #[serde(default)]
    unbounded: Vec<Selector>,
    #[serde(default = "default_note_budget")]
    note_budget: usize,
    #[serde(default = "default_leaf_budget")]
    leaf_budget: usize,
}

fn default_note_budget() -> usize {
    200
}

fn default_leaf_budget() -> usize {
    500
}

/// An element selector: a `::`-qualified name, or `{elementId}` for
/// elements without a resolvable name.
#[derive(Clone, Deserialize, Serialize)]
#[serde(untagged)]
enum Selector {
    Name(String),
    Id {
        #[serde(rename = "elementId")]
        element_id: String,
    },
}

fn resolve_selector(
    r: &mut sysmlv2_model::json::ResolvedModel,
    sel: &Selector,
) -> Option<ElementRef> {
    match sel {
        Selector::Name(name) => r.resolve_qualified(name),
        Selector::Id { element_id } => r.element_by_id(element_id),
    }
}

fn default_view() -> String {
    "tree".to_string()
}

fn yes() -> bool {
    true
}

/// The `view` and `lineStyle` vocabularies are the diagram crate's own
/// (`tree`, `interconnection` / `ic`, `state`, `action`, `sequence` /
/// `seq`, `case`, `mixed`; `polyline`, `ortho`), parsed and spelled
/// through it so this surface cannot drift from the others.
fn parse_view(name: &str) -> Result<sysmlv2_viz::View, String> {
    name.parse()
        .map_err(|e: sysmlv2_viz::ParseOptionError| e.to_string())
}

/// A view's canonical spelling (its `--view` value without aliases).
fn view_name(view: sysmlv2_viz::View) -> &'static str {
    view.as_str()
}

/// An absent `lineStyle` is the emitter's default splines.
fn parse_line_style(name: Option<&str>) -> Result<sysmlv2_viz::LineStyle, String> {
    match name {
        None => Ok(sysmlv2_viz::LineStyle::Default),
        Some(s) => s
            .parse()
            .map_err(|e: sysmlv2_viz::ParseOptionError| e.to_string()),
    }
}

/// The memoized line index of a unit, built on first use; a unit whose
/// source the session does not hold (a library unit) indexes as empty.
fn unit_line_index<'a>(
    indexes: &'a mut HashMap<usize, LineIndex>,
    session: &TSession,
    unit: usize,
) -> &'a LineIndex {
    indexes
        .entry(unit)
        .or_insert_with(|| LineIndex::new(session.source(unit).unwrap_or("")))
}

/// One edit-batch operation as JSON (the `edit` method takes an array):
/// `{op: "rename", target, newName}` · `{op: "setFeatureValue", target,
/// expr}` · `{op: "setFeatureType", target, type}` (replace the written
/// `: T` clause in place, or add one where none exists) · `{op:
/// "insertMember", owner, text}` · `{op: "insertTopLevel", unit, text}`
/// · `{op: "remove", target}` · `{op: "replaceMember", target, text}`
/// (identity-preserving update: swaps the declaration for exactly one
/// parsed member, respells outside references on a declared-name
/// change, and judges validity on the post-edit model — no pre-state
/// outside-reference refusal) · `{op: "moveMember", target, newOwner?,
/// index?}` (omitted `newOwner` = reorder within the current owner;
/// `index` = slot among the destination's current members, self
/// excluded, omitted = append) · `{op: "addUnit", unit}` (create a
/// new, empty unit; refuses a name the session already holds — ops
/// plan against the pre-commit state, so inserting into the born unit
/// belongs in a following batch). Element references
/// (`target`/`owner`/`newOwner`) are `::`-qualified names against the
/// current session state; `type` is a type spelling as written (name or
/// qualified name).
#[derive(Deserialize)]
#[serde(tag = "op", deny_unknown_fields)]
enum EditOpIn {
    #[serde(rename = "rename", rename_all = "camelCase")]
    Rename { target: String, new_name: String },
    #[serde(rename = "setFeatureValue")]
    SetFeatureValue { target: String, expr: String },
    #[serde(rename = "setFeatureType")]
    SetFeatureType {
        target: String,
        #[serde(rename = "type")]
        ty: String,
    },
    #[serde(rename = "insertMember")]
    InsertMember { owner: String, text: String },
    #[serde(rename = "insertTopLevel")]
    InsertTopLevel { unit: String, text: String },
    #[serde(rename = "addUnit")]
    AddUnit { unit: String },
    #[serde(rename = "remove")]
    Remove { target: String },
    #[serde(rename = "replaceMember")]
    ReplaceMember { target: String, text: String },
    #[serde(rename = "moveMember", rename_all = "camelCase")]
    MoveMember {
        target: String,
        #[serde(default)]
        new_owner: Option<String>,
        #[serde(default)]
        index: Option<u32>,
    },
}

/// [`EditOpIn`] with element references resolved against the current
/// session state.
enum ResolvedOp {
    Rename(ElementRef, String),
    SetFeatureValue(ElementRef, String),
    SetFeatureType(ElementRef, String),
    InsertMember(ElementRef, String),
    InsertTopLevel(String, String),
    AddUnit(String),
    Remove(ElementRef),
    ReplaceMember(ElementRef, String),
    MoveMember(ElementRef, ElementRef, Option<usize>),
}

/// A set of model sources (text or interchange JSON) with their resolved
/// model — `sysmlv2_transform::Session` behind a JS-shaped API.
#[wasm_bindgen]
pub struct Session {
    inner: TSession,
    gen: u64,
}

impl Session {
    fn guard(&self, e: &Element) -> Result<(), String> {
        if e.gen != self.gen {
            return Err(
                "stale handle: the session was rebuilt since it was minted (re-resolve)"
                    .to_string(),
            );
        }
        Ok(())
    }

    /// Resolve a diagram's `roots` selection (`::`-qualified top-level
    /// names) to element handles for the emitter; `None`/empty leaves
    /// the diagram at every top-level element.
    fn resolve_roots(
        &mut self,
        names: Option<&[String]>,
    ) -> Result<Option<Vec<ElementRef>>, String> {
        let Some(names) = names.filter(|n| !n.is_empty()) else {
            return Ok(None);
        };
        let mut refs = Vec::with_capacity(names.len());
        for name in names {
            let e = self
                .inner
                .resolved()
                .resolve_qualified(name)
                .ok_or_else(|| format!("element not found: {name}"))?;
            refs.push(e);
        }
        Ok(Some(refs))
    }

    /// Parse a diagram options document (absent or empty = `{}`, so
    /// serde's field defaults apply uniformly) and resolve its scope
    /// against the current model — the one path both diagram emitters
    /// take, so they accept the same options and read a name the same
    /// way. Returns the emitter options with `roots` filled in, and
    /// the subtree root. A view usage named as `element` directs its
    /// own diagram: the elements are what it exposes (filter conditions
    /// applied), as the CLI renders it, while the requested view kind
    /// stands — callers name it explicitly here. An empty exposure
    /// comes back as `roots: Some([])`: an explicit empty selection,
    /// never the whole model (which the emitters draw for a missing
    /// selection).
    fn diagram_request(
        &mut self,
        opts_json: Option<&str>,
    ) -> Result<
        (
            sysmlv2_viz::VizOptions,
            Option<ElementRef>,
            Option<SummaryIn>,
        ),
        String,
    > {
        let opts: PlantumlOpts =
            serde_json::from_str(opts_json.filter(|s| !s.is_empty()).unwrap_or("{}"))
                .map_err(|e| format!("bad options: {e}"))?;
        let view = parse_view(&opts.view)?;
        let line_style = parse_line_style(opts.line_style.as_deref())?;
        let mut root = opts
            .element
            .as_deref()
            .map(|name| {
                self.inner
                    .resolved()
                    .resolve_qualified(name)
                    .ok_or_else(|| format!("element not found: {name}"))
            })
            .transpose()?;
        let mut roots = self.resolve_roots(opts.roots.as_deref())?;
        if let Some(e) = root {
            if let Some((_, exposed)) = sysmlv2_viz::view_directed(self.inner.resolved(), e) {
                roots = Some(exposed);
                root = None;
            }
        }
        let viz = sysmlv2_viz::VizOptions::default()
            .with_direction(if opts.horizontal {
                sysmlv2_viz::Direction::LeftToRight
            } else {
                sysmlv2_viz::Direction::TopToBottom
            })
            .with_show_values(opts.show_values)
            .with_view(view)
            .with_show_notes(opts.show_notes)
            .with_show_metadata(opts.show_metadata)
            .with_show_inherited(opts.show_inherited)
            .with_show_lib(opts.show_lib)
            .with_show_imported(opts.show_imported)
            .with_line_style(line_style)
            .with_std_color(opts.std_color)
            .with_link_template(opts.link_template)
            .with_roots(roots);
        Ok((viz, root, opts.summary))
    }

    fn value_to_json(&mut self, v: &EvalValue) -> serde_json::Value {
        match v {
            EvalValue::Boolean(b) => json!(b),
            EvalValue::Integer(i) => json!(i),
            // A JSON number carries an exact rational only when its
            // decimal spelling is the value; anything else crosses as an
            // explicit fraction with a double approximation alongside.
            EvalValue::Rational(r) if r.json_number_is_exact() => json!(r.to_f64()),
            EvalValue::Rational(r) => {
                let (n, d) = r.to_string_parts();
                json!({ "@rational": format!("{n}/{d}"), "approx": r.to_f64() })
            }
            EvalValue::Real(f) => json!(f),
            EvalValue::String(s) => json!(s),
            EvalValue::Indeterminate => json!({ "@indeterminate": true }),
            EvalValue::Element(e) | EvalValue::Unbound(e) | EvalValue::UnboundMember(e) => json!({
                "@element": self.inner.resolved().element_id(*e).to_string(),
                "qualifiedName": self.inner.resolved().element_qualified_name(*e),
            }),
            EvalValue::Quantity(n, unit) => json!({
                "value": self.value_to_json(n),
                "unit": unit.display(),
            }),
            EvalValue::Instance {
                ty_name, fields, ..
            } => {
                let mut obj = serde_json::Map::new();
                obj.insert("@type".to_string(), json!(ty_name));
                for (name, value) in fields {
                    obj.insert(name.clone(), self.value_to_json(value));
                }
                serde_json::Value::Object(obj)
            }
            EvalValue::Sequence(items) => {
                serde_json::Value::Array(items.iter().map(|i| self.value_to_json(i)).collect())
            }
        }
    }
}

/// An immutable library graph reusable across session builds and edits.
/// Prepare the final ordered source bundle once. Changed sources require a new
/// handle. Sessions retain the library independently of this handle's lifetime.
#[wasm_bindgen]
pub struct PreparedLibrary {
    inner: Library,
}

#[wasm_bindgen]
impl PreparedLibrary {
    /// Prepare library sources (JSON `[{name, text}]`) with an optional sealed
    /// resolution snapshot. Stale or corrupt snapshots fall back to source.
    #[wasm_bindgen(constructor)]
    pub fn new(sources_json: &str, snapshot: Option<Vec<u8>>) -> Result<PreparedLibrary, String> {
        Ok(Self {
            inner: Library::prepared_sources(parse_sources(sources_json)?, snapshot)
                .map_err(|e| e.to_string())?,
        })
    }
}

#[wasm_bindgen]
impl Session {
    /// Open sources against a shared prepared library in one model build.
    #[wasm_bindgen(js_name = fromSourcesWithPreparedLibrary)]
    pub fn from_sources_with_prepared_library(
        sources_json: &str,
        library: &PreparedLibrary,
    ) -> Result<Session, String> {
        Ok(Session {
            inner: TSession::from_sources_with_library(
                parse_sources(sources_json)?,
                Some(library.inner.clone()),
            )
            .map_err(|e| e.to_string())?,
            gen: 0,
        })
    }

    /// Open interchange JSON against a shared prepared library.
    #[allow(clippy::needless_pass_by_value)]
    #[wasm_bindgen(js_name = fromInterchangeJsonWithPreparedLibrary)]
    pub fn from_interchange_json_with_prepared_library(
        json: &str,
        library: &PreparedLibrary,
        indent: Option<String>,
    ) -> Result<Session, String> {
        let value = serde_json::from_str(json).map_err(|e| e.to_string())?;
        Ok(Session {
            inner: TSession::from_interchange_json_indented(
                &value,
                Some(&library.inner),
                &[],
                parse_indent(indent.as_deref())?,
            )
            .map_err(|e| e.to_string())?,
            gen: 0,
        })
    }

    /// Open compact CBOR against a shared prepared library.
    #[allow(clippy::needless_pass_by_value)]
    #[wasm_bindgen(js_name = fromCompactCborWithPreparedLibrary)]
    pub fn from_compact_cbor_with_prepared_library(
        bytes: &[u8],
        library: &PreparedLibrary,
        indent: Option<String>,
    ) -> Result<Session, String> {
        Ok(Session {
            inner: TSession::from_compact_cbor_indented(
                bytes,
                Some(&library.inner),
                parse_indent(indent.as_deref())?,
            )
            .map_err(|e| e.to_string())?,
            gen: 0,
        })
    }

    /// Attach a shared prepared library and rebuild; existing element handles
    /// become stale, just as with `loadLibrarySources`.
    #[wasm_bindgen(js_name = loadPreparedLibrary)]
    pub fn load_prepared_library(&mut self, library: &PreparedLibrary) -> Result<(), String> {
        self.inner
            .load_library_from(library.inner.clone())
            .map_err(|e| e.to_string())?;
        self.gen += 1;
        Ok(())
    }

    /// Open a session over in-memory sources: JSON `[{name, text}]`.
    /// Unit names ending in `.kerml` parse as KerML.
    #[wasm_bindgen(js_name = fromSources)]
    pub fn from_sources(sources_json: &str) -> Result<Session, String> {
        Ok(Session {
            inner: TSession::from_sources(parse_sources(sources_json)?)
                .map_err(|e| e.to_string())?,
            gen: 0,
        })
    }

    /// [`Self::from_sources`] resolved against standard-library sources
    /// (JSON `[{name, text}]`, optional sealed snapshot — see
    /// [`Self::from_interchange_json`]) in the same build. Opening a
    /// session and then calling [`Self::load_library_sources`] resolves
    /// the user units twice; this resolves them once.
    // The export boundary converts an optional string only when owned.
    #[allow(clippy::needless_pass_by_value)]
    #[wasm_bindgen(js_name = fromSourcesWithLibrary)]
    pub fn from_sources_with_library(
        sources_json: &str,
        lib_sources_json: Option<String>,
        lib_snapshot: Option<Vec<u8>>,
    ) -> Result<Session, String> {
        let lib = lib_sources_json
            .as_deref()
            .map(|s| parse_library(s, lib_snapshot))
            .transpose()?;
        Ok(Session {
            inner: TSession::from_sources_with_library(parse_sources(sources_json)?, lib)
                .map_err(|e| e.to_string())?,
            gen: 0,
        })
    }

    /// The session's check findings — the same JSON the free [`check`]
    /// returns for the session's sources and library, read off this
    /// session's build instead of a second one (no parse-stage entries:
    /// the session holds only units that parsed; without a library the
    /// resolution stages are skipped, as `check` skips them). A host
    /// that partitions its units by [`check_syntax`] and opens a
    /// session over the ones that parsed gets every stage with one
    /// resolution.
    pub fn check(&mut self) -> String {
        let findings = self.inner.check_findings();
        let indexes: HashMap<&str, LineIndex> = self
            .inner
            .units()
            .map(|(_, name, text)| (name, LineIndex::new(text)))
            .collect();
        check_findings_json(findings, &indexes)
    }

    /// Open a session over an interchange JSON document (compact or full
    /// form; Flexo `{payload, identity}` wrapping accepted). Pass
    /// standard-library sources (JSON `[{name, text}]`) to name library
    /// element ids during the lift and keep the library loaded for
    /// resolution — a library-typed payload generally needs it. An
    /// optional sealed resolution snapshot (`LibraryCache::to_bytes`,
    /// recorded against the same library sources in the same order —
    /// the stdlib bundle ships one) makes library resolution
    /// replay instead of search; stale bytes are rejected and the build
    /// falls back to a cold resolve.
    /// The optional `indent` names the indentation style for the
    /// lifted unit text: `"tabs"`, or a space count like `"4"`
    /// (default four spaces; presentation only, never identity).
    // The export boundary converts an optional string only when owned.
    #[allow(clippy::needless_pass_by_value)]
    #[wasm_bindgen(js_name = fromInterchangeJson)]
    pub fn from_interchange_json(
        json: &str,
        lib_sources_json: Option<String>,
        lib_snapshot: Option<Vec<u8>>,
        indent: Option<String>,
    ) -> Result<Session, String> {
        let value: serde_json::Value = serde_json::from_str(json).map_err(|e| e.to_string())?;
        let lib = lib_sources_json
            .as_deref()
            .map(|s| parse_library(s, lib_snapshot))
            .transpose()?;
        Ok(Session {
            inner: TSession::from_interchange_json_indented(
                &value,
                lib.as_ref(),
                &[],
                parse_indent(indent.as_deref())?,
            )
            .map_err(|e| e.to_string())?,
            gen: 0,
        })
    }

    /// Open a session over a compact-form CBOR payload (a `Uint8Array`)
    /// — the binary counterpart of [`Self::from_interchange_json`];
    /// library and indent arguments as there.
    // The export boundary converts an optional string only when owned.
    #[allow(clippy::needless_pass_by_value)]
    #[wasm_bindgen(js_name = fromCompactCbor)]
    pub fn from_compact_cbor(
        bytes: &[u8],
        lib_sources_json: Option<String>,
        lib_snapshot: Option<Vec<u8>>,
        indent: Option<String>,
    ) -> Result<Session, String> {
        let lib = lib_sources_json
            .as_deref()
            .map(|s| parse_library(s, lib_snapshot))
            .transpose()?;
        Ok(Session {
            inner: TSession::from_compact_cbor_indented(
                bytes,
                lib.as_ref(),
                parse_indent(indent.as_deref())?,
            )
            .map_err(|e| e.to_string())?,
            gen: 0,
        })
    }

    /// Resolve against standard-library sources (JSON `[{name, text}]`),
    /// optionally with a sealed resolution snapshot (see
    /// [`Self::from_interchange_json`]). Rebuilds the session:
    /// outstanding handles go stale.
    #[wasm_bindgen(js_name = loadLibrarySources)]
    pub fn load_library_sources(
        &mut self,
        sources_json: &str,
        snapshot: Option<Vec<u8>>,
    ) -> Result<(), String> {
        self.inner
            .load_library_from(parse_library(sources_json, snapshot)?)
            .map_err(|e| e.to_string())?;
        self.gen += 1;
        Ok(())
    }

    /// Resolve a `::`-qualified name to an element handle.
    pub fn resolve(&mut self, qualified_name: &str) -> Option<Element> {
        let gen = self.gen;
        self.inner
            .resolved()
            .resolve_qualified(qualified_name)
            .map(|e| Element { e, gen })
    }

    /// Look up an interchange UUID, including unnamed and library elements.
    /// Returns no handle for malformed or absent IDs. Like name-resolved
    /// handles, the result goes stale when the session is rebuilt.
    #[wasm_bindgen(js_name = elementById)]
    pub fn element_by_id(&mut self, id: &str) -> Option<Element> {
        let gen = self.gen;
        self.inner
            .resolved()
            .element_by_id(id)
            .map(|e| Element { e, gen })
    }

    /// Evaluate an ad-hoc KerML query expression at the root namespace
    /// (the `sysmlv2 query` semantics). Returns the value as JSON;
    /// elements come back as `{"@element": id, "qualifiedName": …}`.
    pub fn query(&mut self, expr: &str) -> Result<String, String> {
        let parsed = parse_expression(expr);
        let Some(ast) = parsed.expr else {
            let msg = parsed
                .diagnostics
                .first()
                .map(|d| d.message.clone())
                .unwrap_or_else(|| "not an expression".into());
            return Err(msg);
        };
        let root = self.inner.resolved().root_scope();
        let value = self
            .inner
            .resolved()
            .query(root, &ast)
            .map_err(|e| e.to_string())?;
        Ok(self.value_to_json(&value).to_string())
    }

    /// Render the template a `view` usage presents over its exposed model
    /// slice (semantic mode): `qualified_name` names the view
    /// usage; the result is the rendered node tree as JSON, or HTML when
    /// `format` is `"html"`. Evaluation writes nothing into the model.
    // The export boundary converts an optional string only when owned.
    #[allow(clippy::needless_pass_by_value)]
    #[wasm_bindgen(js_name = renderView)]
    pub fn render_view(
        &mut self,
        qualified_name: &str,
        format: Option<String>,
    ) -> Result<String, String> {
        let view = self
            .inner
            .resolved()
            .resolve_qualified(qualified_name)
            .ok_or_else(|| format!("element not found: {qualified_name}"))?;
        let nodes = self.inner.resolved().render_view(view)?;
        Ok(match format.as_deref() {
            Some("html") => sysmlv2_model::render::to_html(&nodes),
            _ => serde_json::Value::Array(nodes.iter().map(|n| n.to_json()).collect()).to_string(),
        })
    }

    /// Describe a `view` usage for tabular consumers: the rendering it
    /// requests (`render …;` → the rendering usage's declared name),
    /// the elements it exposes (its `expose` imports with the view's
    /// `filter` conditions applied — the same exposure the CLI's
    /// view-directed diagrams use), the view usages it owns (a matrix's
    /// `columns` sub-view), and its prefix metadata with every owned
    /// feature value evaluated (`@MatrixConfig { relationship = "…"; }`
    /// → `{ "type": "…::MatrixConfig", "values": { "relationship": "…" } }`).
    /// JSON `{ qualifiedName (canonical spelling), id, rendering, exposed: [{ id, qualifiedName,
    /// metaclass }], views: [{ name, qualifiedName, id }], metadata: [{ type,
    /// values }] }`; errors when the name does not resolve to a view usage.
    /// Reads only; nothing is written into the model.
    #[wasm_bindgen(js_name = viewInfo)]
    pub fn view_info(&mut self, qualified_name: &str) -> Result<String, String> {
        let view = self
            .inner
            .resolved()
            .resolve_qualified(qualified_name)
            .ok_or_else(|| format!("element not found: {qualified_name}"))?;
        if self.inner.resolved().element_type(view) != "ViewUsage" {
            return Err(format!("{qualified_name} is not a view usage"));
        }
        let (qualified, id, rendering, exposed, views, metadata) = {
            let r = self.inner.resolved();
            // The canonical spelling, not the caller's: a request may quote
            // names the model spells bare (`P::'Verified'` vs `P::Verified`).
            let qualified = r.element_qualified_name(view);
            let id = r.element_id(view).to_string();
            let rendering = r.view_rendering(view);
            let exposed: Vec<serde_json::Value> = r
                .view_exposed_elements(view)
                .into_iter()
                .map(|e| {
                    json!({
                        "id": r.element_id(e).to_string(),
                        "qualifiedName": r.element_qualified_name(e),
                        "metaclass": r.element_type(e),
                    })
                })
                .collect();
            let owned: Vec<ElementRef> = r
                .owned_members(view)
                .into_iter()
                .filter(|&m| r.element_type(m) == "ViewUsage")
                .collect();
            let mut views = Vec::with_capacity(owned.len());
            for m in owned {
                let name = r.element_name(m).map(str::to_string);
                views.push(json!({
                    "name": name,
                    "qualifiedName": r.element_qualified_name(m),
                    "id": r.element_id(m).to_string(),
                }));
            }
            // Each metadata usage: its (first) type and the evaluated
            // values of the features its body declares; unevaluable
            // values are omitted rather than failing the whole report.
            let mut metadata: Vec<MetadataValues> = Vec::new();
            for m in r.metadata_of(view) {
                let ty = r
                    .typings(m)
                    .first()
                    .and_then(|&t| r.element_qualified_name(t));
                let mut values = Vec::new();
                for f in r.owned_members(m) {
                    let Some(name) = r.element_name(f).map(str::to_string) else {
                        continue;
                    };
                    if let Ok(v) = r.evaluate(f) {
                        values.push((name, v));
                    }
                }
                metadata.push(MetadataValues { ty, values });
            }
            (qualified, id, rendering, exposed, views, metadata)
        };
        let metadata: Vec<serde_json::Value> = metadata
            .into_iter()
            .map(|MetadataValues { ty, values }| {
                let mut obj = serde_json::Map::new();
                for (name, v) in &values {
                    obj.insert(name.clone(), self.value_to_json(v));
                }
                json!({ "type": ty, "values": serde_json::Value::Object(obj) })
            })
            .collect();
        Ok(json!({
            "qualifiedName": qualified,
            "id": id,
            "rendering": rendering,
            "exposed": exposed,
            "views": views,
            "metadata": metadata,
        })
        .to_string())
    }

    /// Evaluate `e`'s bound feature value; JSON, as in [`Self::query`].
    pub fn evaluate(&mut self, e: &Element) -> Result<String, String> {
        self.guard(e)?;
        let value = self
            .inner
            .resolved()
            .evaluate(e.e)
            .map_err(|e| e.to_string())?;
        Ok(self.value_to_json(&value).to_string())
    }

    // ---- derived properties (the spec-name read API) ----

    /// The derived property `name` of `e`, by its specification name
    /// (`"ownedFeature"`, `"owningNamespace"`, `"name"`, …), as JSON: `null`
    /// for a null single value, a boolean or string, an array of strings,
    /// an element as `{"@id": …}` and a list of elements as an array of
    /// them; a target outside the model as `{"outside": true, "id"?: …,
    /// "spelling"?: …}` (an element of an unloaded library or a foreign
    /// payload by its id, or a reference that never resolved by its
    /// spelling). Element handles for the same value come from
    /// [`Self::derived_elements`]. Errors when the element's metaclass
    /// does not declare the property as derived or the toolkit does not
    /// compute it yet; `derives` tells in advance.
    pub fn derived(&mut self, e: &Element, name: &str) -> Result<String, String> {
        use sysmlv2_model::json::{DerivedValue, Reference, dangling_id};
        self.guard(e)?;
        let value = self.derived_value(e, name)?;
        let r = self.inner.resolved();
        let id = |x: ElementRef| serde_json::json!({ "@id": r.element_id(x).to_string() });
        let reference = |x: &Reference| -> Result<serde_json::Value, String> {
            Ok(match x {
                Reference::Element(x) => id(*x),
                Reference::External(u) => {
                    serde_json::json!({ "outside": true, "id": u.to_string() })
                }
                // The full form spells an unresolved reference as its
                // deterministic dangling id: carried beside the spelling.
                Reference::Unresolved(s) => serde_json::json!({
                    "outside": true,
                    "spelling": s,
                    "danglingId": dangling_id(s),
                }),
                _ => return Err("unsupported reference shape from a newer toolkit".into()),
            })
        };
        let json = match &value {
            DerivedValue::Null => serde_json::Value::Null,
            DerivedValue::Bool(b) => serde_json::Value::Bool(*b),
            DerivedValue::Str(s) => serde_json::Value::String(s.clone()),
            DerivedValue::Strings(ss) => serde_json::json!(ss),
            DerivedValue::Element(x) => id(*x),
            DerivedValue::Elements(xs) => {
                serde_json::Value::Array(xs.iter().map(|&x| id(x)).collect())
            }
            DerivedValue::Reference(x) => reference(x)?,
            DerivedValue::References(xs) => {
                serde_json::Value::Array(xs.iter().map(reference).collect::<Result<_, _>>()?)
            }
            _ => return Err("unsupported derived value shape from a newer toolkit".into()),
        };
        Ok(json.to_string())
    }

    /// The element handles of the derived property `name` of `e`: the
    /// element of a single-valued value, the elements of a list, the
    /// in-model targets of a reference-typed value — a target outside the
    /// model has no handle and is *dropped* here (it is in
    /// [`Self::derived`]'s JSON as an `outside` object); empty for a
    /// string or boolean. Errors as `derived` does.
    #[wasm_bindgen(js_name = derivedElements)]
    pub fn derived_elements(&mut self, e: &Element, name: &str) -> Result<Vec<Element>, String> {
        use sysmlv2_model::json::DerivedValue;
        self.guard(e)?;
        let gen = self.gen;
        let value = self.derived_value(e, name)?;
        let handles: Vec<ElementRef> = match &value {
            DerivedValue::Element(x) => vec![*x],
            DerivedValue::Elements(xs) => xs.clone(),
            DerivedValue::Reference(r) => r.element().into_iter().collect(),
            DerivedValue::References(rs) => rs.iter().filter_map(|r| r.element()).collect(),
            _ => Vec::new(),
        };
        Ok(handles.into_iter().map(|x| Element { e: x, gen }).collect())
    }

    fn derived_value(
        &mut self,
        e: &Element,
        name: &str,
    ) -> Result<sysmlv2_model::json::DerivedValue, String> {
        use sysmlv2_model::json::Derived;
        match self.inner.resolved().derived(e.e, name) {
            Derived::NotDeclared => Err(format!(
                "{name} is not a derived property of {}",
                self.inner.resolved().element_type(e.e)
            )),
            Derived::NotComputed => Err(format!("{name} is not computed by this toolkit yet")),
            Derived::Value(v) => Ok(v),
        }
    }

    /// What `derived` answers for `name` on elements of `metaclass`,
    /// decided without a model: `"not-declared"`, `"not-computed"`,
    /// `"passthrough"` or `"exact"`.
    pub fn derives(metaclass: &str, name: &str) -> String {
        use sysmlv2_model::json::Derives;
        match sysmlv2_model::json::derives(metaclass, name) {
            Derives::NotDeclared => "not-declared",
            Derives::NotComputed => "not-computed",
            Derives::Passthrough => "passthrough",
            Derives::Exact => "exact",
        }
        .to_string()
    }

    /// Whether the abstract syntax owns `name` on `metaclass`.
    #[wasm_bindgen(js_name = isOwnedProperty)]
    pub fn is_owned_property(metaclass: &str, name: &str) -> bool {
        sysmlv2_model::json::is_owned_property(metaclass, name)
    }

    /// Every derived property name `derived` can answer on some
    /// metaclass.
    #[wasm_bindgen(js_name = computedNames)]
    pub fn computed_names() -> Vec<String> {
        sysmlv2_model::json::computed_names()
            .map(str::to_string)
            .collect()
    }

    /// The closure policy `derived` answers under: `"passthrough"` (the
    /// default), `"closure"` or `"closure-implied"`.
    #[wasm_bindgen(js_name = closurePolicy)]
    pub fn closure_policy(&mut self) -> String {
        use sysmlv2_model::json::ClosurePolicy;
        match self.inner.resolved().closure_policy() {
            ClosurePolicy::Passthrough => "passthrough",
            ClosurePolicy::Closure {
                include_implied: false,
            } => "closure",
            ClosurePolicy::Closure {
                include_implied: true,
            } => "closure-implied",
        }
        .to_string()
    }

    /// Set the closure policy (see `closurePolicy`).
    #[wasm_bindgen(js_name = setClosurePolicy)]
    pub fn set_closure_policy(&mut self, policy: &str) -> Result<(), String> {
        use sysmlv2_model::json::ClosurePolicy;
        let policy = match policy {
            "passthrough" => ClosurePolicy::Passthrough,
            "closure" => ClosurePolicy::Closure {
                include_implied: false,
            },
            "closure-implied" => ClosurePolicy::Closure {
                include_implied: true,
            },
            other => {
                return Err(format!(
                    "unknown closure policy {other:?}: passthrough, closure or closure-implied"
                ));
            }
        };
        self.inner.resolved().set_closure_policy(policy);
        Ok(())
    }

    // ---- navigation ----

    /// The element's qualified name (undefined for anonymous elements):
    /// the specification's derivation, in which a reserved word used as
    /// a name stays bare (`part::view`). A model property, not source
    /// text — splice [`Self::reference_spelling`] into generated
    /// `import`/`expose` targets instead.
    #[wasm_bindgen(js_name = qualifiedName)]
    pub fn qualified_name(&mut self, e: &Element) -> Result<Option<String>, String> {
        self.guard(e)?;
        Ok(self.inner.resolved().element_qualified_name(e.e))
    }

    /// The element's qualified name spelled as reference text that
    /// re-parses in either dialect: reserved words and non-basic names
    /// quoted (`'part'::'view'` where `qualifiedName` reports
    /// `part::view`). Undefined for anonymous elements.
    #[wasm_bindgen(js_name = referenceSpelling)]
    pub fn reference_spelling(&mut self, e: &Element) -> Result<Option<String>, String> {
        self.guard(e)?;
        Ok(self.inner.resolved().element_reference_spelling(e.e))
    }

    /// The element's declared name; the specification's `name` (an
    /// unnamed feature named by what it redefines) is `derived(e, "name")`.
    pub fn name(&mut self, e: &Element) -> Result<Option<String>, String> {
        self.guard(e)?;
        Ok(self.inner.resolved().element_name(e.e).map(str::to_string))
    }

    /// The element's declared short name (`<shortName>`), when it has one;
    /// the specification's `shortName` is `derived(e, "shortName")`.
    #[wasm_bindgen(js_name = shortName)]
    pub fn short_name(&mut self, e: &Element) -> Result<Option<String>, String> {
        self.guard(e)?;
        Ok(self
            .inner
            .resolved()
            .element_declared_short_name(e.e)
            .map(str::to_string))
    }

    /// The element's documentation/comment bodies, display-normalized,
    /// in declaration order: `doc` members annotating it plus comments
    /// naming it in `about`.
    pub fn docs(&mut self, e: &Element) -> Result<Vec<String>, String> {
        self.guard(e)?;
        Ok(self
            .inner
            .resolved()
            .annotation_bodies()
            .into_iter()
            .filter(|(t, _)| *t == e.e)
            .map(|(_, b)| sysmlv2_model::json::doc_display_text(&b))
            .filter(|b| !b.is_empty())
            .collect())
    }

    /// The element's abstract-syntax metaclass (`PartUsage`, …).
    pub fn metaclass(&mut self, e: &Element) -> Result<String, String> {
        self.guard(e)?;
        Ok(self.inner.resolved().element_type(e.e).to_string())
    }

    /// The element's interchange `@id`.
    #[wasm_bindgen(js_name = elementId)]
    pub fn element_id(&mut self, e: &Element) -> Result<String, String> {
        self.guard(e)?;
        Ok(self.inner.resolved().element_id(e.e).to_string())
    }

    /// The owning element (undefined for document roots).
    pub fn owner(&mut self, e: &Element) -> Result<Option<Element>, String> {
        self.guard(e)?;
        let gen = self.gen;
        Ok(self.inner.resolved().owner(e.e).map(|e| Element { e, gen }))
    }

    /// Owned members, in declaration order (KerML `ownedMember`).
    pub fn members(&mut self, e: &Element) -> Result<Vec<Element>, String> {
        self.guard(e)?;
        let gen = self.gen;
        Ok(self
            .inner
            .resolved()
            .owned_members(e.e)
            .into_iter()
            .map(|e| Element { e, gen })
            .collect())
    }

    /// Members owned via FeatureMembership kinds (KerML `ownedFeature`).
    pub fn features(&mut self, e: &Element) -> Result<Vec<Element>, String> {
        self.guard(e)?;
        let gen = self.gen;
        Ok(self
            .inner
            .resolved()
            .owned_features(e.e)
            .into_iter()
            .map(|e| Element { e, gen })
            .collect())
    }

    /// Explicit FeatureTyping targets (`: T`), resolved.
    pub fn typings(&mut self, e: &Element) -> Result<Vec<Element>, String> {
        self.guard(e)?;
        let gen = self.gen;
        Ok(self
            .inner
            .resolved()
            .typings(e.e)
            .into_iter()
            .map(|e| Element { e, gen })
            .collect())
    }

    /// Explicit `about` targets of an annotating element, resolved.
    #[wasm_bindgen(js_name = annotatedElements)]
    pub fn annotated_elements(&mut self, e: &Element) -> Result<Vec<Element>, String> {
        self.guard(e)?;
        let gen = self.gen;
        Ok(self
            .inner
            .resolved()
            .annotated_elements(e.e)
            .into_iter()
            .map(|e| Element { e, gen })
            .collect())
    }

    /// Does `e` reach `ancestor` through the explicit specialization
    /// closure?
    pub fn conforms(&mut self, e: &Element, ancestor: &Element) -> Result<bool, String> {
        self.guard(e)?;
        self.guard(ancestor)?;
        Ok(self.inner.resolved().conforms(e.e, ancestor.e))
    }

    /// The shortest spelling of `target` that resolves to it from
    /// inside `context`'s declaration — what a generated value
    /// expression should write instead of the full qualified name
    /// (same suffix discipline as minimize, without rewriting).
    #[wasm_bindgen(js_name = minimalSpelling)]
    pub fn minimal_spelling(
        &mut self,
        context: &Element,
        target: &Element,
    ) -> Result<Option<String>, String> {
        self.guard(context)?;
        self.guard(target)?;
        Ok(self.inner.minimal_spelling(context.e, target.e))
    }

    /// Rewrite every plain reference site to the shortest suffix that
    /// still resolves to the same element (reparse-verified; ids are
    /// untouched by construction). Returns `{respelled, sites}`.
    /// Element handles from before the call are invalidated — the
    /// sources were rewritten and the model rebuilt.
    #[wasm_bindgen(js_name = minimizeQualifications)]
    pub fn minimize_qualifications(&mut self) -> Result<String, String> {
        let report = self
            .inner
            .minimize_qualifications()
            .map_err(|e| e.to_string())?;
        self.gen += 1;
        Ok(serde_json::json!({
            "respelled": report.respelled,
            "reverted": report.reverted,
        })
        .to_string())
    }

    /// Top-level user elements: the owned members of each unit's root
    /// namespace, in declaration order — the outline/tree entry point.
    /// (Ownerless relationship records — memberships, typings, feature
    /// values — are graph plumbing and never appear here.)
    pub fn roots(&mut self) -> Vec<Element> {
        let gen = self.gen;
        let r = self.inner.resolved();
        let all: Vec<ElementRef> = r.user_elements().collect();
        let mut tops = Vec::new();
        for e in all {
            if r.owner(e).is_none() && r.element_type(e) == "Namespace" {
                tops.extend(r.owned_members(e));
            }
        }
        tops.into_iter().map(|e| Element { e, gen }).collect()
    }

    /// Every element of the given metaclass.
    #[wasm_bindgen(js_name = elementsOfMetaclass)]
    pub fn elements_of_metaclass(&mut self, ty: &str) -> Vec<Element> {
        let gen = self.gen;
        self.inner
            .resolved()
            .elements_of_metaclass(ty)
            .into_iter()
            .map(|e| Element { e, gen })
            .collect()
    }

    /// Whether the element belongs to a loaded library.
    #[wasm_bindgen(js_name = isLibraryElement)]
    pub fn is_library_element(&mut self, e: &Element) -> Result<bool, String> {
        self.guard(e)?;
        Ok(self.inner.resolved().is_library_element(e.e))
    }

    // ---- sources and emission ----

    /// The user units as JSON `[{unit, name, text}]` (`unit` is the
    /// model unit index).
    pub fn units(&self) -> String {
        let units: Vec<serde_json::Value> = self
            .inner
            .units()
            .map(|(i, n, s)| json!({"unit": i, "name": n, "text": s}))
            .collect();
        serde_json::Value::Array(units).to_string()
    }

    /// Current text of a unit by model unit index (undefined for
    /// library units).
    pub fn source(&self, unit: usize) -> Option<String> {
        self.inner.source(unit).map(str::to_string)
    }

    /// How many references failed to resolve.
    #[wasm_bindgen(js_name = unresolvedCount)]
    pub fn unresolved_count(&self) -> usize {
        self.inner.resolved_ref().unresolved_count()
    }

    /// Non-fatal problems from lifting interchange JSON, as a JSON
    /// string array.
    pub fn warnings(&self) -> String {
        json!(self.inner.warnings()).to_string()
    }

    /// Compact interchange JSON (KerML 10.4) for the session's model.
    #[wasm_bindgen(js_name = toCompactJson)]
    pub fn to_compact_json(&self) -> String {
        self.inner.to_compact_json().to_string()
    }

    /// Compact-form CBOR for the session's model (a `Uint8Array`) — the
    /// deterministic binary re-encoding of [`Self::to_compact_json`],
    /// several times smaller on the wire and decodable back to the
    /// identical element array.
    #[wasm_bindgen(js_name = toCompactCbor)]
    pub fn to_compact_cbor(&self) -> Vec<u8> {
        self.inner.to_compact_cbor()
    }

    /// [`Self::to_compact_cbor`] with **id elision**: graph-derivable
    /// ids are omitted and receivers recompute them, verified by the
    /// payload digest. The session's library names the effective-name
    /// targets; decode against the same library version.
    #[wasm_bindgen(js_name = toCompactCborElided)]
    pub fn to_compact_cbor_elided(&self) -> Result<Vec<u8>, String> {
        self.inner
            .to_compact_cbor_elided()
            .map_err(|e| e.to_string())
    }

    /// The model's **state digest** — the content identity a delta
    /// names its base by; emission-order-independent.
    #[wasm_bindgen(js_name = stateDigest)]
    pub fn state_digest(&self) -> String {
        self.inner.state_digest().to_string()
    }

    /// Encode the delta from `base_json` (a compact element array) to
    /// this session's model as an s2c delta payload. `portable`
    /// selects id-keyed identities for best-effort application to
    /// divergent bases; the strict default is smaller and digest-gated.
    #[wasm_bindgen(js_name = deltaCborFrom)]
    pub fn delta_cbor_from(&self, base_json: &str, portable: bool) -> Result<Vec<u8>, String> {
        let base: serde_json::Value = serde_json::from_str(base_json).map_err(|e| e.to_string())?;
        self.inner
            .delta_cbor_from(&base, portable)
            .map_err(|e| e.to_string())
    }

    /// Decode any snapshot-form s2c payload (compact, id-elided, or
    /// full) to its element array as JSON text, naming elided targets
    /// through the session's library. Delta payloads refuse with their
    /// pointed message — apply those with [`Self::apply_delta_cbor`].
    #[wasm_bindgen(js_name = decodeCbor)]
    pub fn decode_cbor(&self, bytes: &[u8]) -> Result<String, String> {
        self.inner
            .decode_cbor(bytes)
            .map(|v| v.to_string())
            .map_err(|e| e.to_string())
    }

    /// Apply a delta payload against the session's model. Returns JSON
    /// `{ "result": [...], "report": { "baseMatched", "noopDeletes",
    /// "upsertedUpdates", "replacedCreates" } }`; the session itself is
    /// unchanged — the host decides what to do with the result. Strict
    /// application refuses a wrong base; `lenient` applies portable
    /// deltas best-effort with the report saying what happened.
    #[wasm_bindgen(js_name = applyDeltaCbor)]
    pub fn apply_delta_cbor(&self, bytes: &[u8], lenient: bool) -> Result<String, String> {
        let (result, report) = self
            .inner
            .apply_delta_cbor(bytes, lenient)
            .map_err(|e| e.to_string())?;
        Ok(apply_report_json(&result, &report))
    }

    /// Apply a delta payload against a caller-held base document (a
    /// compact element array as JSON) instead of the session's own
    /// model — the payload-file base path: a file base's identity is
    /// the file's content, and lifting it into a session would
    /// re-derive ids and change the digest a strict delta gates on.
    /// The session provides the library context for elided created
    /// ids; result shape as [`Self::apply_delta_cbor`].
    #[wasm_bindgen(js_name = applyDeltaCborTo)]
    pub fn apply_delta_cbor_to(
        &self,
        bytes: &[u8],
        base_json: &str,
        lenient: bool,
    ) -> Result<String, String> {
        let base: serde_json::Value = serde_json::from_str(base_json).map_err(|e| e.to_string())?;
        let (result, report) = self
            .inner
            .apply_delta_cbor_to(bytes, &base, lenient)
            .map_err(|e| e.to_string())?;
        Ok(apply_report_json(&result, &report))
    }

    /// [`Self::apply_delta_cbor_to`] with the applied result embedded
    /// as a raw JSON **string** field (`resultJson`) instead of a
    /// parsed value: host-language JSON parsers may re-canonicalize
    /// numbers (`1.0` → `1`), which changes the compact-CBOR encoding
    /// and therefore the state digest — a digest-faithful replay chain
    /// must carry state documents as emitted strings end to end.
    #[wasm_bindgen(js_name = applyDeltaCborToRaw)]
    pub fn apply_delta_cbor_to_raw(
        &self,
        bytes: &[u8],
        base_json: &str,
        lenient: bool,
    ) -> Result<String, String> {
        let base: serde_json::Value = serde_json::from_str(base_json).map_err(|e| e.to_string())?;
        let (result, report) = self
            .inner
            .apply_delta_cbor_to(bytes, &base, lenient)
            .map_err(|e| e.to_string())?;
        Ok(serde_json::json!({
            "resultJson": result.to_string(),
            "report": apply_report_value(&report),
        })
        .to_string())
    }

    /// Full interchange JSON (derived properties + implied
    /// relationships). With `recover_refs`, references that serialize as
    /// dangling ids also carry their source spelling, so a partial model
    /// survives emit → reload losslessly (the Flexo change-record path).
    #[wasm_bindgen(js_name = toFullJson)]
    pub fn to_full_json(&self, recover_refs: bool) -> String {
        self.inner.to_full_json_with(recover_refs).to_string()
    }

    /// Full-form CBOR (a `Uint8Array`) — the binary re-encoding of
    /// [`Self::to_full_json`]. Emit view only; transport the compact
    /// form and expand at the edge.
    #[wasm_bindgen(js_name = toFullCbor)]
    pub fn to_full_cbor(&self, recover_refs: bool) -> Vec<u8> {
        self.inner.to_full_cbor(recover_refs)
    }

    /// Emit a PlantUML diagram of the session's model. Options as
    /// a JSON object (see `PlantumlOpts` docs); pass `undefined`/`"{}"`
    /// for the defaults (tree view). Feed the text to any PlantUML build.
    // The export boundary converts an optional string only when owned.
    #[allow(clippy::needless_pass_by_value)]
    #[wasm_bindgen(js_name = toPlantuml)]
    pub fn to_plantuml(&mut self, opts_json: Option<String>) -> Result<String, String> {
        let (viz, root, _) = self.diagram_request(opts_json.as_deref())?;
        if viz.roots.as_ref().is_some_and(|r| r.is_empty()) {
            return Ok("@startuml\n' the view exposes nothing\n@enduml\n".to_string());
        }
        Ok(sysmlv2_viz::plantuml(self.inner.resolved(), root, &viz))
    }

    /// Emit the structured diagram graph (nodes with element identity,
    /// source spans, and compartment rows; edges with kinds) for a
    /// view — the native renderer's input. Options as in
    /// [`Self::to_plantuml`]; views without a graph emitter yet error.
    // The export boundary converts an optional string only when owned.
    #[allow(clippy::needless_pass_by_value)]
    #[wasm_bindgen(js_name = toGraph)]
    pub fn to_graph(&mut self, opts_json: Option<String>) -> Result<String, String> {
        let (mut viz, root, summary_opts) = self.diagram_request(opts_json.as_deref())?;
        let view = view_name(viz.view);
        if !matches!(
            viz.view,
            sysmlv2_viz::View::Tree
                | sysmlv2_viz::View::Interconnection
                | sysmlv2_viz::View::State
                | sysmlv2_viz::View::Action
        ) {
            return Err(format!("no structured-graph emitter for view: {view}"));
        }
        if summary_opts.is_some() && viz.view != sysmlv2_viz::View::Tree {
            return Err("summary emission is tree-only".to_string());
        }
        if viz.roots.as_ref().is_some_and(|r| r.is_empty()) {
            let mut g = json!({ "view": view, "nodes": [], "edges": [] });
            if summary_opts.is_some() {
                g["summary"] = json!({ "resolved": [], "unresolved": [] });
            }
            return Ok(g.to_string());
        }
        // Summary mode: resolve the open set, remembering what did not
        // resolve so the client can prune a persisted set.
        let mut summary = None;
        let mut resolved_open = Vec::new();
        let mut unresolved_open = Vec::new();
        if let Some(sm) = &summary_opts {
            let mut open = Vec::new();
            for sel in &sm.open {
                match resolve_selector(self.inner.resolved(), sel) {
                    Some(e) => {
                        let r = self.inner.resolved();
                        resolved_open.push(json!({
                            "id": r.element_id(e).to_string(),
                            "qualifiedName": r.element_qualified_name(e),
                        }));
                        open.push(e);
                    }
                    None => unresolved_open
                        .push(serde_json::to_value(sel).unwrap_or(serde_json::Value::Null)),
                }
            }
            let unbounded = sm
                .unbounded
                .iter()
                .filter_map(|sel| resolve_selector(self.inner.resolved(), sel))
                .collect();
            summary = Some(sysmlv2_viz::SummaryOptions {
                open,
                note_budget: sm.note_budget,
                leaf_budget: sm.leaf_budget,
                unbounded,
            });
        }
        viz.summary = summary;
        let mut g =
            sysmlv2_viz::graph(self.inner.resolved(), root, &viz).map_err(|e| e.to_string())?;
        if summary_opts.is_some() {
            g["summary"] = json!({ "resolved": resolved_open, "unresolved": unresolved_open });
        }
        Ok(g.to_string())
    }

    /// The containers from the scope root down to an element (root
    /// first, the element's owner last), for opening a summary picture
    /// onto it: JSON `[{id, qualifiedName}]`. The selector is a
    /// qualified name or `{elementId}`; errors when it does not resolve.
    #[wasm_bindgen(js_name = revealPath)]
    pub fn reveal_path(&mut self, selector_json: &str) -> Result<String, String> {
        // A bare name is as good as its JSON string form.
        let sel: Selector = serde_json::from_str(selector_json)
            .unwrap_or_else(|_| Selector::Name(selector_json.to_string()));
        let r = self.inner.resolved();
        let e = resolve_selector(r, &sel)
            .ok_or_else(|| format!("element not found: {selector_json}"))?;
        let mut path = Vec::new();
        let mut cur = r.owner(e);
        while let Some(o) = cur {
            if r.element_type(o) == "Namespace" {
                break;
            }
            path.push(json!({ "id": r.element_id(o).to_string(), "qualifiedName": r.element_qualified_name(o) }));
            cur = r.owner(o);
        }
        path.reverse();
        Ok(serde_json::Value::Array(path).to_string())
    }

    /// Apply an edit batch (JSON array of `EditOpIn` operations) via
    /// the session's edit engine: splices are planned at
    /// resolver-recorded spans, applied, reparsed, and verified for
    /// semantic identity — or rolled back, in which case this returns
    /// the engine's error and the session is unchanged.
    ///
    /// On success the session is rebuilt (outstanding handles go stale)
    /// and the result JSON reports what happened: `{idMap: [[oldId,
    /// newId]…], findings: [string…], splices: [{unit, start, end,
    /// text}…]}` — splices in pre-commit byte offsets per unit, exactly
    /// what an editor mirror needs to replay the change.
    ///
    /// A `rename` whose new name a sibling in the same owner already
    /// carries (or that another rename in the batch gives a sibling)
    /// is dropped rather than refusing the batch: the rest commits and
    /// each dropped rename is one `findings` line. A batch of nothing
    /// but dropped renames commits nothing and leaves handles valid.
    pub fn edit(&mut self, ops_json: &str) -> Result<String, String> {
        let resolved = self.resolve_ops(Self::parse_ops(ops_json)?)?;
        let mut batch = self.inner.edit();
        batch.skip_colliding_renames();
        Self::stage_ops(&mut batch, &resolved);
        let report = batch.commit().map_err(|e| e.to_string())?;
        self.gen += 1;
        Ok(Self::report_json(&report).to_string())
    }

    /// Dry-run an edit batch (same ops JSON as [`Self::edit`]): the full
    /// verified-commit pipeline — splice, reparse, rebuild, reference
    /// checks — runs against copies and the session is untouched either
    /// way (no rebuild, handles stay valid). Returns `{wouldCommit:
    /// true, idMap, findings, splices}` — exactly what `edit` would
    /// report — or `{wouldCommit: false, refusal}` with the exact
    /// refusal it would roll back with (unresolvable op targets
    /// included). Errors only for malformed ops JSON.
    #[wasm_bindgen(js_name = checkEdit)]
    pub fn check_edit(&mut self, ops_json: &str) -> Result<String, String> {
        let ops = Self::parse_ops(ops_json)?;
        let resolved = match self.resolve_ops(ops) {
            Ok(r) => r,
            Err(refusal) => {
                return Ok(json!({"wouldCommit": false, "refusal": refusal}).to_string());
            }
        };
        let mut batch = self.inner.edit();
        batch.skip_colliding_renames();
        Self::stage_ops(&mut batch, &resolved);
        Ok(match batch.check() {
            Ok(report) => {
                let mut v = Self::report_json(&report);
                v["wouldCommit"] = json!(true);
                v.to_string()
            }
            Err(e) => json!({"wouldCommit": false, "refusal": e.to_string()}).to_string(),
        })
    }

    fn parse_ops(ops_json: &str) -> Result<Vec<EditOpIn>, String> {
        let ops: Vec<EditOpIn> =
            serde_json::from_str(ops_json).map_err(|e| format!("bad edit ops: {e}"))?;
        if ops.is_empty() {
            return Err("empty edit batch".to_string());
        }
        Ok(ops)
    }

    /// Resolve every element reference against the current state, so a
    /// bad reference fails before any planning starts.
    fn resolve_ops(&mut self, ops: Vec<EditOpIn>) -> Result<Vec<ResolvedOp>, String> {
        let resolve = resolve_edit_target;
        let mut resolved = Vec::with_capacity(ops.len());
        for op in ops {
            resolved.push(match op {
                EditOpIn::Rename { target, new_name } => {
                    ResolvedOp::Rename(resolve(&mut self.inner, &target)?, new_name)
                }
                EditOpIn::SetFeatureValue { target, expr } => {
                    ResolvedOp::SetFeatureValue(resolve(&mut self.inner, &target)?, expr)
                }
                EditOpIn::SetFeatureType { target, ty } => {
                    ResolvedOp::SetFeatureType(resolve(&mut self.inner, &target)?, ty)
                }
                EditOpIn::InsertMember { owner, text } => {
                    ResolvedOp::InsertMember(resolve(&mut self.inner, &owner)?, text)
                }
                EditOpIn::InsertTopLevel { unit, text } => ResolvedOp::InsertTopLevel(unit, text),
                EditOpIn::AddUnit { unit } => ResolvedOp::AddUnit(unit),
                EditOpIn::Remove { target } => {
                    ResolvedOp::Remove(resolve(&mut self.inner, &target)?)
                }
                EditOpIn::ReplaceMember { target, text } => {
                    ResolvedOp::ReplaceMember(resolve(&mut self.inner, &target)?, text)
                }
                EditOpIn::MoveMember {
                    target,
                    new_owner,
                    index,
                } => {
                    let e = resolve(&mut self.inner, &target)?;
                    let owner = match new_owner {
                        Some(name) => resolve(&mut self.inner, &name)?,
                        None => self
                            .inner
                            .resolved()
                            .owner(e)
                            .ok_or_else(|| format!("{target} has no owner to reorder in"))?,
                    };
                    ResolvedOp::MoveMember(e, owner, index.map(|i| i as usize))
                }
            });
        }
        Ok(resolved)
    }

    fn stage_ops(batch: &mut sysmlv2_transform::EditBuilder<'_>, ops: &[ResolvedOp]) {
        for op in ops {
            match op {
                ResolvedOp::Rename(e, name) => batch.rename(*e, name),
                ResolvedOp::SetFeatureValue(e, expr) => batch.set_feature_value(*e, expr),
                ResolvedOp::SetFeatureType(e, ty) => batch.set_feature_type(*e, ty),
                ResolvedOp::InsertMember(e, text) => batch.insert_member(*e, text),
                ResolvedOp::InsertTopLevel(unit, text) => batch.insert_top_level(unit, text),
                ResolvedOp::AddUnit(unit) => batch.add_unit(unit),
                ResolvedOp::Remove(e) => batch.remove(*e),
                ResolvedOp::ReplaceMember(e, text) => batch.replace_member(*e, text),
                ResolvedOp::MoveMember(e, owner, index) => batch.move_member(*e, *owner, *index),
            };
        }
    }

    fn report_json(report: &sysmlv2_transform::CommitReport) -> serde_json::Value {
        json!({
            "idMap": report
                .id_map
                .iter()
                .map(|(old, new)| json!([old.to_string(), new.to_string()]))
                .collect::<Vec<_>>(),
            "findings": report.findings,
            "splices": report
                .splices
                .iter()
                .map(|s| json!({
                    "unit": s.unit,
                    "start": s.start,
                    "end": s.end,
                    "text": s.text,
                }))
                .collect::<Vec<_>>(),
        })
    }

    /// The full source text of the member declaration that created the
    /// element (target = `::`-qualified name or `@<interchange-id>`) —
    /// what copy/paste carries between owners: feed it back through an
    /// `insertMember` op. Errors for library elements and elements
    /// without a recorded extent.
    #[wasm_bindgen(js_name = memberSource)]
    pub fn member_source(&mut self, target: &str) -> Result<String, String> {
        let e = resolve_edit_target(&mut self.inner, target)?;
        let (unit, span) = self
            .inner
            .resolved()
            .member_extent(e)
            .ok_or_else(|| format!("{target} has no recorded source extent"))?;
        let src = self
            .inner
            .source(unit)
            .ok_or_else(|| format!("{target} is a library element (read-only)"))?;
        Ok(src[span.start as usize..span.end as usize].to_string())
    }

    /// The element's recorded declaration site as JSON
    /// `{"unit": index, "start": byte, "end": byte}` (the declaration
    /// span, falling back to the full member extent), or undefined for
    /// elements without one (library elements, synthesized members).
    /// The unit index keys into `units()`; offsets are byte positions
    /// into that unit's source — the caller owns line/column mapping.
    /// The element's full member extent as JSON `{"unit": index,
    /// "start": byte, "end": byte}` — the whole declaration including
    /// its body, the range decorations and interception guards cover —
    /// or undefined for elements without one.
    #[wasm_bindgen(js_name = memberExtent)]
    pub fn member_extent_js(&mut self, e: &Element) -> Result<Option<String>, String> {
        self.guard(e)?;
        Ok(self
            .inner
            .resolved()
            .member_extent(e.e)
            .map(|(unit, span)| {
                json!({"unit": unit, "start": span.start, "end": span.end}).to_string()
            }))
    }

    #[wasm_bindgen(js_name = declarationSite)]
    pub fn declaration_site(&mut self, e: &Element) -> Result<Option<String>, String> {
        self.guard(e)?;
        Ok(self
            .inner
            .resolved()
            .declaration_site(e.e)
            .or_else(|| self.inner.resolved().member_extent(e.e))
            .map(|(unit, span)| {
                json!({"unit": unit, "start": span.start, "end": span.end}).to_string()
            }))
    }

    /// The source text of `e`'s bound value expression — the `<expr>`
    /// in `= <expr>` — or undefined when the declaration carries no
    /// value part (or the element has no user source). This is what a
    /// value editor should prefill before the user rewrites it; feed
    /// the replacement back through a `setFeatureValue` edit op, which
    /// splices at the same recorded span.
    #[wasm_bindgen(js_name = valueSource)]
    pub fn value_source(&mut self, e: &Element) -> Result<Option<String>, String> {
        self.guard(e)?;
        let Some((_, expr)) = self.inner.resolved().value_expr(e.e) else {
            return Ok(None);
        };
        let Some((unit, _)) = self
            .inner
            .resolved()
            .declaration_site(e.e)
            .or_else(|| self.inner.resolved().member_extent(e.e))
        else {
            return Ok(None);
        };
        let Some(src) = self.inner.source(unit) else {
            return Ok(None);
        };
        Ok(Some(
            src[expr.span.start as usize..expr.span.end as usize].to_string(),
        ))
    }

    /// Verify constraints the way `sysmlv2 verify --ranges` does:
    /// evaluate every non-library constraint, then narrow free
    /// feature domains by joint interval propagation per unit — no
    /// external solver. Options JSON: `{maxIters?}` (fixpoint pass cap
    /// per unit, default 100). Returns a JSON report: `{constraints:
    /// [{unit, unitName, name, elementType, asserted, line, col,
    /// endLine, endCol, status, method, detail, bindings, features}]
    /// (`method` = which stage decided: evaluation|propagation, null
    /// while undecided), ranges:
    /// [{feature, unit, range, narrowed}], summary: {satisfied,
    /// violated, undecided}}` — positions 1-based over the result
    /// expression; `status` folds definitive propagation conclusions
    /// into satisfied|violated|undecided; `detail` is the human
    /// verdict line, worded exactly like the CLI's (incl. the `(with
    /// reserveKg = 0.10)` suffix on violated verdicts). `bindings` =
    /// the result expression's feature references with their own
    /// evaluations and declaration positions (`{feature, value?,
    /// unitName?, line?, col?}`, empty for satisfied constraints);
    /// `features` = the free features the propagation term references
    /// (the keys into `ranges`).
    // The export boundary converts an optional string only when owned.
    #[allow(clippy::needless_pass_by_value)]
    pub fn verify(&mut self, opts_json: Option<String>) -> Result<String, String> {
        #[derive(Deserialize)]
        #[serde(rename_all = "camelCase", deny_unknown_fields)]
        struct VerifyOpts {
            max_iters: Option<usize>,
        }
        let opts: VerifyOpts = serde_json::from_str(opts_json.as_deref().unwrap_or("{}"))
            .map_err(|e| format!("bad verify options: {e}"))?;
        let cfg = PropagateConfig {
            max_iters: opts
                .max_iters
                .unwrap_or_else(|| PropagateConfig::default().max_iters),
        };
        // `None` solver = the solverless pipeline; it cannot fail.
        let report = sysmlv2_solve::verify_constraints(self.inner.model(), None, &cfg)
            .map_err(|e| e.to_string())?;

        let names: std::collections::HashMap<usize, String> = self
            .inner
            .units()
            .map(|(i, n, _)| (i, n.to_string()))
            .collect();
        // One line index per unit, built on first use and shared by the
        // constraint spans and their bindings' declaration sites.
        let mut indexes: HashMap<usize, LineIndex> = HashMap::new();
        let (mut sat, mut vio, mut und) = (0usize, 0usize, 0usize);
        let inner = &self.inner;
        let constraints: Vec<serde_json::Value> = report
            .constraints
            .iter()
            .map(|c| {
                let (status, mut detail) = verify_status(&c.verdict, c.propagate.as_ref());
                match status {
                    "satisfied" => sat += 1,
                    "violated" => vio += 1,
                    _ => und += 1,
                }
                // Which stage decided the verdict — `None` while undecided.
                let method = match (&c.verdict, &c.propagate) {
                    (ConstraintVerdict::Satisfied | ConstraintVerdict::Violated, _) => {
                        Some("evaluation")
                    }
                    (
                        _,
                        Some(
                            PropagateOutcome::Satisfied
                            | PropagateOutcome::Violated
                            | PropagateOutcome::Unsatisfiable,
                        ),
                    ) => Some("propagation"),
                    _ => None,
                };
                // The CLI's "why" suffix: evaluated values of the bound
                // references under a violated verdict.
                if status == "violated" {
                    let vals: Vec<String> = c
                        .bindings
                        .iter()
                        .filter_map(|b| b.value.as_ref().map(|v| format!("{} = {v}", b.feature)))
                        .collect();
                    if !vals.is_empty() {
                        detail = format!("{detail} (with {})", vals.join(", "));
                    }
                }
                let bindings: Vec<serde_json::Value> = c
                    .bindings
                    .iter()
                    .map(|b| {
                        // Declaration site → position, when the feature
                        // lives in a user unit (library sources are not
                        // held, so library declarations carry no position).
                        let pos = b
                            .site
                            .filter(|(unit, _)| inner.source(*unit).is_some())
                            .map(|(unit, span)| {
                                let lc =
                                    unit_line_index(&mut indexes, inner, unit).line_col(span.start);
                                (unit, lc)
                            });
                        json!({
                            "feature": b.feature,
                            "value": b.value,
                            "unitName": pos.and_then(|(u, _)| names.get(&u)),
                            "line": pos.map(|(_, lc)| lc.line),
                            "col": pos.map(|(_, lc)| lc.col),
                        })
                    })
                    .collect();
                let li = unit_line_index(&mut indexes, inner, c.unit);
                let start = li.line_col(c.span.start);
                let end = li.line_col(c.span.end);
                json!({
                    "unit": c.unit,
                    "unitName": names.get(&c.unit),
                    "name": c.name,
                    "elementType": c.element_type,
                    "asserted": c.asserted,
                    "line": start.line,
                    "col": start.col,
                    "endLine": end.line,
                    "endCol": end.col,
                    "status": status,
                    "method": method,
                    "detail": detail,
                    "bindings": bindings,
                    "features": c.features,
                })
            })
            .collect();
        let ranges: Vec<serde_json::Value> = report
            .ranges
            .iter()
            .map(|r| {
                json!({
                    "feature": r.feature,
                    "unit": r.unit,
                    "range": r.range,
                    "rangeApprox": r.range_approx,
                    "narrowed": r.narrowed,
                })
            })
            .collect();
        Ok(json!({
            "constraints": constraints,
            "ranges": ranges,
            "summary": {"satisfied": sat, "violated": vio, "undecided": und},
        })
        .to_string())
    }

    /// Lint the session's user units the way `sysmlv2 lint` does:
    /// configurable project-policy rules over the resolved
    /// model — library and dependency elements are exempt by the
    /// engine's closed-world discipline, so the caller owns dep-free
    /// semantics exactly as with `verify`. `config_json` is the
    /// `sysmlint.json` text (`{"rules": {"<id>": "off"|"hint"|"info"|"warn"|"error"
    /// | {severity, …options}}}`); absent means every rule at its
    /// default severity; unknown ids/options surface as `lint-config`
    /// findings, and unreadable JSON is the only error. Returns
    /// `{findings: [{stage, rule, severity, message, unit, unitName,
    /// start, end, line, col, endLine, endCol, element, suggest, fix,
    /// alternatives}], summary: {errors, warnings, infos, hints}}` (the
    /// `sysmlv2_lint::json` report shape, shared with the CLI's
    /// `--format json`; `stage` is always `lint` here) — byte offsets
    /// and 1-based positions over the finding's name span; `unit` and
    /// the positions are null on `lint-config` findings. `element`
    /// (nullable) = the finding's edit-target spelling (`::`-qualified
    /// name or `@<id>`) for host quick fixes;
    /// `suggest` (nullable) = a naming finding's style-converted
    /// replacement name. `fix` (nullable)
    /// = `{label, deletes, semantic, edits: [{unit, unitName, start,
    /// end, replacement}]}` with **byte** offsets over the unit's
    /// current text (the splice currency every edit surface here uses);
    /// `deletes` marks fixes hosts must gate behind explicit opt-in, and
    /// `semantic` marks fixes that change what a declaration means
    /// (never part of a fix-all sweep).
    /// `alternatives` (array, same shape as `fix`) are equally-valid
    /// remedies for a quick-fix menu — a dimensionally ambiguous unit
    /// lists every compatible quantity type — never auto-applied.
    // The export boundary converts an optional string only when owned.
    #[allow(clippy::needless_pass_by_value)]
    pub fn lint(&mut self, config_json: Option<String>) -> Result<String, String> {
        let cfg = match config_json.as_deref().filter(|s| !s.trim().is_empty()) {
            Some(text) => sysmlv2_lint::Config::from_json(text).map_err(|e| e.to_string())?,
            None => sysmlv2_lint::Config::default(),
        };
        // The textual tier (`indentation`) reads the units' source
        // text; the generated-provenance tier additionally reads unit
        // names (the sidecar contract is spelled in them).
        let texts: Vec<(usize, String, String)> = self
            .inner
            .units()
            .map(|(i, n, t)| (i, n.to_string(), t.to_string()))
            .collect();
        let units: Vec<(usize, &str, &str)> = texts
            .iter()
            .map(|(i, n, t)| (*i, n.as_str(), t.as_str()))
            .collect();
        let findings = sysmlv2_lint::lint_units(self.inner.resolved(), &cfg, &units);
        // The shared report shape (`sysmlv2_lint::json`): engine unit
        // indexes are reported unchanged — they are the session's — so
        // every unit gets an identity alias (the table reports only
        // aliased units).
        let mut table = sysmlv2_lint::json::Units::new();
        for (i, name, text) in &texts {
            table.add(*i, name, text);
            table.alias(*i, *i);
        }
        let mut report = sysmlv2_lint::json::Report::new();
        for f in &findings {
            report.push_finding(f, &table);
        }
        Ok(report.into_value().to_string())
    }

    /// The lint engine's validated generated-ownership join, exposed
    /// directly to editor hosts. Unlike a host-side rescan this omits
    /// every corrupt/ambiguous row (while `lint` reports why) and keeps
    /// the guard contract in lockstep with sidecar ownership policy.
    #[wasm_bindgen(js_name = generatedInventory)]
    pub fn generated_inventory(&mut self) -> String {
        let texts: Vec<(usize, String, String)> = self
            .inner
            .units()
            .map(|(i, n, t)| (i, n.to_string(), t.to_string()))
            .collect();
        let units: Vec<(usize, &str, &str)> = texts
            .iter()
            .map(|(i, n, t)| (*i, n.as_str(), t.as_str()))
            .collect();
        let names: std::collections::HashMap<usize, &str> =
            units.iter().map(|(i, n, _)| (*i, *n)).collect();
        let inventory = sysmlv2_lint::generated_inventory(self.inner.resolved(), &units);
        let row_json = |row: &sysmlv2_lint::GeneratedRange| {
            json!({
                "unit": names.get(&row.unit).copied().unwrap_or(""),
                "start": row.start,
                "end": row.end,
                "key": row.key,
                "transformId": row.transform_id,
                "source": row.source,
                "sources": row.sources.iter().map(|source| json!({
                    "alias": source.alias,
                    "ref": source.source_ref,
                    "inputDigest": source.input_digest,
                    "rowCount": source.row_count,
                })).collect::<Vec<_>>(),
                "transformerPath": row.transformer_path,
                "memberQn": row.member_qn,
                "memberId": row.member_id,
                "recordId": row.record_id,
                "raw": row.raw,
                "excluded": row.excluded,
                "rowDigest": row.row_digest,
            })
        };
        json!({
            "members": inventory.members.iter().map(row_json).collect::<Vec<_>>(),
            "excluded": inventory.excluded.iter().map(row_json).collect::<Vec<_>>(),
            "tombstones": inventory.tombstones.iter().map(|row| json!({
                "key": row.key,
                "transformId": row.transform_id,
                "source": row.source,
                "sources": row.sources.iter().map(|source| json!({
                    "alias": source.alias,
                    "ref": source.source_ref,
                    "inputDigest": source.input_digest,
                    "rowCount": source.row_count,
                })).collect::<Vec<_>>(),
                "transformerPath": row.transformer_path,
                "recordId": row.record_id,
            })).collect::<Vec<_>>(),
            "states": inventory.states.iter().map(|st| json!({
                "transformId": st.transform_id,
                "transformerPath": st.transformer_path,
                "scriptDigest": st.script_digest,
                "forcedSchemaDrift": st.forced_schema_drift,
                "targetQn": st.target_qn,
                "recordId": st.record_id,
                "sources": st.sources.iter().map(|source| json!({
                    "alias": source.alias,
                    "ref": source.source_ref,
                    "inputDigest": source.input_digest,
                    "rowCount": source.row_count,
                })).collect::<Vec<_>>(),
            })).collect::<Vec<_>>(),
        })
        .to_string()
    }
}

/// Format one standalone KerML query expression — a query document's
/// statement, which is an expression rather than a model unit, so the
/// model formatter does not apply. `->` chain steps, invocation
/// arguments, and lambda-body results break one per line wherever the
/// flat form would outrun `width` (default 80); anything that fits
/// stays on one line. Rejects input that is not a single well-formed
/// expression, reporting the first diagnostic — a formatter must not
/// guess at broken input.
// The export boundary converts an optional string only when owned.
#[allow(clippy::needless_pass_by_value)]
#[wasm_bindgen(js_name = formatQuery)]
pub fn format_query(
    text: &str,
    indent: Option<String>,
    width: Option<usize>,
) -> Result<String, String> {
    sysmlv2_syntax::print::format_expression(
        text,
        sysmlv2_syntax::ast::Dialect::Sysml,
        parse_indent(indent.as_deref())?,
        width.unwrap_or(sysmlv2_syntax::print::FORMAT_QUERY_WIDTH),
    )
    .map_err(|d| {
        d.first()
            .map(|d| d.message.clone())
            .unwrap_or_else(|| "not an expression".into())
    })
}

/// Format SysML source text canonically under a project's lint
/// configuration: `config_json` is the sysmlint.json content (absent or
/// empty = engine defaults), read by the same parser the lint engine
/// uses, so the indentation style (`indentation` rule `style`/`size`)
/// and the multiline-chain threshold (`multiline-conditions` `min`)
/// can never disagree with what `lint` enforces. Parses, then re-prints
/// preserving notes and single blank lines. Rejects source with parse
/// diagnostics — a formatter must not guess at broken input — reporting
/// the first as `"<line>:<col> <message>"` (1-based, byte columns) so
/// hosts can map it onto their own spans.
// The export boundary converts an optional string only when owned.
#[allow(clippy::needless_pass_by_value)]
#[wasm_bindgen(js_name = formatSource)]
pub fn format_source_js(text: &str, config_json: Option<String>) -> Result<String, String> {
    let config = match config_json.as_deref() {
        None | Some("") => sysmlv2_lint::Config::default(),
        Some(json) => sysmlv2_lint::Config::from_json(json).map_err(|e| e.to_string())?,
    };
    sysmlv2_syntax::print::format_source_opts(
        text,
        sysmlv2_syntax::ast::Dialect::Sysml,
        sysmlv2_syntax::print::PrintOptions {
            indent: config.format_indent(),
            multiline_chains: config.format_chain_min(),
            ..sysmlv2_syntax::print::PrintOptions::default()
        },
    )
    .map_err(|diagnostics| {
        diagnostics
            .first()
            .map(|d| {
                let lc = LineIndex::new(text).line_col(d.span.start);
                format!("{}:{} {}", lc.line, lc.col, d.message)
            })
            .unwrap_or_else(|| "unparseable source".into())
    })
}

/// The id-normalized structural digest of exactly one member's text
/// (top-level form, as the canonical formatter emits it) — the
/// `structureDigest` provenance baseline. A
/// pure function of the text: parsed standalone, so it is independent
/// of the member's surroundings and of which session computed it.
/// Errors name the first parse diagnostic or a member-count violation.
#[wasm_bindgen(js_name = memberStructureDigest)]
pub fn member_structure_digest_js(text: &str) -> Result<String, String> {
    sysmlv2_model::structure::member_structure_digest(text)
}

/// Fingerprint of the effective canonicalization policy under a lint
/// configuration (absent/empty = engine defaults): resolved formatter
/// options + enabled auto-fix rules/options + the canonicalizer
/// schema version — the `canonicalizationDigest` provenance baseline.
// The export boundary converts an optional string only when owned.
#[allow(clippy::needless_pass_by_value)]
#[wasm_bindgen(js_name = canonicalizationDigest)]
pub fn canonicalization_digest_js(config_json: Option<String>) -> Result<String, String> {
    let cfg = match config_json.as_deref().filter(|s| !s.trim().is_empty()) {
        Some(text) => sysmlv2_lint::Config::from_json(text).map_err(|e| e.to_string())?,
        None => sysmlv2_lint::Config::default(),
    };
    Ok(sysmlv2_lint::canonicalization_digest(&cfg))
}

/// The lint rule inventory (for configuration UIs): JSON
/// `[{id, description, default, styles, families: [{key, label,
/// defaultStyle}], scopes: [{key, label, default, defaultStyle}]}]`
/// in the engine's documentation order — `default` = "off" | "hint" |
/// "info" | "warn" | "error" (a scope's null = inherits the rule; a
/// scope's non-null default is soft — rule-level "off" silences it),
/// `styles` the preset
/// names styled scopes accept (empty = severity-only scopes),
/// `families` the rule's family-level style options. Sourced from the
/// engine's own registry, so a form built from it can never drift
/// from the rules that actually run.
#[must_use]
#[wasm_bindgen(js_name = lintRules)]
pub fn lint_rules() -> String {
    let rules: Vec<serde_json::Value> = sysmlv2_lint::RULES
        .iter()
        .map(|r| {
            let scopes: Vec<serde_json::Value> = r
                .scopes
                .iter()
                .map(|s| {
                    json!({
                        "key": s.key,
                        "label": s.label,
                        "default": s.default.map(|d| d.as_str()),
                        "defaultStyle": s.default_style,
                    })
                })
                .collect();
            let families: Vec<serde_json::Value> = r
                .families
                .iter()
                .map(|(key, label, style)| {
                    json!({"key": key, "label": label, "defaultStyle": style})
                })
                .collect();
            let options: Vec<serde_json::Value> = r
                .options
                .iter()
                .map(|o| {
                    // One flat object: the option's identity followed by
                    // the fields its kind contributes.
                    let mut entry = serde_json::Map::new();
                    entry.insert("key".to_string(), json!(o.key));
                    entry.insert("label".to_string(), json!(o.label));
                    match &o.kind {
                        sysmlv2_lint::OptionKind::Int { default, min, zero } => {
                            entry.insert("kind".to_string(), json!("int"));
                            entry.insert("default".to_string(), json!(default));
                            entry.insert("min".to_string(), json!(min));
                            entry.insert("zero".to_string(), json!(zero));
                        }
                        sysmlv2_lint::OptionKind::Choice { default, values } => {
                            entry.insert("kind".to_string(), json!("choice"));
                            entry.insert("default".to_string(), json!(default));
                            entry.insert("values".to_string(), json!(values));
                        }
                    }
                    serde_json::Value::Object(entry)
                })
                .collect();
            json!({
                "id": r.id.id(),
                "description": r.description,
                "default": r.default.as_str(),
                "styles": r.styles,
                "families": families,
                "scopes": scopes,
                "options": options,
            })
        })
        .collect();
    serde_json::Value::Array(rules).to_string()
}

/// Repair sources (JSON `[{name, text}]`) that fail to parse so a
/// session can be built over what parsed: a member carrying a parse
/// error is removed (a failed member the parser skipped is recovered
/// from the tokens around the error), bodies left open at the end of a
/// unit get their closers appended, until each unit parses. Returns JSON
/// `{sources: [{name, text}], dropped: [{unit, start, end, line, col,
/// endLine, endCol, text, inserted, linesRemoved, wholeLines, message}],
/// unrepaired: [{unit, line, col, message}]}` — `dropped` in the
/// original texts' coordinates (byte offsets and byte columns, as `check`
/// reports; `inserted` holds appended closers, then `text` is empty and
/// the span is empty; `linesRemoved` and `wholeLines` map a line of the
/// repaired text back to the original), `unrepaired` naming units still
/// broken after the repair, positioned in their repaired text. Units
/// that parse come back unchanged.
#[wasm_bindgen(js_name = lenientSources)]
pub fn lenient_sources(sources_json: &str) -> Result<String, String> {
    let sources = parse_sources(sources_json)?;
    let result = sysmlv2_transform::lenient_sources(&sources);
    let sources: Vec<serde_json::Value> = result
        .sources
        .into_iter()
        .map(|(name, text)| json!({"name": name, "text": text}))
        .collect();
    let dropped: Vec<serde_json::Value> = result
        .dropped
        .into_iter()
        .map(|d| {
            json!({
                "unit": d.unit, "start": d.start, "end": d.end,
                "line": d.line, "col": d.col, "endLine": d.end_line, "endCol": d.end_col,
                "text": d.text, "inserted": d.inserted, "message": d.message,
                "linesRemoved": d.lines_removed, "wholeLines": d.whole_lines,
            })
        })
        .collect();
    let unrepaired: Vec<serde_json::Value> = result
        .unrepaired
        .into_iter()
        .map(|u| json!({"unit": u.unit, "line": u.line, "col": u.col, "message": u.message}))
        .collect();
    Ok(json!({"sources": sources, "dropped": dropped, "unrepaired": unrepaired}).to_string())
}

/// Check sources (JSON `[{name, text}]`) the way `sysmlv2 check` does:
/// per-unit parse and body-context validation always; referential and
/// semantic checks against the standard library when `lib_sources_json`
/// (same shape) is given. Returns findings as a JSON string:
/// `[{severity, stage, message, unit, line, col, endLine, endCol}]`
/// (1-based positions; the end pair spans the full diagnostic, so
/// markers cover the whole offending construct rather than just its
/// start). `stage` is `parse`, `context`, `referential` or `semantic`;
/// only `parse` findings keep a unit out of a session. A broken parse
/// is a finding, not an error.
// The export boundary converts an optional string only when owned.
#[allow(clippy::needless_pass_by_value)]
#[wasm_bindgen]
pub fn check(
    sources_json: &str,
    lib_sources_json: Option<String>,
    lib_snapshot: Option<Vec<u8>>,
) -> Result<String, String> {
    let sources = parse_sources(sources_json)?;
    let lib = lib_sources_json
        .as_deref()
        .map(|s| parse_library(s, lib_snapshot))
        .transpose()?;
    let findings = check_sources_with_library(&sources, lib.as_ref()).map_err(|e| e.to_string())?;
    let indexes: HashMap<&str, LineIndex> = sources
        .iter()
        .map(|(name, src)| (name.as_str(), LineIndex::new(src)))
        .collect();
    Ok(check_findings_json(findings, &indexes))
}

/// The parse and context stages of [`check`] alone — no model is built,
/// so the cost is a parse per unit. The partition step of a host that
/// then opens a [`Session`] over the units that parsed and reads the
/// resolution stages from [`Session::check`].
#[wasm_bindgen(js_name = checkSyntax)]
pub fn check_syntax(sources_json: &str) -> Result<String, String> {
    let sources = parse_sources(sources_json)?;
    let findings = sysmlv2_transform::check_sources_syntax(&sources);
    let indexes: HashMap<&str, LineIndex> = sources
        .iter()
        .map(|(name, src)| (name.as_str(), LineIndex::new(src)))
        .collect();
    Ok(check_findings_json(findings, &indexes))
}

/// The findings array `check` and its session twin share.
fn check_findings_json(
    findings: Vec<sysmlv2_transform::CheckFinding>,
    indexes: &HashMap<&str, LineIndex>,
) -> String {
    let findings: Vec<serde_json::Value> = findings
        .into_iter()
        .map(|f| {
            let end = indexes
                .get(f.unit.as_str())
                .map(|li| li.line_col(f.span.end));
            let mut obj = json!({
                "severity": match f.severity {
                    sysmlv2_transform::Severity::Error => "error",
                    sysmlv2_transform::Severity::Warning => "warning",
                },
                "stage": f.stage.as_str(),
                "message": f.message,
                "unit": f.unit,
                "line": f.line,
                "col": f.col,
            });
            if let Some(end) = end {
                obj["endLine"] = json!(end.line);
                obj["endCol"] = json!(end.col);
            }
            obj
        })
        .collect();
    serde_json::Value::Array(findings).to_string()
}

/// JSON envelope shared by the delta-apply surfaces.
fn apply_report_value(report: &sysmlv2_cbor::ApplyReport) -> serde_json::Value {
    serde_json::json!({
        "baseMatched": report.base_matched,
        "noopDeletes": report.noop_deletes,
        "upsertedUpdates": report.upserted_updates,
        "replacedCreates": report.replaced_creates,
        // The result's unit structure when the delta carries one,
        // same row shape as describe's units.
        "units": report
            .units
            .iter()
            .map(|(i, p)| serde_json::json!({ "index": i, "path": p }))
            .collect::<Vec<_>>(),
    })
}

fn apply_report_json(result: &serde_json::Value, report: &sysmlv2_cbor::ApplyReport) -> String {
    serde_json::json!({ "result": result, "report": apply_report_value(report) }).to_string()
}

/// The canonical spelling of an element name:
/// JSON `{"spelling", "quoted"}` — `spelling` is exactly what the
/// printer emits (bare, or a single-quoted restricted name for reserved
/// words and non-basic characters) and `quoted` says which. Errors when
/// the string cannot be a name (empty). `dialect` is `"sysml"` or
/// `"kerml"`; the reserved-word sets differ, and an omitted dialect
/// means SysML here (unlike `spellReference`, whose omitted dialect
/// means either). Generators that mint
/// names from external vocabularies call this instead of copying the
/// parser's keyword table.
// The export boundary converts an optional string only when owned.
#[allow(clippy::needless_pass_by_value)]
#[wasm_bindgen(js_name = canonicalName)]
pub fn canonical_name_js(name: &str, dialect: Option<String>) -> Result<String, String> {
    let dialect = parse_dialect(dialect.as_deref())?.unwrap_or(sysmlv2_syntax::ast::Dialect::Sysml);
    let c = sysmlv2_syntax::name::canonical_name(dialect, name).map_err(|e| e.to_string())?;
    Ok(json!({ "spelling": c.spelling, "quoted": c.quoted }).to_string())
}

/// Respell a canonical qualified name — as `qualifiedName` reports it,
/// or as interchange JSON carries it — as reference text that parses:
/// reserved words and non-basic names quoted per segment
/// (`spellReference("part::view")` is `'part'::'view'`). `dialect` is
/// `"sysml"` or `"kerml"` for text going into a unit of that kind;
/// omitted, the spelling re-parses in either (every reserved word of
/// both dialects is quoted). Hosts generating `import`/`expose` lines
/// call this instead of quoting segments themselves.
// The export boundary converts an optional string only when owned.
#[allow(clippy::needless_pass_by_value)]
#[wasm_bindgen(js_name = spellReference)]
pub fn spell_reference_js(qualified_name: &str, dialect: Option<String>) -> Result<String, String> {
    let dialect = parse_dialect(dialect.as_deref())?;
    Ok(sysmlv2_syntax::name::respell_canonical(
        dialect,
        qualified_name,
    ))
}

/// `"sysml"` / `"kerml"` → the dialect; absent or empty → `None`.
fn parse_dialect(dialect: Option<&str>) -> Result<Option<sysmlv2_syntax::ast::Dialect>, String> {
    match dialect {
        None | Some("") => Ok(None),
        Some("sysml") => Ok(Some(sysmlv2_syntax::ast::Dialect::Sysml)),
        Some("kerml") => Ok(Some(sysmlv2_syntax::ast::Dialect::Kerml)),
        Some(d) => Err(format!("dialect must be \"sysml\" or \"kerml\", got {d:?}")),
    }
}

/// The toolkit version this module was built from.
#[must_use]
#[wasm_bindgen]
pub fn version() -> String {
    env!("CARGO_PKG_VERSION").to_string()
}

/// Enable or disable expanding quoted power-product unit spellings
/// (`'m³⋅s⁻²'` parsed into `m³/s²` when the unit element carries no
/// definition or conversion of its own). On by default; module-wide,
/// so hosts flip it once at startup or on a settings change.
#[wasm_bindgen(js_name = setUnitSpellingExpansion)]
pub fn set_unit_spelling_expansion(on: bool) {
    sysmlv2_model::eval::set_unit_spelling_expansion(on);
}

/// Encode any compact interchange element array (JSON text) to s2c
/// bytes (`CBOR.md`) — the element-scoped export path, where the host
/// filters a subtree out of the session's compact array first.
/// Whole-session exports use [`Session::to_compact_cbor`]. References
/// to elements outside the array travel in the payload's external
/// table, so a filtered subtree is a valid payload.
#[wasm_bindgen(js_name = encodeCompactCbor)]
pub fn encode_compact_cbor(json: &str) -> Result<Vec<u8>, String> {
    let value: serde_json::Value = serde_json::from_str(json).map_err(|e| e.to_string())?;
    sysmlv2_cbor::to_compact_cbor(&value).map_err(|e| e.to_string())
}

/// Canonicalize a compact interchange element array (JSON text):
/// materialize every element through its metaclass field table and
/// re-emit with each absent property spelled at its metaclass-specific
/// default (`isUnique` true, `isAbstract` false, `visibility`
/// "public", empty lists, nulls, the `elementId` mirror of `@id`).
/// Present values and `@id`s are preserved verbatim, element order is
/// untouched, and the result is independent of the input's default
/// elision/spelling split — so producers that wire-elide schema
/// defaults and producers that spell them explicitly digest
/// identically. The CBOR round-trip does NOT do this (encode/decode is
/// presence-faithful); this is the rehydration entry point. Strict
/// like the encoder: unknown `@type`s and non-compact-form keys are
/// errors.
#[wasm_bindgen(js_name = canonicalizeCompact)]
pub fn canonicalize_compact(json: &str) -> Result<String, String> {
    sysmlv2_cbor::canonicalize_compact(json).map_err(|e| e.to_string())
}

/// The mirror twin of [`canonicalize_compact`]: re-spell a compact
/// interchange element array (JSON text) in the **graph-normal**
/// (stored/wire-normal) form a graph-backed store reconstructs after
/// materializing it as triples — default-valued properties elided,
/// derived canonical properties (`owner`, `qualifiedName`, …) dropped
/// as such a store's ingest drops them, `elementId` always spelled,
/// absent ownership backpointers completed by first-claimant
/// derivation from the forward ownership lists, elements sorted by
/// `@id`. `stateDigestOf(graphNormalizeCompact(doc))` is the digest
/// such a store reconstructs after ingesting `doc`, so snapshots (and
/// strict deltas whose base digests live in the same domain) encoded
/// from this spelling pass the store's end-to-end digest
/// verification. Idempotent; strict on unknown `@type`s, missing
/// `@id`s, and keys outside the full schema.
#[wasm_bindgen(js_name = graphNormalizeCompact)]
pub fn graph_normalize_compact(json: &str) -> Result<String, String> {
    sysmlv2_cbor::graph_normalize_compact(json).map_err(|e| e.to_string())
}

/// State digest of a compact interchange element array (JSON text) —
/// over the document exactly as given, with no session lift in
/// between. This is the digest a delta names its base by
/// ([`Session::state_digest`] digests the *session's* model instead;
/// lifting a payload file into a session re-derives ids, so only the
/// raw digest can say whether a given payload file is a delta's
/// base).
#[wasm_bindgen(js_name = stateDigestOf)]
pub fn state_digest_of(json: &str) -> Result<String, String> {
    let value: serde_json::Value = serde_json::from_str(json).map_err(|e| e.to_string())?;
    sysmlv2_cbor::state_digest(&value)
        .map(|u| u.to_string())
        .map_err(|e| e.to_string())
}

/// s2c delta between two compact interchange element arrays (JSON
/// text), read base → target. With `rebase`, the target's element ids
/// are first rebased onto the base by ownership-path matching
/// (`sysmlv2_cbor::rebase_ids`) so independently derived payloads —
/// different unit names, separate lifts, foreign producers — diff by
/// structure instead of full create/delete churn; a rebase refusal
/// (id collision) falls back to the raw target, which still yields a
/// correct (just larger) delta. Same-session payloads should pass
/// `rebase: false`: session identity survives moves, which path
/// matching cannot see.
/// Optional tail arguments: `units_json` — the target's unit
/// structure as JSON `[[index, path], …]` (indices into the target
/// array as passed) rides the payload so file adds/renames/deletes
/// travel with the delta (strict only). `elide` — id-elided
/// created records encoded resolver-less: foreign ids land in
/// the exception map, which is always safe (the applier's digest gate
/// proves recovery); apply through a session for library context.
#[wasm_bindgen(js_name = deltaCborBetween)]
pub fn delta_cbor_between(
    base_json: &str,
    target_json: &str,
    portable: bool,
    rebase: bool,
    units_json: Option<String>,
    elide: Option<bool>,
) -> Result<Vec<u8>, String> {
    let base: serde_json::Value = serde_json::from_str(base_json).map_err(|e| e.to_string())?;
    let mut target: serde_json::Value =
        serde_json::from_str(target_json).map_err(|e| e.to_string())?;
    if rebase {
        if let Ok(rebased) = sysmlv2_cbor::rebase_ids(&base, &target) {
            target = rebased;
        }
    }
    let units: Vec<(usize, String)> = match units_json {
        Some(s) => serde_json::from_str(&s).map_err(|e| e.to_string())?,
        None => Vec::new(),
    };
    let opts = sysmlv2_cbor::DeltaOptions::new()
        .with_portable(portable)
        .with_units(units);
    if elide.unwrap_or(false) {
        sysmlv2_cbor::delta_compact_cbor_elided(&base, &target, &opts, &|_| None)
            .map_err(|e| e.to_string())
    } else {
        sysmlv2_cbor::delta_compact_cbor(&base, &target, &opts).map_err(|e| e.to_string())
    }
}

/// The s2c codec tables as JSON, for hosts that label raw payload
/// structure (the IDE's CBOR explorer): metaclass wire codes with
/// their per-ordinal field tables (property name, kind code, enum
/// table index) and the closed enum vocabularies. `full` selects the
/// full-form ordinal space; the compact tables cover every ingest
/// payload. Kind codes are the `cbor_tables` constants (0 bool,
/// 1 str, 2 str list, 3 ref, 4 ref list, 5 enum, 6 literal,
/// 7 element id).
#[must_use]
#[wasm_bindgen(js_name = codecTables)]
pub fn codec_tables(full: bool) -> String {
    let set = if full {
        sysmlv2_cbor::tables::FULL_METACLASS_FIELDS
    } else {
        sysmlv2_cbor::tables::METACLASS_FIELDS
    };
    let metaclasses: Vec<serde_json::Value> = set
        .iter()
        .map(|(name, fields)| {
            json!({
                "name": name,
                "fields": fields
                    .iter()
                    .map(|(prop, kind, etbl, _)| json!({
                        "prop": prop,
                        "kind": kind,
                        "enum": if *etbl == 255 { serde_json::Value::Null } else { json!(etbl) },
                    }))
                    .collect::<Vec<_>>(),
            })
        })
        .collect();
    let enums: Vec<serde_json::Value> = sysmlv2_cbor::tables::ENUM_NAMES
        .iter()
        .zip(sysmlv2_cbor::tables::ENUM_TABLES)
        .map(|(name, values)| json!({ "name": name, "values": values }))
        .collect();
    json!({
        "tablesVersion": sysmlv2_cbor::tables::CBOR_TABLES_VERSION,
        "metaclasses": metaclasses,
        "enums": enums,
    })
    .to_string()
}

/// Inspect an s2c payload without decoding or applying it: form,
/// header versions, sizes and counts, and for deltas the
/// digests, claims, and change breakdown — the summary a host renders
/// as a payload preview. Returns the summary as JSON text.
#[wasm_bindgen(js_name = describeCbor)]
pub fn describe_cbor(bytes: &[u8]) -> Result<String, String> {
    sysmlv2_cbor::describe(bytes)
        .map(|v| v.to_string())
        .map_err(|e| e.to_string())
}

/// The push-driven language server (`sysmlv2-lsp`, browser transport):
/// feed one client→server LSP JSON-RPC message, get the server→client
/// messages it produced. A tiny worker shim on the JS side is the
/// transport: `postMessage` objects in, `handle` strings through,
/// `postMessage` objects out. Serves the syntax tier (diagnostics,
/// symbols, semantic tokens, formatting, navigation over open
/// documents); workspace/library-aware semantics stay with [`Session`]
/// and [`check`] — the kernel's job.
#[wasm_bindgen]
pub struct LspServer {
    inner: sysmlv2_lsp::PushServer,
}

impl Default for LspServer {
    fn default() -> LspServer {
        LspServer::new()
    }
}

#[wasm_bindgen]
impl LspServer {
    /// The syntax-tier-only server (no standard library).
    /// NOTE: a fallible `#[wasm_bindgen(constructor)]` (Result return)
    /// leaves the JS object with a null pointer — keep the constructor
    /// infallible and use [`Self::with_library`] for the library shape.
    #[must_use]
    #[wasm_bindgen(constructor)]
    pub fn new() -> LspServer {
        LspServer {
            inner: sysmlv2_lsp::PushServer::new(),
        }
    }

    /// A server whose navigation and completions see the standard
    /// library: sources as JSON `[{name, text}]`, optionally with the
    /// sealed resolution snapshot recorded against the same units.
    #[wasm_bindgen(js_name = withLibrary)]
    pub fn with_library(
        lib_sources_json: &str,
        lib_snapshot: Option<Vec<u8>>,
    ) -> Result<LspServer, String> {
        Ok(LspServer {
            inner: sysmlv2_lsp::PushServer::with_library_sources(
                parse_sources(lib_sources_json)?,
                lib_snapshot,
            ),
        })
    }

    /// Seed (or replace) the navigation workspace: every model unit the
    /// host knows about, as JSON `[{name, text}]` where `name` is the
    /// same uri string the client opens the document under. Open
    /// documents overlay these, so definition/references/hover cross
    /// into units that are not open.
    ///
    /// Returns server→client messages the re-seed produced — the
    /// `workspace/inlayHint/refresh` / `workspace/codeLens/refresh`
    /// requests that make supporting clients re-pull answers the old
    /// session gave. Relay them exactly like [`Self::handle`] output.
    #[wasm_bindgen(js_name = setWorkspace)]
    pub fn set_workspace(&mut self, sources_json: &str) -> Result<Vec<String>, String> {
        self.inner
            .set_workspace_sources(parse_sources(sources_json)?);
        self.inner.take_outbound().map_err(|e| e.to_string())
    }

    /// Handle one JSON-RPC message string; returns produced messages.
    pub fn handle(&mut self, msg: &str) -> Result<Vec<String>, String> {
        self.inner.handle(msg).map_err(|e| e.to_string())
    }

    /// Drop cached navigation sessions after a host-side engine
    /// reconfiguration (e.g. [`set_unit_spelling_expansion`]) that
    /// changes answers without any source changing. Returns the
    /// refresh requests to relay, like `setWorkspace`.
    #[wasm_bindgen(js_name = invalidateSessions)]
    pub fn invalidate_sessions(&mut self) -> Result<Vec<String>, String> {
        self.inner.invalidate_sessions();
        self.inner.take_outbound().map_err(|e| e.to_string())
    }

    /// Set whether evaluated-value inlay hints that restate the
    /// declared expression verbatim are suppressed (default on).
    /// Returns the refresh requests to relay, like
    /// `setWorkspace`.
    #[wasm_bindgen(js_name = setHideRedundantValueHints)]
    pub fn set_hide_redundant_value_hints(&mut self, on: bool) -> Result<Vec<String>, String> {
        self.inner.set_hide_redundant_value_hints(on);
        self.inner.take_outbound().map_err(|e| e.to_string())
    }

    /// Set whether accepting a unit completion inside an untyped
    /// attribute's quantity bracket also declares the type the unit
    /// determines (default on). Takes effect on the next completion
    /// request.
    #[wasm_bindgen(js_name = setInferUnitTypes)]
    pub fn set_infer_unit_types(&mut self, on: bool) {
        self.inner.set_infer_unit_types(on);
    }
}
