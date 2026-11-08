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

use sysmlv2_lsp::{Encoding, Mapper, library_uri_under};
use sysmlv2_model::check::ConstraintVerdict;
use sysmlv2_model::eval::Value as EvalValue;
use sysmlv2_model::json::ElementRef;
use sysmlv2_solve::{PropagateConfig, PropagateOutcome};
use sysmlv2_syntax::parser::parse_expression;
use sysmlv2_syntax::span::{LineIndex, Span};
use sysmlv2_transform::{
    GraphFormat, Indent, Library, Session as TSession, check_sources_with_library,
};

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

/// Parse an interchange JSON payload, read the way Flexo MMS returns it
/// when `flexo` is set ([`sysmlv2_transform::unwrap_flexo`]).
fn interchange_value(json: &str, flexo: Option<bool>) -> Result<serde_json::Value, String> {
    let value = serde_json::from_str(json).map_err(|e| e.to_string())?;
    Ok(if flexo == Some(true) {
        sysmlv2_transform::unwrap_flexo(value).map_err(|e| e.to_string())?
    } else {
        value
    })
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

/// A graph format by its name on the JavaScript side: `"legacy"` (scheme 2,
/// the default) or `"canonical"` (the opt-in scheme 3); an absent or empty
/// name is the default.
fn parse_graph_format(name: Option<&str>) -> Result<GraphFormat, String> {
    match name {
        None | Some("" | "legacy") => Ok(GraphFormat::LegacyV2),
        Some("canonical") => Ok(GraphFormat::CanonicalV3),
        Some(other) => Err(format!(
            "unknown graph format {other:?}: legacy or canonical"
        )),
    }
}

fn graph_format_name(format: GraphFormat) -> &'static str {
    match format {
        GraphFormat::LegacyV2 => "legacy",
        GraphFormat::CanonicalV3 => "canonical",
        _ => "unknown",
    }
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
/// valueUnits?, showNotes?, showMetadata?, showInherited?, showLib?,
/// showImported?, lineStyle?, stdColor?, linkTemplate?}` — all
/// optional, defaults match Python. `roots` restricts an all-roots
/// diagram to the named top-level elements (ignored when `element`
/// scopes to one subtree). `valueUnits` is `"si"` (the default) or
/// `"asWritten"`: the units a `= value` quantity shows in.
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
    value_units: Option<String>,
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

/// `{open: [selector…], noteBudget, leafBudget, unbounded: [selector…],
/// fullWithin?}`: which containers emit their members, how many notes
/// draw as cards per cluster, how many members draw per open container,
/// and which open containers draw every member regardless (a selector
/// that does not resolve is ignored). `fullWithin` is a finite number: when
/// the summary's would-draw total — its node count plus every node's
/// `summary.hidden` ([`sysmlv2_viz::summary_would_draw`]) — is at most
/// that, the reply is the full graph instead, exactly as a request
/// without `summary` emits it, marked `full: true` and without the
/// `summary` reply field.
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
    #[serde(default)]
    full_within: Option<f64>,
}

fn default_note_budget() -> usize {
    200
}

fn default_leaf_budget() -> usize {
    500
}

/// [`Session::tree`]'s options: the root selection and the CLI's
/// `--depth`, `--no-references`, `--implied` and `--ids`.
#[derive(Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct TreeIn {
    #[serde(default)]
    root: Option<Selector>,
    #[serde(default)]
    depth: Option<usize>,
    #[serde(default = "yes")]
    references: bool,
    #[serde(default)]
    implied: bool,
    #[serde(default)]
    ids: bool,
}

/// [`Session::outline`]'s budgets: `{outlineNodes?, outlineDepth?,
/// shapeNodes?, shapeDepth?}`.
#[derive(Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct OutlineIn {
    #[serde(default = "default_outline_nodes")]
    outline_nodes: usize,
    #[serde(default = "default_outline_depth")]
    outline_depth: usize,
    #[serde(default = "default_shape_nodes")]
    shape_nodes: usize,
    #[serde(default = "default_shape_depth")]
    shape_depth: usize,
}

fn default_outline_nodes() -> usize {
    4000
}

fn default_outline_depth() -> usize {
    24
}

fn default_shape_nodes() -> usize {
    20000
}

fn default_shape_depth() -> usize {
    64
}

/// One element of the outline tree (fields in the order a host's own
/// walk builds them).
#[derive(Serialize)]
#[serde(rename_all = "camelCase")]
struct OutlineNodeOut {
    name: Option<String>,
    metaclass: &'static str,
    qualified_name: Option<String>,
    children: Vec<OutlineNodeOut>,
}

/// One named element of the shape: `owner` indexes the nearest named
/// ancestor recorded before it, `-1` when there is none.
#[derive(Serialize)]
#[serde(rename_all = "camelCase")]
struct ShapeNodeOut {
    id: String,
    name: String,
    qualified_name: String,
    metaclass: &'static str,
    owner: i64,
}

/// The state of one [`Session::outline`] walk.
struct OutlineWalk {
    opts: OutlineIn,
    /// Outline nodes still to hand out, claimed in visiting order.
    outline_left: usize,
    shape: Vec<ShapeNodeOut>,
    /// A budget cut the shape short: a named element left out, or an
    /// element at the depth limit with members.
    truncated: bool,
}

/// A field of [`Session::rows`]: one per-element read, by the name of
/// the method that answers it.
enum RowField {
    Name,
    ShortName,
    QualifiedName,
    ReferenceSpelling,
    Metaclass,
    Owner,
    IsLibraryElement,
    ValueSource,
    ValueIsDefault,
    Docs,
    DeclarationSite,
    MemberExtent,
    Property(String),
    Derived(String),
}

impl RowField {
    fn parse(field: &str) -> Result<RowField, String> {
        if let Some(name) = field.strip_prefix("property:") {
            return Ok(RowField::Property(name.to_string()));
        }
        if let Some(name) = field.strip_prefix("derived:") {
            return Ok(RowField::Derived(name.to_string()));
        }
        Ok(match field {
            "name" => RowField::Name,
            "shortName" => RowField::ShortName,
            "qualifiedName" => RowField::QualifiedName,
            "referenceSpelling" => RowField::ReferenceSpelling,
            "metaclass" => RowField::Metaclass,
            "owner" => RowField::Owner,
            "isLibraryElement" => RowField::IsLibraryElement,
            "valueSource" => RowField::ValueSource,
            "valueIsDefault" => RowField::ValueIsDefault,
            "docs" => RowField::Docs,
            "declarationSite" => RowField::DeclarationSite,
            "memberExtent" => RowField::MemberExtent,
            _ => return Err(format!("unknown row field: {field}")),
        })
    }
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

thread_local! {
    /// The units this module shows evaluated quantities in unless a
    /// request names its own: [`set_value_units`].
    static VALUE_UNITS: std::cell::Cell<sysmlv2_model::eval::UnitDisplay> =
        const { std::cell::Cell::new(sysmlv2_model::eval::UnitDisplay::Si) };
    /// The directory the host serves the library's units under, as the
    /// language server keeps it, under which this module names a library
    /// unit in a position answer; `None` names it under the `sysmlv2-lib:`
    /// scheme: [`set_library_root`].
    static LIBRARY_ROOT: std::cell::RefCell<Option<sysmlv2_lsp::LibraryRoot>> =
        const { std::cell::RefCell::new(None) };
}

/// Where this module names a library unit in a position answer (find-
/// usages' `unit`): under the host's library directory when one is set,
/// else under the `sysmlv2-lib:` scheme.
fn library_unit_uri(name: &str) -> String {
    LIBRARY_ROOT.with_borrow(|root| library_uri_under(root.as_ref(), name))
}

/// Name library units in position answers under `root`, the directory
/// the host serves the library's units as files of, as a uri (`null` or
/// an empty string names them under the `sysmlv2-lib:` scheme again, the
/// default). `dirs_json`, when given, is a JSON object naming, for each
/// bundle directory the host shows under another name, that name
/// (`{"local-packages": "Own Libraries"}`), applied to the first
/// directory of a unit's name both ways. The language server's
/// `initializationOptions.libraryRoot` and `libraryDirs` are the same
/// settings for its locations; a host that serves the library as a
/// directory gives both the same, so a `Session`'s find-usages and the
/// server's references name a library unit the same way. Throws on a
/// root that is no uri, or directories that are not an object of
/// single-segment names. Module-wide, like
/// [`setUnitSpellingExpansion`](set_unit_spelling_expansion).
#[wasm_bindgen(js_name = setLibraryRoot)]
pub fn set_library_root(root: Option<String>, dirs_json: Option<String>) -> Result<(), String> {
    let root = match root.as_deref().filter(|r| !r.is_empty()) {
        Some(uri) => {
            let root = sysmlv2_lsp::LibraryRoot::new(uri)
                .ok_or_else(|| format!("library root `{uri}` is not a uri"))?;
            let dirs: std::collections::BTreeMap<String, String> = match dirs_json.as_deref() {
                Some(json) if !json.trim().is_empty() => {
                    serde_json::from_str(json).map_err(|e| {
                        format!("library directories: expected an object of names: {e}")
                    })?
                }
                _ => std::collections::BTreeMap::new(),
            };
            Some(root.with_dirs(dirs).ok_or_else(|| {
                "library directories: directory names must be non-empty path segments with unique, non-conflicting mappings".to_string()
            })?)
        }
        None => None,
    };
    LIBRARY_ROOT.with_borrow_mut(|slot| *slot = root);
    Ok(())
}

/// The library root [`setLibraryRoot`](set_library_root) set, as kept
/// (ending in `/`); `null` when library units are named under the
/// `sysmlv2-lib:` scheme.
#[must_use]
#[wasm_bindgen(js_name = libraryRoot)]
pub fn library_root() -> Option<String> {
    LIBRARY_ROOT.with_borrow(|root| root.as_ref().map(|r| r.uri().to_string()))
}

/// A `valueUnits` option: `"si"` or `"asWritten"`; absent, the module's
/// [`setValueUnits`](set_value_units) choice.
fn parse_value_units(spec: Option<&str>) -> Result<sysmlv2_model::eval::UnitDisplay, String> {
    spec.map_or(
        Ok(VALUE_UNITS.get()),
        sysmlv2_model::eval::UnitDisplay::parse,
    )
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

/// Where `span` of `unit` lies, positioned as an editor positions it:
/// JSON `{unit, line, col, endLine, endCol}` — the unit's name, 1-based
/// lines, and columns counted in UTF-16 code units — which is the
/// language server's location for the same span, one-based. A unit of
/// an in-memory library is named as the server names it: under the
/// library directory the host set ([`set_library_root`]), else under
/// the `sysmlv2-lib:/` scheme a host serves the library's text under.
/// `mappers` memoizes a unit's line table across the sites of one
/// answer. A unit whose text the session does not hold has no position.
fn unit_location<'a>(
    session: &'a TSession,
    mappers: &mut HashMap<usize, Option<(String, Mapper<'a>)>>,
    unit: usize,
    span: Span,
) -> Option<serde_json::Value> {
    let (name, mapper) = mappers
        .entry(unit)
        .or_insert_with(|| {
            let (name, text) = session
                .units()
                .find(|(i, _, _)| *i == unit)
                .map(|(_, name, text)| (name.to_string(), text))
                .or_else(|| {
                    session
                        .library_unit(unit)
                        .map(|(name, text)| (library_unit_uri(name), text))
                })?;
            Some((name, Mapper::new(text, Encoding::Utf16)))
        })
        .as_ref()?;
    let range = mapper.range(span);
    Some(json!({
        "unit": name,
        "line": range.start.line + 1,
        "col": range.start.character + 1,
        "endLine": range.end.line + 1,
        "endCol": range.end.character + 1,
    }))
}

/// A verdict's feature bindings as the verify report spells them: `{feature,
/// value?, unitName?, line?, col?}`, values in the units `units` chooses. A
/// declaration in a library unit has no position (library sources are not
/// held).
fn bindings_json(
    bindings: &[sysmlv2_model::check::ConstraintBinding],
    units: sysmlv2_model::eval::UnitDisplay,
    session: &TSession,
    names: &HashMap<usize, String>,
    indexes: &mut HashMap<usize, LineIndex>,
) -> Vec<serde_json::Value> {
    bindings
        .iter()
        .map(|b| {
            let pos = b
                .site
                .filter(|(unit, _)| session.source(*unit).is_some())
                .map(|(unit, span)| {
                    let lc = unit_line_index(indexes, session, unit).line_col(span.start);
                    (unit, lc)
                });
            json!({
                "feature": b.feature,
                "value": b.value_in(units),
                "unitName": pos.and_then(|(u, _)| names.get(&u)),
                "line": pos.map(|(_, lc)| lc.line),
                "col": pos.map(|(_, lc)| lc.col),
            })
        })
        .collect()
}

/// The CLI's "why" suffix on a violated verdict line: the evaluated values
/// of its bound references (`VIOLATED (with reserveKg = 0.10)`).
fn with_values(
    detail: String,
    bindings: &[sysmlv2_model::check::ConstraintBinding],
    units: sysmlv2_model::eval::UnitDisplay,
) -> String {
    let vals: Vec<String> = bindings
        .iter()
        .filter_map(|b| b.value_in(units).map(|v| format!("{} = {v}", b.feature)))
        .collect();
    if vals.is_empty() {
        detail
    } else {
        format!("{detail} (with {})", vals.join(", "))
    }
}

/// One edit-batch operation as JSON (the `edit` method takes an array):
/// `{op: "rename", target, newName}` · `{op: "setFeatureValue", target,
/// expr}` · `{op: "setFeatureType", target, type}` (replace the written
/// `: T` clause in place, or add one where none exists) · `{op:
/// "setRedefinedFeature", target, feature}` (replace the first written
/// `:>>` / `redefines` target, a name or a chain, with `feature` as
/// written) · `{op: "removeFeatureValue", target}` (the `= …`, `:= …` /
/// `default …` clause goes, its operator with it) · `{op:
/// "setCommentBody", target, body}` (a comment's or documentation's
/// `/* … */` body becomes `body`, the text as a reader sees it; the
/// keyword, name, `about` list and locale stay as written) · `{op:
/// "insertMember", owner, text, index?}` (`index` = slot among the
/// owner's current members: the new member goes on the line after the
/// one before that slot; omitted = append; a unit's root namespace as
/// `owner` writes at that unit's top level; the slot is held before a
/// body's trailing result expression, a subject before the first
/// parameter, other inputs after the subject, and past the `then`
/// members that start from the member before the slot; a second subject,
/// objective, `entry`/`do`/`exit` action, rendering or return
/// parameter in one owner is refused) · `{op: "insertTopLevel",
/// unit, text}`
/// · `{op: "remove", target}` (the `then` members written right after
/// the target go with it, since they start from it: `state a; then
/// b;`, `entry; then idle;`) · `{op: "replaceMember", target, text}`
/// (identity-preserving update: swaps the declaration for exactly one
/// parsed member, respells outside references on a declared-name
/// change, and judges validity on the post-edit model — no pre-state
/// outside-reference refusal) · `{op: "moveMember", target, newOwner?,
/// index?}` (omitted `newOwner` = reorder within the current owner;
/// `index` = slot among the destination's current members, self
/// excluded, omitted = append; held and refused as for `insertMember`;
/// the `then` members written after the target move with it, as they
/// go with it on `remove`) · `{op: "addUnit", unit}` (create a
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
    #[serde(rename = "setRedefinedFeature")]
    SetRedefinedFeature { target: String, feature: String },
    #[serde(rename = "removeFeatureValue")]
    RemoveFeatureValue { target: String },
    #[serde(rename = "setCommentBody")]
    SetCommentBody { target: String, body: String },
    #[serde(rename = "insertMember")]
    InsertMember {
        owner: String,
        text: String,
        #[serde(default)]
        index: Option<u32>,
    },
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
    SetRedefinedFeature(ElementRef, String),
    RemoveFeatureValue(ElementRef),
    SetCommentBody(ElementRef, String),
    InsertMember(ElementRef, String, Option<usize>),
    InsertTopLevel(String, String),
    AddUnit(String),
    Remove(ElementRef),
    ReplaceMember(ElementRef, String),
    MoveMember(ElementRef, ElementRef, Option<usize>),
}

/// A closure policy by its name (`closurePolicy`, `setClosurePolicy`,
/// `toFullJson`): `"passthrough"`, `"closure"` or `"closure-implied"`.
fn parse_closure_policy(name: &str) -> Result<sysmlv2_model::json::ClosurePolicy, String> {
    use sysmlv2_model::json::ClosurePolicy;
    Ok(match name {
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
    })
}

/// A set of model sources (text or interchange JSON) with their resolved
/// model — `sysmlv2_transform::Session` behind a JS-shaped API.
#[wasm_bindgen]
pub struct Session {
    inner: TSession,
    gen: u64,
}

impl Session {
    /// Whether the session's compact emissions read the rows its build
    /// made instead of building the model again (see
    /// `ResolvedModel::emits_built_rows`). Not part of the JS surface: the
    /// binding's tests hold the reads a host makes to keeping it.
    #[doc(hidden)]
    pub fn emits_built_rows(&self) -> bool {
        self.inner.resolved_ref().emits_built_rows()
    }

    fn guard(&self, e: &Element) -> Result<(), String> {
        if e.gen != self.gen {
            return Err(
                "stale handle: the session was rebuilt since it was minted (re-resolve)"
                    .to_string(),
            );
        }
        Ok(())
    }

    /// The nodes of the ownership tree the options select (see
    /// [`Self::tree`]).
    fn tree_nodes(
        &mut self,
        opts_json: Option<&str>,
    ) -> Result<Vec<sysmlv2_model::inspect::TreeNode>, String> {
        let opts: TreeIn =
            serde_json::from_str(opts_json.filter(|s| !s.is_empty()).unwrap_or("{}"))
                .map_err(|e| format!("bad options: {e}"))?;
        let root = match &opts.root {
            Some(sel) => Some(resolve_selector(self.inner.resolved(), sel).ok_or_else(
                || match sel {
                    Selector::Name(name) => format!("element not found: {name}"),
                    Selector::Id { element_id } => format!("element not found: {element_id}"),
                },
            )?),
            None => None,
        };
        let options = sysmlv2_model::inspect::TreeOptions {
            depth: opts.depth,
            references: opts.references,
            implied: opts.implied,
            ids: opts.ids,
        };
        Ok(sysmlv2_model::inspect::tree(
            self.inner.resolved(),
            root,
            &options,
        ))
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
        let value_units = parse_value_units(opts.value_units.as_deref())
            .map_err(|e| format!("bad options: valueUnits: {e}"))?;
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
            .with_value_units(value_units)
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

    /// Top-level user elements (see [`Self::roots`]).
    fn root_refs(&mut self) -> Vec<ElementRef> {
        let r = self.inner.resolved();
        let all: Vec<ElementRef> = r.user_elements().collect();
        let mut tops = Vec::new();
        for e in all {
            if r.owner(e).is_none() && r.element_type(e) == "Namespace" {
                tops.extend(r.owned_members(e));
            }
        }
        tops
    }

    /// The name an outline shows: `derived(e, "name")` when that is a
    /// string, else the declared name. Errors as `derived` does.
    fn display_name(&mut self, e: ElementRef) -> Result<Option<String>, String> {
        let gen = self.gen;
        match self.derived_json(&Element { e, gen }, "name")? {
            serde_json::Value::String(name) => Ok(Some(name)),
            _ => Ok(self.inner.resolved().element_name(e).map(str::to_string)),
        }
    }

    /// Visit `e` at `depth` under the shape node `owner` (see
    /// [`Self::outline`]): its outline node, or `None` once the outline
    /// budget is spent.
    fn outline_visit(
        &mut self,
        walk: &mut OutlineWalk,
        e: ElementRef,
        owner: i64,
        depth: usize,
    ) -> Result<Option<OutlineNodeOut>, String> {
        let name = self.display_name(e)?;
        let r = self.inner.resolved();
        let qualified_name = r.element_qualified_name(e);
        let metaclass = r.element_type(e);
        // Shape: named elements only. An anonymous one is still walked,
        // its named members re-parented onto its nearest named ancestor.
        let mut this = owner;
        if let (Some(n), Some(q)) = (&name, &qualified_name) {
            if !n.is_empty() && !q.is_empty() {
                if walk.shape.len() >= walk.opts.shape_nodes {
                    walk.truncated = true;
                } else {
                    this = i64::try_from(walk.shape.len()).unwrap_or(i64::MAX);
                    walk.shape.push(ShapeNodeOut {
                        id: r.element_id(e).to_string(),
                        name: n.clone(),
                        qualified_name: q.clone(),
                        metaclass,
                        owner,
                    });
                }
            }
        }
        // The outline claims its slot before any member is visited.
        let in_outline = walk.outline_left > 0;
        walk.outline_left = walk.outline_left.saturating_sub(1);
        let members = r.owned_members(e);
        let mut children = Vec::new();
        if depth < walk.opts.shape_depth {
            for m in members {
                let child = self.outline_visit(walk, m, this, depth + 1)?;
                if let Some(child) = child.filter(|_| depth < walk.opts.outline_depth) {
                    children.push(child);
                }
            }
        } else if !members.is_empty() {
            walk.truncated = true;
        }
        Ok(in_outline.then_some(OutlineNodeOut {
            name,
            metaclass,
            qualified_name,
            children,
        }))
    }

    /// The JSON of a `{unit, start, end}` source extent.
    fn extent_json((unit, span): (usize, Span)) -> serde_json::Value {
        json!({"unit": unit, "start": span.start, "end": span.end})
    }

    /// Every element's documentation bodies as [`Self::docs`] answers
    /// them, by element: one pass over the model's annotations, where
    /// `docs` makes one per element.
    fn docs_by_target(&mut self) -> HashMap<ElementRef, Vec<String>> {
        let mut by_target: HashMap<ElementRef, Vec<String>> = HashMap::new();
        for (target, body) in self.inner.resolved().annotation_bodies() {
            let text = sysmlv2_model::json::doc_display_text(&body);
            if !text.is_empty() {
                by_target.entry(target).or_default().push(text);
            }
        }
        by_target
    }

    /// One [`Self::rows`] field of `e`, as the per-element read answers
    /// it; `docs` holds every element's documentation once a row asked.
    fn row_field(
        &mut self,
        e: &Element,
        field: &RowField,
        docs: &mut Option<HashMap<ElementRef, Vec<String>>>,
    ) -> Result<serde_json::Value, String> {
        Ok(match field {
            RowField::Name => json!(self.name(e)?),
            RowField::ShortName => json!(self.short_name(e)?),
            RowField::QualifiedName => json!(self.qualified_name(e)?),
            RowField::ReferenceSpelling => json!(self.reference_spelling(e)?),
            RowField::Metaclass => json!(self.metaclass(e)?),
            RowField::Owner => {
                let r = self.inner.resolved();
                json!(r.owner(e.e).map(|o| r.element_id(o).to_string()))
            }
            RowField::IsLibraryElement => json!(self.is_library_element(e)?),
            RowField::ValueSource => json!(self.value_source(e)?),
            RowField::ValueIsDefault => json!(self.value_is_default(e)?),
            RowField::Docs => {
                let by_target = docs.get_or_insert_with(|| self.docs_by_target());
                json!(by_target.get(&e.e).map_or(&[][..], Vec::as_slice))
            }
            RowField::DeclarationSite => self
                .declaration_site_of(e.e)
                .map_or(serde_json::Value::Null, Self::extent_json),
            RowField::MemberExtent => self
                .inner
                .resolved()
                .member_extent(e.e)
                .map_or(serde_json::Value::Null, Self::extent_json),
            RowField::Property(name) => self
                .inner
                .resolved()
                .property(e.e, name)
                .map_err(|e| e.to_string())?,
            RowField::Derived(name) => self.derived_json(e, name)?,
        })
    }

    /// Where `e` is declared: its name's site, else its member extent.
    fn declaration_site_of(&mut self, e: ElementRef) -> Option<(usize, Span)> {
        let r = self.inner.resolved();
        r.declaration_site(e).or_else(|| r.member_extent(e))
    }

    /// A quantity as `{value, unit}` in the evaluator's units.
    fn quantity_json(&mut self, v: &EvalValue) -> serde_json::Value {
        let EvalValue::Quantity(n, unit) = v else {
            return self.value_to_json(v);
        };
        json!({
            "value": self.value_to_json(n),
            "unit": unit.display(),
        })
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
            EvalValue::Element(e) | EvalValue::Unbound(e, _) | EvalValue::UnboundMember(e, _) => {
                json!({
                    "@element": self.inner.resolved().element_id(*e).to_string(),
                    "qualifiedName": self.inner.resolved().element_qualified_name(*e),
                })
            }
            // In the module's units (see `setValueUnits`).
            EvalValue::Quantity(..)
                if VALUE_UNITS.get() == sysmlv2_model::eval::UnitDisplay::AsWritten =>
            {
                match self.inner.resolved().value_as_written(v) {
                    Some(EvalValue::Quantity(n, unit)) => json!({
                        "value": self.value_to_json(&n),
                        "unit": unit.display(),
                    }),
                    _ => self.quantity_json(v),
                }
            }
            EvalValue::Quantity(..) => self.quantity_json(v),
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

/// Whether a snapshot decode keeps what hosts shipped in it — the language
/// server's library symbol table — for them to read: only when the caller
/// passes `keepHostParts: true`.
fn keeps_host_parts(keep_host_parts: Option<bool>) -> bool {
    keep_host_parts.unwrap_or(false)
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

    /// [`Self::new`] under a graph format: `"legacy"` (the default) or
    /// `"canonical"` (the opt-in contract of IDS.md, in which a conditional
    /// operand is a reference to an owned expression and a constructor's
    /// arguments belong to its result feature). A session opened on the
    /// handle takes the handle's format (`fromSourcesWithPreparedLibrary`);
    /// a snapshot recorded under another format is passed over and the
    /// library prepared from source.
    #[wasm_bindgen(js_name = withGraphFormat)]
    #[allow(clippy::needless_pass_by_value)]
    pub fn with_graph_format(
        sources_json: &str,
        snapshot: Option<Vec<u8>>,
        #[wasm_bindgen(js_name = graphFormat)] graph_format: Option<String>,
    ) -> Result<PreparedLibrary, String> {
        let format = parse_graph_format(graph_format.as_deref())?;
        Ok(Self {
            inner: Library::prepared_sources_with_format(
                parse_sources(sources_json)?,
                snapshot,
                format,
            )
            .map_err(|e| e.to_string())?,
        })
    }

    /// [`Self::from_snapshot`] under a graph format: `"legacy"` (the
    /// default, what `fromSnapshot` and `fromSnapshotStream` decode) or
    /// `"canonical"`. A snapshot prepared under the other format is refused
    /// with a message naming it (a canonical deployment ships a snapshot
    /// written under canonical; one written by `sysmlv2 prepare` is legacy).
    #[wasm_bindgen(js_name = fromSnapshotWithGraphFormat)]
    #[allow(clippy::needless_pass_by_value)]
    pub fn from_snapshot_with_graph_format(
        snapshot: Vec<u8>,
        sources_json: &str,
        recording: Option<Vec<u8>>,
        #[wasm_bindgen(js_name = graphFormat)] graph_format: Option<String>,
        #[wasm_bindgen(js_name = keepHostParts)] keep_host_parts: Option<bool>,
    ) -> Result<PreparedLibrary, String> {
        let format = parse_graph_format(graph_format.as_deref())?;
        Ok(Self {
            inner: Library::prepared_snapshot_in(
                parse_sources(sources_json)?,
                &snapshot,
                recording,
                format,
                keeps_host_parts(keep_host_parts),
            )
            .map_err(|e| e.to_string())?,
        })
    }

    /// The graph format this library was prepared under: `"legacy"` or
    /// `"canonical"`.
    #[wasm_bindgen(js_name = graphFormat)]
    pub fn graph_format(&self) -> String {
        graph_format_name(library_graph_format(&self.inner)).to_string()
    }

    /// [`Self::from_snapshot`] reading the snapshot where it lies: `view` stays
    /// in the host's memory and is copied into this module one window at a
    /// time, so the module's memory never holds the whole snapshot (which it
    /// would keep as its high-water mark). Same refusals as `fromSnapshot`.
    /// The snapshot also carries the language server's library symbol table:
    /// with `keepHostParts: true` the handle keeps it for a server on it
    /// (`LspServer.withPreparedLibrary`) to build its table from; by default
    /// it passes through, verified, and a module that hosts no language
    /// server holds none of it.
    #[cfg(target_arch = "wasm32")]
    #[wasm_bindgen(js_name = fromSnapshotStream)]
    #[allow(clippy::needless_pass_by_value)]
    pub fn from_snapshot_stream(
        view: js_sys::Uint8Array,
        sources_json: &str,
        recording: Option<Vec<u8>>,
        #[wasm_bindgen(js_name = keepHostParts)] keep_host_parts: Option<bool>,
    ) -> Result<PreparedLibrary, String> {
        let len = usize::try_from(view.length()).map_err(|e| e.to_string())?;
        let mut at: u32 = 0;
        let fill = |buf: &mut [u8]| {
            let n = u32::try_from(buf.len())
                .unwrap_or(u32::MAX)
                .min(view.length() - at);
            if n == 0 {
                return 0;
            }
            view.subarray(at, at + n).copy_to(&mut buf[..n as usize]);
            at += n;
            n as usize
        };
        Ok(Self {
            inner: Library::prepared_snapshot_chunks_with(
                parse_sources(sources_json)?,
                len,
                fill,
                recording,
                keeps_host_parts(keep_host_parts),
            )
            .map_err(|e| e.to_string())?,
        })
    }

    /// Decode a prepared snapshot (the package's `sysml-library.prepared.gz`,
    /// decompressed) of exactly `sources_json`, the bundle it was generated
    /// from: no resolve at boot, no syntax trees in memory. A snapshot made by
    /// another build or from other units is refused with an error, and the
    /// caller prepares from source with `new` instead. `recording` is the
    /// sealed resolution snapshot, kept encoded for the builds that must
    /// resolve the library together with user units. The snapshot also
    /// carries the language server's library symbol table: with
    /// `keepHostParts: true` the handle keeps it for a server on it
    /// (`LspServer.withPreparedLibrary`) to build its table from; by default
    /// it is verified and dropped, and a module that hosts no language
    /// server holds none of it.
    #[wasm_bindgen(js_name = fromSnapshot)]
    #[allow(clippy::needless_pass_by_value)]
    pub fn from_snapshot(
        snapshot: Vec<u8>,
        sources_json: &str,
        recording: Option<Vec<u8>>,
        #[wasm_bindgen(js_name = keepHostParts)] keep_host_parts: Option<bool>,
    ) -> Result<PreparedLibrary, String> {
        Ok(Self {
            inner: Library::prepared_snapshot_with(
                parse_sources(sources_json)?,
                &snapshot,
                recording,
                keeps_host_parts(keep_host_parts),
            )
            .map_err(|e| e.to_string())?,
        })
    }
}

/// The graph format a library was prepared under (`LegacyV2` for source
/// and directory libraries, which are prepared when a session takes them).
fn library_graph_format(library: &Library) -> GraphFormat {
    match library {
        Library::Prepared(prepared) => prepared.graph_format(),
        _ => GraphFormat::LegacyV2,
    }
}

#[wasm_bindgen]
impl Session {
    /// Open sources against a shared prepared library in one model build,
    /// under the library's graph format (a library prepared with
    /// `PreparedLibrary.withGraphFormat` opens canonical sessions).
    #[wasm_bindgen(js_name = fromSourcesWithPreparedLibrary)]
    pub fn from_sources_with_prepared_library(
        sources_json: &str,
        library: &PreparedLibrary,
    ) -> Result<Session, String> {
        let sources = parse_sources(sources_json)?;
        let inner = match library_graph_format(&library.inner) {
            GraphFormat::LegacyV2 => {
                TSession::from_sources_with_library(sources, Some(library.inner.clone()))
            }
            format => TSession::from_sources_with_graph_format(
                sources,
                Some(library.inner.clone()),
                format,
            ),
        }
        .map_err(|e| e.to_string())?;
        Ok(Session { inner, gen: 0 })
    }

    /// [`Self::from_sources_with_library`] under a graph format: `"legacy"`
    /// (the default) or `"canonical"` (see `PreparedLibrary.withGraphFormat`).
    /// The session lowers, emits and encodes under that format, keeps it
    /// through edits and library reloads, and refuses incoming snapshots
    /// and deltas of the other.
    #[allow(clippy::needless_pass_by_value)]
    #[wasm_bindgen(js_name = fromSourcesWithGraphFormat)]
    pub fn from_sources_with_graph_format(
        sources_json: &str,
        lib_sources_json: Option<String>,
        lib_snapshot: Option<Vec<u8>>,
        #[wasm_bindgen(js_name = graphFormat)] graph_format: Option<String>,
    ) -> Result<Session, String> {
        let format = parse_graph_format(graph_format.as_deref())?;
        let lib = lib_sources_json
            .as_deref()
            .map(|s| parse_library(s, lib_snapshot))
            .transpose()?;
        Ok(Session {
            inner: TSession::from_sources_with_graph_format(
                parse_sources(sources_json)?,
                lib,
                format,
            )
            .map_err(|e| e.to_string())?,
            gen: 0,
        })
    }

    /// The graph format this session was opened under: `"legacy"` or
    /// `"canonical"`.
    #[wasm_bindgen(js_name = graphFormat)]
    pub fn graph_format(&self) -> String {
        graph_format_name(self.inner.graph_format()).to_string()
    }

    /// Open interchange JSON against a shared prepared library; `flexo`
    /// as in [`Self::from_interchange_json`].
    #[allow(clippy::needless_pass_by_value)]
    #[wasm_bindgen(js_name = fromInterchangeJsonWithPreparedLibrary)]
    pub fn from_interchange_json_with_prepared_library(
        json: &str,
        library: &PreparedLibrary,
        indent: Option<String>,
        flexo: Option<bool>,
    ) -> Result<Session, String> {
        let value = interchange_value(json, flexo)?;
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
}

/// The outcomes a session's build settled on, held apart from the
/// session for the next build of mostly the same units to start from
/// (see [`Session::from_sources_settled`]). The handle keeps only the
/// outcomes — each reference's fingerprint and the identity of its
/// target — so the session that produced it may be freed before the
/// next build; free the handle once a build has taken it, or keep the
/// latest one across edits.
#[wasm_bindgen]
pub struct SettledOutcomes {
    inner: std::sync::Arc<sysmlv2_transform::SettledOutcomes>,
}

#[wasm_bindgen]
impl SettledOutcomes {
    /// How many units' outcomes the handle keeps.
    #[must_use]
    #[wasm_bindgen(js_name = unitCount)]
    pub fn unit_count(&self) -> usize {
        self.inner.unit_count()
    }
}

#[wasm_bindgen]
impl Session {
    /// The outcomes this session's build settled on, for a session over
    /// mostly the same units to start from ([`Self::from_sources_settled`]):
    /// `undefined` unless the session was built on a prepared library and
    /// its resolution ran more than one pass and settled — a build that
    /// resolved in one pass, one that resolved the library together with
    /// its units, or one that did not settle keeps none. A session rebuilt
    /// by an edit or a library load keeps the outcomes of its latest build.
    #[must_use]
    #[wasm_bindgen(js_name = settledOutcomes)]
    pub fn settled_outcomes(&self) -> Option<SettledOutcomes> {
        self.inner
            .settled_outcomes()
            .map(|inner| SettledOutcomes { inner })
    }

    /// [`Self::from_sources_with_prepared_library`] with resolution started
    /// from `settled`, the outcomes a previous session settled on
    /// ([`Self::settled_outcomes`]): a reference lowered where and as it
    /// was takes its outcome, so a unit that resolves as it did is
    /// confirmed in one pass, while an edited reference, and every
    /// reference after an inserted or removed element, starts unresolved
    /// and is carried through as many passes as it takes. What a host that
    /// rebuilds its session after every edit starts the next build from;
    /// the session answers as one built without.
    #[wasm_bindgen(js_name = fromSourcesSettled)]
    pub fn from_sources_settled(
        sources_json: &str,
        library: &PreparedLibrary,
        settled: &SettledOutcomes,
    ) -> Result<Session, String> {
        Ok(Session {
            inner: TSession::from_sources_settled(
                parse_sources(sources_json)?,
                Some(library.inner.clone()),
                Some(settled.inner.clone()),
            )
            .map_err(|e| e.to_string())?,
            gen: 0,
        })
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
    /// `flexo: true` reads the payload the way Flexo MMS returns it,
    /// deriving the `owningRelationship` and `owningRelatedElement` it
    /// omits from the owners' `ownedRelationship` and
    /// `ownedRelatedElement`; without it such a payload is refused.
    // The export boundary converts an optional string only when owned.
    #[allow(clippy::needless_pass_by_value)]
    #[wasm_bindgen(js_name = fromInterchangeJson)]
    pub fn from_interchange_json(
        json: &str,
        lib_sources_json: Option<String>,
        lib_snapshot: Option<Vec<u8>>,
        indent: Option<String>,
        flexo: Option<bool>,
    ) -> Result<Session, String> {
        let value = interchange_value(json, flexo)?;
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

    /// Describe a `view` usage for tabular consumers: the rendering it
    /// requests (`render …;` → the rendering usage's declared name; a
    /// view with no `render` member of its own reports the one it
    /// inherits from its definition or a view it specializes, the first
    /// in heritage order when there are several), the elements it
    /// exposes (its `expose` imports with the view's
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
            // A multiplicity member (a usage's default, SysML 7.6.3, or a
            // written range) is exposed with its owner's members and
            // renders through its owner, never as a row of its own.
            let exposed: Vec<ElementRef> = r.view_exposed_elements(view);
            let exposed: Vec<ElementRef> = exposed
                .into_iter()
                .filter(|&e| !matches!(r.element_type(e), "Multiplicity" | "MultiplicityRange"))
                .collect();
            let exposed: Vec<serde_json::Value> = exposed
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
        self.guard(e)?;
        self.derived_json(e, name).map(|json| json.to_string())
    }

    /// [`Self::derived`]'s answer as a JSON value, for the reads that
    /// embed it in a document of their own.
    fn derived_json(&mut self, e: &Element, name: &str) -> Result<serde_json::Value, String> {
        use sysmlv2_model::json::{DerivedValue, Reference, dangling_id};
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
            DerivedValue::Strings(ss) | DerivedValue::Literals(ss) => serde_json::json!(ss),
            DerivedValue::Literal(s) => serde_json::Value::String(s.clone()),
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
        Ok(json)
    }

    /// Checked owned/derived property by specification name, encoded as JSON.
    pub fn property(&mut self, e: &Element, name: &str) -> Result<String, String> {
        self.guard(e)?;
        self.inner
            .resolved()
            .property(e.e, name)
            .map(|v| v.to_string())
            .map_err(|e| e.to_string())
    }

    /// Strict full JSON; no recovery elements or unavailable-value placeholders.
    #[wasm_bindgen(js_name = toFullJsonStrict)]
    pub fn to_full_json_strict(&mut self) -> Result<String, String> {
        self.inner
            .to_full_json_strict()
            .map(|v| v.to_string())
            .map_err(|e| e.to_string())
    }

    /// `toFullJsonStrict` with the refusals beside the rows instead of in
    /// place of them, as one JSON document `{"elements": [...], "issues":
    /// [{"elementId", "property", "kind", "reason"}, ...]}`: every
    /// admitted element's row with the properties the checked reader
    /// answered, every refused property absent from its row and listed
    /// once. The rows are schema-invalid wherever a required property is
    /// missing: a report of what can be certified, not an interchange
    /// document (`toFullJson` is that). Throws only for what stops the
    /// export before the property reads.
    #[wasm_bindgen(js_name = toFullJsonChecked)]
    pub fn to_full_json_checked(&mut self) -> Result<String, String> {
        self.inner
            .to_full_json_checked()
            .map(|export| export.to_json().to_string())
            .map_err(|e| e.to_string())
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
        let policy = parse_closure_policy(policy)?;
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

    /// The links of the feature chain `e` redefines (`attribute :>>
    /// chassis.mass`), first to last, resolved: the first such
    /// redefinition's; empty when `e` redefines no chain.
    #[wasm_bindgen(js_name = redefinedChain)]
    pub fn redefined_chain(&mut self, e: &Element) -> Result<Vec<Element>, String> {
        self.guard(e)?;
        let gen = self.gen;
        Ok(self
            .inner
            .resolved()
            .redefined_chains(e.e)
            .into_iter()
            .next()
            .unwrap_or_default()
            .into_iter()
            .map(|e| Element { e, gen })
            .collect())
    }

    /// Whether `e`'s own value is a default (`default v`) rather than a
    /// binding (`= v`); undefined when `e` declares no value.
    #[wasm_bindgen(js_name = valueIsDefault)]
    pub fn value_is_default(&mut self, e: &Element) -> Result<Option<bool>, String> {
        self.guard(e)?;
        Ok(self.inner.resolved().value_is_default(e.e))
    }

    /// The feature `e` stands for through its redefinitions by name —
    /// the end of `e` → its first redefinition target → … — or `e`
    /// itself. Features that redefine one feature, however many steps
    /// apart, share a root.
    #[wasm_bindgen(js_name = redefinitionRoot)]
    pub fn redefinition_root(&mut self, e: &Element) -> Result<Element, String> {
        self.guard(e)?;
        let gen = self.gen;
        let root = self.inner.resolved().redefinition_root(e.e);
        Ok(Element { e: root, gen })
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

    /// Reachability including supported implied library and variation bases.
    /// A negative result does not establish complete non-conformance.
    #[wasm_bindgen(js_name = conformsWithImplied)]
    pub fn conforms_with_implied(
        &mut self,
        e: &Element,
        ancestor: &Element,
    ) -> Result<bool, String> {
        self.guard(e)?;
        self.guard(ancestor)?;
        Ok(self.inner.resolved().conforms_with_implied(e.e, ancestor.e))
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

    /// Respell every reference with the shortest spelling that still
    /// resolves to the same element: plain sites, feature chains (as one
    /// unit: the shortest head, then the written member names) and
    /// import targets (a member import keeps its written last segment
    /// and at least two segments, or one when only one is written).
    /// Reparse-verified; ids are untouched by construction. Returns
    /// `{respelled, reverted}`, `reverted` counting the respells the
    /// reparse dropped (their sites keep the original spelling).
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
        self.root_refs()
            .into_iter()
            .map(|e| Element { e, gen })
            .collect()
    }

    /// The model's outline tree and its named-element shape from one
    /// walk, as JSON: what reading every element through `roots`,
    /// `members`, `derived(e, "name")`, `name`, `qualifiedName`,
    /// `metaclass` and `elementId` assembles, in one call and without a
    /// handle per element.
    ///
    /// Options JSON (absent or empty = every default): `{outlineNodes?:
    /// 4000, outlineDepth?: 24, shapeNodes?: 20000, shapeDepth?: 64}`.
    ///
    /// The walk visits `roots()` in order, each depth-first through its
    /// `members` in declaration order. A root is at depth 0, and the walk
    /// goes below an element at depth `d` only while `d < shapeDepth`.
    /// Each visited element is named as `derived(e, "name")` names it
    /// when that is a string, else by its declared name, else `null`.
    ///
    /// - **Outline.** Every visited element claims one of `outlineNodes`
    ///   slots in visiting order (before its members); one visited after
    ///   they are spent has no outline node. A node is `{name, metaclass,
    ///   qualifiedName, children}` (`qualifiedName` `null` for an
    ///   anonymous element), and a node at depth `d` keeps its members'
    ///   nodes as `children` only while `d < outlineDepth`.
    /// - **Shape.** An element whose name and qualified name are both
    ///   non-empty is recorded as `{id, name, qualifiedName, metaclass,
    ///   owner}`, in visiting order; `owner` indexes the nearest such
    ///   ancestor in the list, `-1` for none (an anonymous element's
    ///   members re-parent onto its nearest named ancestor). Once
    ///   `shapeNodes` are recorded, every further named element is left
    ///   out and sets `truncated`; so does an element at `shapeDepth`
    ///   that has members.
    ///
    /// Reply: `{outline: [node…], shape: {nodes: [node…], truncated}}`.
    /// Errors as `derived` does, or on malformed options.
    // The export boundary converts an optional string only when owned.
    #[allow(clippy::needless_pass_by_value)]
    pub fn outline(&mut self, opts_json: Option<String>) -> Result<String, String> {
        let opts: OutlineIn = serde_json::from_str(
            opts_json
                .as_deref()
                .filter(|s| !s.is_empty())
                .unwrap_or("{}"),
        )
        .map_err(|e| format!("bad options: {e}"))?;
        let mut walk = OutlineWalk {
            outline_left: opts.outline_nodes,
            opts,
            shape: Vec::new(),
            truncated: false,
        };
        let mut outline = Vec::new();
        for e in self.root_refs() {
            if let Some(node) = self.outline_visit(&mut walk, e, -1, 0)? {
                outline.push(node);
            }
        }
        #[derive(Serialize)]
        struct Shape {
            nodes: Vec<ShapeNodeOut>,
            truncated: bool,
        }
        #[derive(Serialize)]
        struct Reply {
            outline: Vec<OutlineNodeOut>,
            shape: Shape,
        }
        serde_json::to_string(&Reply {
            outline,
            shape: Shape {
                nodes: walk.shape,
                truncated: walk.truncated,
            },
        })
        .map_err(|e| e.to_string())
    }

    /// The ownership tree under `root` as JSON — the document `sysmlv2
    /// tree --format json` writes: an array of nodes `{metaclass, name?,
    /// qualifiedName?, id?, library?, site?, references?, relationships:
    /// [{metaclass, id?, implied?, references?, children}], truncated?}`.
    /// Ownership makes the hierarchy — an element lists the
    /// relationships it owns, a relationship the elements it owns in
    /// turn — and every other end of a relationship (a typing's `type`,
    /// a subclassification's `superclassifier`, an import's namespace, an alias's
    /// `memberElement`) is a reference `{property, target: {metaclass,
    /// name?, qualifiedName?, library?, outside?, id?, spelling?}}`,
    /// never expanded, so a library is entered only through a chosen
    /// root.
    ///
    /// Options JSON (absent or empty = every default): `{root?, depth?:
    /// number, references?: true, implied?: false, ids?: false}` —
    /// `root` is a `::`-qualified name or `{elementId}` for an element
    /// without one (absent, the tree starts at every top-level element,
    /// the `roots()`); `depth` bounds the ownership levels (a node past
    /// it is `truncated`); `references: false` keeps the ownership
    /// alone; `implied` adds the implied relationships (the library
    /// specializations of each kind, the positional redefinitions) and
    /// the elements they generate; `ids` carries the interchange ids.
    /// Errors on a root that does not resolve or malformed options.
    // The export boundary converts an optional string only when owned.
    #[allow(clippy::needless_pass_by_value)]
    pub fn tree(&mut self, opts_json: Option<String>) -> Result<String, String> {
        let nodes = self.tree_nodes(opts_json.as_deref())?;
        serde_json::to_string(&nodes).map_err(|e| e.to_string())
    }

    /// [`Self::tree`] as the box-drawing text `sysmlv2 tree` prints: the
    /// root by its qualified name, each owned element by its name,
    /// `property → qualified name [Metaclass] [library]` per reference,
    /// `(unresolved)` on a spelling that did not resolve, `(implied)` on
    /// an implied relationship and `…` where `depth` cut the walk. The
    /// options are `tree`'s.
    #[wasm_bindgen(js_name = treeText)]
    #[allow(clippy::needless_pass_by_value)]
    pub fn tree_text(&mut self, opts_json: Option<String>) -> Result<String, String> {
        let nodes = self.tree_nodes(opts_json.as_deref())?;
        Ok(sysmlv2_model::inspect::render(&nodes))
    }

    /// Per-element reads for many elements in one call, as JSON.
    ///
    /// `ids_json` is an array of interchange ids and `fields_json` an
    /// array of field names. The reply is an array in the order of the
    /// ids: `null` where `elementById` finds no element, else an object
    /// holding each field under its name, valued as the same-named
    /// per-element read answers it — `undefined` as `null`, a JSON
    /// answer decoded:
    ///
    /// - `name`, `shortName`, `qualifiedName`, `referenceSpelling`,
    ///   `metaclass`, `isLibraryElement`, `valueSource`,
    ///   `valueIsDefault`, `docs`, `declarationSite`, `memberExtent`;
    /// - `owner`: the owner's id, or `null` for a document root;
    /// - `property:<name>`: `property(e, name)`;
    /// - `derived:<name>`: `derived(e, name)`.
    ///
    /// A read that errors leaves its field out and puts its message
    /// under `errors: {field: message}` instead. Errors when either
    /// array is malformed or names a field outside this list.
    pub fn rows(&mut self, ids_json: &str, fields_json: &str) -> Result<String, String> {
        let ids: Vec<String> =
            serde_json::from_str(ids_json).map_err(|e| format!("bad ids: {e}"))?;
        let names: Vec<String> =
            serde_json::from_str(fields_json).map_err(|e| format!("bad fields: {e}"))?;
        let fields = names
            .iter()
            .map(|name| RowField::parse(name))
            .collect::<Result<Vec<_>, _>>()?;
        let mut docs = None;
        let mut out = Vec::with_capacity(ids.len());
        for id in &ids {
            let Some(e) = self.element_by_id(id) else {
                out.push(serde_json::Value::Null);
                continue;
            };
            let mut row = serde_json::Map::new();
            let mut errors = serde_json::Map::new();
            for (name, field) in names.iter().zip(&fields) {
                match self.row_field(&e, field, &mut docs) {
                    Ok(value) => row.insert(name.clone(), value),
                    Err(message) => errors.insert(name.clone(), message.into()),
                };
            }
            if !errors.is_empty() {
                row.insert("errors".to_string(), errors.into());
            }
            out.push(row.into());
        }
        Ok(serde_json::Value::Array(out).to_string())
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
        self.inner.to_compact_json_string()
    }

    /// Compact-form CBOR for the session's model (a `Uint8Array`) — the
    /// deterministic binary re-encoding of [`Self::to_compact_json`],
    /// several times smaller on the wire and decodable back to the
    /// identical element array.
    #[wasm_bindgen(js_name = toCompactCbor)]
    pub fn to_compact_cbor(&self) -> Vec<u8> {
        self.inner.to_compact_cbor()
    }

    /// The unit structure [`Self::to_compact_cbor`] carries, as JSON
    /// `[[index, path], …]`: for each user unit, the compact element-array
    /// index of its root namespace and the unit's source path — the
    /// `units` that [`describe_cbor`] reports for that payload, read
    /// without encoding it.
    #[wasm_bindgen(js_name = unitTable)]
    pub fn unit_table(&self) -> String {
        json!(self.inner.unit_structure()).to_string()
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
    /// `closures` selects the values of the inheritance-aware properties:
    /// `"passthrough"` (the default, and `undefined`) writes the owned side
    /// and `[]` for the four closure names whatever `isImpliedIncluded`
    /// says; `"closure"` writes the specification's values over the
    /// written heritage, `"closure-implied"` with the implied library
    /// heritage too (the session's own `closurePolicy` is the reads' and
    /// does not select the export's). The closure levels throw for an
    /// element whose inheritance walk exceeds the resolver's depth budget.
    // The export boundary converts an optional string only when owned.
    #[allow(clippy::needless_pass_by_value)]
    #[wasm_bindgen(js_name = toFullJson)]
    pub fn to_full_json(
        &self,
        recover_refs: bool,
        closures: Option<String>,
    ) -> Result<String, String> {
        use sysmlv2_model::full::{EmissionPolicy, UnresolvedReferencePolicy};
        let closures = match closures.as_deref() {
            None => Default::default(),
            Some(name) => parse_closure_policy(name)?,
        };
        let unresolved = if recover_refs {
            UnresolvedReferencePolicy::Preserve
        } else {
            UnresolvedReferencePolicy::LegacyDanglingId
        };
        self.inner
            .to_full_json_with_policy(EmissionPolicy {
                unresolved,
                closures,
            })
            .map(|v| v.to_string())
            .map_err(|e| e.to_string())
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
    ///
    /// With `summary` (tree view only) the reply is the summary picture
    /// and carries `summary: {resolved, unresolved}` — the open selectors
    /// it resolved, as `{id, qualifiedName}`, and those it did not. With
    /// `summary.fullWithin: n` as well, a scope whose summary would draw
    /// at most `n` cards in full (its nodes plus every node's
    /// `summary.hidden`) comes back as the full graph instead: the
    /// request without `summary` would emit the same document, here with
    /// `full: true` added and no `summary` field. One call then answers
    /// what a summary request followed by a full request would.
    /// `fullWithin` must be a finite number: `JSON.stringify` spells
    /// `Infinity` and `NaN` as `null`, which reads as no `fullWithin`. A
    /// host that wants the full graph whatever its size sends a large
    /// finite number, or leaves `summary` out.
    // The export boundary converts an optional string only when owned.
    #[allow(clippy::needless_pass_by_value)]
    #[wasm_bindgen(js_name = toGraph)]
    pub fn to_graph(&mut self, opts_json: Option<String>) -> Result<String, String> {
        let (mut viz, mut root, summary_opts) = self.diagram_request(opts_json.as_deref())?;
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
        let full_within = summary_opts.as_ref().and_then(|sm| sm.full_within);
        if viz.roots.as_ref().is_some_and(|r| r.is_empty()) {
            let mut g = json!({ "view": view, "nodes": [], "edges": [] });
            if full_within.is_some_and(|n| 0.0 <= n) {
                // nothing to draw is within any budget
                g["full"] = json!(true);
            } else if summary_opts.is_some() {
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
        // The summary's total is counted without emitting it, so a scope
        // that fits emits only its full graph. The total is a whole
        // number: a budget fits what its whole part does, and a negative
        // one fits nothing. The count stops once past the budget.
        let limit = full_within.filter(|n| 0.0 <= *n).map(|n| n as usize);
        let counted_fit = match limit {
            Some(limit) => {
                // The count and the emission after it start from the same
                // elements: look them up once.
                let tops = sysmlv2_viz::scope_roots(self.inner.resolved(), root, &viz);
                viz.roots = Some(tops);
                root = None;
                sysmlv2_viz::summary_would_draw_within(self.inner.resolved(), root, &viz, limit)
                    .map_err(|e| e.to_string())?
                    .is_some()
            }
            None => false,
        };
        if !counted_fit {
            let mut g =
                sysmlv2_viz::graph(self.inner.resolved(), root, &viz).map_err(|e| e.to_string())?;
            // The summary's own total decides where a count that stopped
            // early could not: one that counted elements sharing an id.
            if !full_within.is_some_and(|n| sysmlv2_viz::summary_would_draw(&g) as f64 <= n) {
                if summary_opts.is_some() {
                    g["summary"] =
                        json!({ "resolved": resolved_open, "unresolved": unresolved_open });
                }
                return Ok(g.to_string());
            }
        }
        // The whole scope fits: emit it as the request without a summary
        // does — the options are that request's once the summary is gone.
        viz.summary = None;
        let mut full =
            sysmlv2_viz::graph(self.inner.resolved(), root, &viz).map_err(|e| e.to_string())?;
        full["full"] = json!(true);
        Ok(full.to_string())
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
                EditOpIn::SetRedefinedFeature { target, feature } => {
                    ResolvedOp::SetRedefinedFeature(resolve(&mut self.inner, &target)?, feature)
                }
                EditOpIn::RemoveFeatureValue { target } => {
                    ResolvedOp::RemoveFeatureValue(resolve(&mut self.inner, &target)?)
                }
                EditOpIn::SetCommentBody { target, body } => {
                    ResolvedOp::SetCommentBody(resolve(&mut self.inner, &target)?, body)
                }
                EditOpIn::InsertMember { owner, text, index } => ResolvedOp::InsertMember(
                    resolve(&mut self.inner, &owner)?,
                    text,
                    index.map(|i| i as usize),
                ),
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
                ResolvedOp::SetRedefinedFeature(e, t) => batch.set_redefined_feature(*e, t),
                ResolvedOp::RemoveFeatureValue(e) => batch.remove_feature_value(*e),
                ResolvedOp::SetCommentBody(e, body) => batch.set_comment_body(*e, body),
                ResolvedOp::InsertMember(e, text, index) => {
                    batch.insert_member_at(*e, text, *index)
                }
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
            .map(|site| Self::extent_json(site).to_string()))
    }

    #[wasm_bindgen(js_name = declarationSite)]
    pub fn declaration_site(&mut self, e: &Element) -> Result<Option<String>, String> {
        self.guard(e)?;
        Ok(self
            .declaration_site_of(e.e)
            .map(|site| Self::extent_json(site).to_string()))
    }

    /// Find usages: every reference that resolves to the element, with
    /// the element's declaration — the language server's references
    /// answer with the declaration included, positioned the same way.
    /// The selector is a qualified name or `{elementId}`, as `revealPath`
    /// takes it.
    ///
    /// JSON `{declaration: {unit, line, col, endLine, endCol, site} |
    /// null, references: [{unit, line, col, endLine, endCol, kind,
    /// owner}]}`. `unit` is the unit's name, as `check` findings carry
    /// it; a library unit is `sysmlv2-lib:/` and its name percent-encoded
    /// as a uri path, the uri the server gives it and a host serves the
    /// library's text under — or, where the host set a library directory
    /// ([`setLibraryRoot`](set_library_root)), the unit's file under it.
    /// Lines and columns are 1-based, columns counted in UTF-16 code
    /// units as an editor counts them, the end exclusive.
    ///
    /// The declaration's `site` is `name` when its range is the declared
    /// name, or `extent` when the element declares no name and the range
    /// is its whole member declaration instead (a nameless redefinition,
    /// `part :>> chassis { … }`, reached through a chain): somewhere to
    /// open, not a range to rename at, and the server includes no
    /// declaration then. The declaration is `null` for an element with
    /// no recorded source.
    ///
    /// A reference's range covers the segment that names the element
    /// (`Wheel` in `Defs::Wheel`). `kind` is the serialized property it
    /// feeds (`type`, `superclassifier`, `importedMembership`, …).
    /// `owner` is `{id, qualifiedName}` of the nearest enclosing element
    /// that has a qualified name — `w` for `part w : Wheel;`, the package
    /// an import sits in, the feature whose value names it, the first
    /// named element around a reference written on something nameless —
    /// or `null` when nothing around it has one, as at the top level of
    /// a unit or inside a nameless element there. The sites come in unit
    /// and position order. A library's own references are not recorded,
    /// so a library element's sites are the model's references to it.
    ///
    /// Errors when the selector does not resolve. Reads only: nothing is
    /// written into the model, and handles stay valid.
    pub fn references(&mut self, selector_json: &str) -> Result<String, String> {
        // A bare name is as good as its JSON string form.
        let sel: Selector = serde_json::from_str(selector_json)
            .unwrap_or_else(|_| Selector::Name(selector_json.to_string()));
        let e = resolve_selector(self.inner.resolved(), &sel)
            .ok_or_else(|| format!("element not found: {selector_json}"))?;
        let resolved = self.inner.resolved_ref();
        let declaration = resolved
            .declaration_site(e)
            .map(|site| (site, "name"))
            .or_else(|| resolved.member_extent(e).map(|site| (site, "extent")));
        let sites = resolved.references_to(e);
        // Each site is written on a relationship or an expression, which
        // has no name of its own; the element named for it is the first
        // one above that has a qualified name. A unit's root namespace
        // has none and owns nothing above, so a site with nothing named
        // around it (at the top level of a unit, or inside a nameless
        // element there) has no owner.
        let owners: Vec<serde_json::Value> = sites
            .iter()
            .map(|site| {
                let r = self.inner.resolved();
                let mut cur = Some(site.owner);
                while let Some(o) = cur {
                    if let Some(qualified_name) = r.element_qualified_name(o) {
                        return json!({
                            "id": r.element_id(o).to_string(),
                            "qualifiedName": qualified_name,
                        });
                    }
                    cur = r.owner(o);
                }
                serde_json::Value::Null
            })
            .collect();
        let mut mappers = HashMap::new();
        let declaration = declaration.and_then(|((unit, span), site)| {
            let mut location = unit_location(&self.inner, &mut mappers, unit, span)?;
            location["site"] = json!(site);
            Some(location)
        });
        let references: Vec<serde_json::Value> = sites
            .iter()
            .zip(owners)
            .filter_map(|(site, owner)| {
                let mut location =
                    unit_location(&self.inner, &mut mappers, site.unit, site.name_span)?;
                location["kind"] = json!(site.kind);
                location["owner"] = owner;
                Some(location)
            })
            .collect();
        Ok(json!({ "declaration": declaration, "references": references }).to_string())
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
    /// external solver. Options JSON: `{maxIters?, numberFormat?,
    /// valueUnits?}` (fixpoint pass cap per unit, default 100; the
    /// [`setNumberFormat`](LspServer::set_number_format) spec `rangeApprox`
    /// writes non-terminating endpoints in, default `"exact"`; `"si"` or
    /// `"asWritten"`, by default the module's
    /// [`setValueUnits`](set_value_units) choice: `"asWritten"` gives each
    /// range in the units its bounds were written in where those differ
    /// from the evaluator's — `unit`, `range` and `rangeApprox` then read
    /// `in**2`, `[1, 6]` for bounds folded to `m**2` — and each binding's
    /// `value`, in `bindings` and in a `detail`'s `(with …)`, in the units
    /// it was written in). Returns a JSON report: `{constraints:
    /// [{unit, unitName, name, elementType, asserted, line, col,
    /// endLine, endCol, status, method, detail, bindings, features}]
    /// (`method` = which stage decided: evaluation|propagation, null
    /// while undecided), ranges:
    /// [{feature, unit, range, rangeApprox, narrowed}], summary: {satisfied,
    /// violated, undecided}}` — positions 1-based over the result
    /// expression; `status` folds definitive propagation conclusions
    /// into satisfied|violated|undecided; `detail` is the human
    /// verdict line, worded exactly like the CLI's (incl. the `(with
    /// reserveKg = 0.10)` suffix on violated verdicts). `bindings` =
    /// the result expression's feature references with their own
    /// evaluations and declaration positions (`{feature, value?,
    /// unitName?, line?, col?}`, empty for satisfied constraints);
    /// `features` = the free features the propagation term references
    /// (the keys into `ranges`). `satisfactions` holds one verdict per
    /// `satisfy R by x;` claim, decided at the evaluation tier with R's
    /// subjects bound to `x`: `{unit, unitName, requirement, by, negated,
    /// line, col, endLine, endCol, status, vacuous, detail, constraints}`,
    /// positioned over the whole `satisfy` statement; `vacuous` = satisfied
    /// only because an assumption does not hold; `constraints` = the
    /// verdicts it combines, `{unit, unitName, name, elementType, assumed,
    /// line, col, endLine, endCol, status, detail, bindings}` (bindings
    /// evaluated under the subject binding, chains like `x.mass` whole).
    /// The summary counts claims alongside constraints.
    // The export boundary converts an optional string only when owned.
    #[allow(clippy::needless_pass_by_value)]
    pub fn verify(&mut self, opts_json: Option<String>) -> Result<String, String> {
        #[derive(Deserialize)]
        #[serde(rename_all = "camelCase", deny_unknown_fields)]
        struct VerifyOpts {
            max_iters: Option<usize>,
            number_format: Option<String>,
            value_units: Option<String>,
        }
        let opts: VerifyOpts = serde_json::from_str(opts_json.as_deref().unwrap_or("{}"))
            .map_err(|e| format!("bad verify options: {e}"))?;
        let value_units = parse_value_units(opts.value_units.as_deref())
            .map_err(|e| format!("bad verify options: valueUnits: {e}"))?;
        let number_format = match opts.number_format.as_deref() {
            Some(spec) => sysmlv2_model::numfmt::NumberFormat::parse(spec)
                .map_err(|e| format!("bad verify options: numberFormat: {e}"))?,
            None => PropagateConfig::default().number_format,
        };
        let mut cfg = PropagateConfig::default().with_number_format(number_format);
        if let Some(max_iters) = opts.max_iters {
            cfg = cfg.with_max_iters(max_iters);
        }
        // `None` solver = the solverless pipeline; it cannot fail. It runs on
        // the session's own resolved graph, reusing what earlier queries
        // derived instead of resolving the model again.
        let (resolved, model) = self.inner.resolved_with_model();
        let report = sysmlv2_solve::verify_constraints_with(resolved, model, None, &cfg)
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
                    detail = with_values(detail, &c.bindings, value_units);
                }
                let bindings = bindings_json(&c.bindings, value_units, inner, &names, &mut indexes);
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
            .map(|r| match (value_units, &r.as_written) {
                (sysmlv2_model::eval::UnitDisplay::AsWritten, Some(w)) => json!({
                    "feature": r.feature,
                    "unit": w.unit,
                    "range": w.range,
                    "rangeApprox": w.range_approx,
                    "narrowed": r.narrowed,
                }),
                _ => json!({
                    "feature": r.feature,
                    "unit": r.unit,
                    "range": r.range,
                    "rangeApprox": r.range_approx,
                    "narrowed": r.narrowed,
                }),
            })
            .collect();
        let mut satisfactions: Vec<serde_json::Value> = Vec::new();
        for claim in &report.satisfactions {
            let (status, detail) = match &claim.verdict {
                ConstraintVerdict::Satisfied if claim.vacuous => (
                    "satisfied",
                    "satisfied (an assumption does not hold)".to_string(),
                ),
                verdict => verify_status(verdict, None),
            };
            match status {
                "satisfied" => sat += 1,
                "violated" => vio += 1,
                _ => und += 1,
            }
            let mut constraints: Vec<serde_json::Value> = Vec::new();
            for c in &claim.constraints {
                let (status, mut detail) = verify_status(&c.check.verdict, None);
                if status == "violated" {
                    detail = with_values(detail, &c.check.bindings, value_units);
                }
                let li = unit_line_index(&mut indexes, inner, c.check.unit);
                let (start, end) = (
                    li.line_col(c.check.span.start),
                    li.line_col(c.check.span.end),
                );
                constraints.push(json!({
                    "unit": c.check.unit,
                    "unitName": names.get(&c.check.unit),
                    "name": c.check.name,
                    "elementType": c.check.element_type,
                    "assumed": c.assumed,
                    "line": start.line,
                    "col": start.col,
                    "endLine": end.line,
                    "endCol": end.col,
                    "status": status,
                    "detail": detail,
                    "bindings": bindings_json(&c.check.bindings, value_units, inner, &names, &mut indexes),
                }));
            }
            let li = unit_line_index(&mut indexes, inner, claim.unit);
            let (start, end) = (li.line_col(claim.span.start), li.line_col(claim.span.end));
            satisfactions.push(json!({
                "unit": claim.unit,
                "unitName": names.get(&claim.unit),
                "requirement": claim.requirement,
                "by": claim.by,
                "negated": claim.negated,
                "line": start.line,
                "col": start.col,
                "endLine": end.line,
                "endCol": end.col,
                "status": status,
                "vacuous": claim.vacuous,
                "detail": detail,
                "constraints": constraints,
            }));
        }
        Ok(json!({
            "constraints": constraints,
            "ranges": ranges,
            "satisfactions": satisfactions,
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
        let outcome = sysmlv2_lint::lint_outcome(self.inner.resolved(), &cfg, &units);
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
        for f in &outcome.findings {
            report.push_finding(f, &table);
        }
        report.set_suppressed(outcome.suppressed.len());
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
/// `[{severity, stage, message, unit, line, col, endLine, endCol, rule?}]`
/// (1-based positions; the end pair spans the full diagnostic, so
/// markers cover the whole offending construct rather than just its
/// start). `stage` is `parse`, `context`, `referential` or `semantic`;
/// only `parse` findings keep a unit out of a session. `rule` names the
/// normative rule a semantic finding reports
/// (`validateSatisfyRequirementUsageReference`) and is absent when the
/// finding names none. A broken parse is a finding, not an error.
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
            if let Some(rule) = f.code {
                obj["rule"] = json!(rule);
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

/// Choose the units evaluated quantities show in across this module.
/// `"si"`, the default, keeps the evaluator's units: a bracket's unit,
/// kept through sums and scaling, and SI units for a product, quotient
/// or power (`10 ['in'] / (2 [s])` is `0.127 [m/s]`). `"asWritten"`
/// shows each quantity in the units it was written in, where those
/// cover its dimensions (`5 [in/s]`), by the rules
/// [`LspServer.setValueHintUnits`](LspServer::set_value_hint_units)
/// uses. It applies to the values [`Session::query`],
/// [`Session::evaluate`] and [`Session::view_info`] return, and it is
/// the default of the `valueUnits` option of [`Session::to_graph`],
/// [`Session::to_plantuml`] and [`Session::verify`]. Evaluation is
/// unchanged; only the unit a quantity is written in, and its number,
/// differ. Module-wide, so hosts set it once at startup or on a settings
/// change; a language server keeps its own setting. Throws on any other
/// mode.
#[wasm_bindgen(js_name = setValueUnits)]
pub fn set_value_units(mode: &str) -> Result<(), String> {
    VALUE_UNITS.set(sysmlv2_model::eval::UnitDisplay::parse(mode)?);
    Ok(())
}

/// The module's [`setValueUnits`](set_value_units) choice: `"si"` or
/// `"asWritten"`.
#[must_use]
#[wasm_bindgen(js_name = valueUnits)]
pub fn value_units() -> String {
    VALUE_UNITS.get().as_str().to_string()
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
/// derivation from the forward ownership lists, each literal's number
/// spelled as its value type spells it (a `LiteralRational`'s `150` as
/// `150.0`, a `LiteralInteger`'s `150.0` as `150`), elements sorted by
/// `@id`. `stateDigestOf(graphNormalizeCompact(doc))` is the digest
/// such a store reconstructs after ingesting `doc`, so snapshots (and
/// strict deltas whose base digests live in the same domain) encoded
/// from this spelling pass the store's end-to-end digest
/// verification; a document printed through `JSON.parse` and
/// `JSON.stringify`, which drop a whole float's fraction, digests as
/// the kernel's own spelling of it does. Idempotent; strict on unknown
/// `@type`s, missing `@id`s, and keys outside the full schema.
/// Optional `as_spelled`: keep each literal's number as the document
/// spells it, as this normalization did before every spelling of a
/// value was one — a digest recorded then is checked against it.
#[wasm_bindgen(js_name = graphNormalizeCompact)]
pub fn graph_normalize_compact(json: &str, as_spelled: Option<bool>) -> Result<String, String> {
    if as_spelled.unwrap_or(false) {
        sysmlv2_cbor::graph_normalize_compact_as_spelled(json)
    } else {
        sysmlv2_cbor::graph_normalize_compact(json)
    }
    .map_err(|e| e.to_string())
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

    /// A server whose navigation and completions see a prepared library.
    /// The library was resolved when it was prepared, so a session resolves
    /// the workspace's units against it rather than the library's sources;
    /// a workspace that may change what the library's own names resolve to
    /// (for example a root name the library looked up and missed, or a root
    /// declaration named like one of the library's) has the library resolved
    /// again with it. The server keeps its own reference; the handle may be
    /// freed afterwards. A handle decoded with `keepHostParts: true`
    /// (`PreparedLibrary.fromSnapshot`, `fromSnapshotStream`) gives the
    /// server the library symbol table its snapshot carries, which it builds
    /// its table from on its first completion or import fix instead of
    /// parsing every library unit; on any other handle it parses them, as
    /// before, and answers the same.
    #[must_use]
    #[wasm_bindgen(js_name = withPreparedLibrary)]
    pub fn with_prepared_library(library: &PreparedLibrary) -> LspServer {
        LspServer {
            inner: sysmlv2_lsp::PushServer::with_library(library.inner.clone()),
        }
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
    /// session gave. Relay them exactly like [`Self::handle`] output. Only
    /// a re-seed of the same units with the same texts, with no document
    /// opened, changed or closed since refresh requests last went out,
    /// returns none. A re-seed that changes only the texts of units open as
    /// documents, whose open texts overlay them, keeps the server's
    /// sessions, and the re-pull answers from them.
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

    /// Set how evaluated-value inlay hints, hover values and range hints
    /// write a rational without a terminating decimal expansion. `spec`
    /// is a style — `exact` (`1/15`, the default), `approx`
    /// (`≈0.06666666666666667`), `overline` (`0.06̅`), `parens` (`0.0(6)`) or
    /// `unicode` (`¹/₁₅`) — then optional comma-separated settings:
    /// `digits=N` (significant digits of an approximate decimal, every
    /// style's fallback; 0 = shortest), `period=N` (`overline`,
    /// `parens`: longest period written out, default 6), `mixed=bool`
    /// (`exact`, `unicode`: `2 1/3`, `2¹/₃`), `slash=solidus|fraction|division`
    /// and `glyphs=bool` (`unicode`), `fraction-digits=N` (`exact`,
    /// `unicode`: most digits per numerator or denominator, 0 = no
    /// limit). Throws on a spec it cannot read, naming the problem.
    /// Returns the refresh requests to relay, like `setWorkspace`.
    #[wasm_bindgen(js_name = setNumberFormat)]
    pub fn set_number_format(&mut self, spec: &str) -> Result<Vec<String>, String> {
        let format = sysmlv2_model::numfmt::NumberFormat::parse(spec)?;
        self.inner.set_number_format(format);
        self.inner.take_outbound().map_err(|e| e.to_string())
    }

    /// Set which units evaluated-value inlay hints and hover values show
    /// quantities in: `si` (the evaluator's own — a bracket's unit, kept
    /// through additive and scalar operations, and SI for products,
    /// quotients and powers; the default) or `asWritten` (each value
    /// re-expressed in the units it was written in where they reach its
    /// dimensions: `10 ['in'] / (2 [s])` shows `5 [in/s]`, not
    /// `0.127 [m/s]`). Hover shows the other reading alongside when it
    /// differs. Throws on any other mode. Returns the refresh requests to
    /// relay, like `setWorkspace`.
    #[wasm_bindgen(js_name = setValueHintUnits)]
    pub fn set_value_hint_units(&mut self, mode: &str) -> Result<Vec<String>, String> {
        let units = sysmlv2_model::eval::UnitDisplay::parse(mode)?;
        self.inner.set_value_hint_units(units);
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

#[cfg(test)]
mod host_part_tests {
    use super::{PreparedLibrary, keeps_host_parts};
    use sysmlv2_transform::Library;

    /// A snapshot decoded without `keepHostParts`, or with `false`, holds
    /// none of what hosts shipped in it; with `true` it keeps it for them to
    /// read. The streamed decode takes its default from the same place.
    #[test]
    fn a_snapshot_keeps_its_hosts_parts_only_when_asked() {
        assert!(!keeps_host_parts(None), "dropped by default");
        assert!(!keeps_host_parts(Some(false)));
        assert!(keeps_host_parts(Some(true)));
        let units = vec![(
            "lib.sysml".to_owned(),
            "package L { part def A; }".to_owned(),
        )];
        let Library::Prepared(prepared) = Library::prepared_sources(units.clone(), None).unwrap()
        else {
            unreachable!("a prepared library");
        };
        prepared.carry_host_part("table", &"shipped").unwrap();
        let key = sysmlv2_model::libcache::hash_units(
            units.iter().map(|(n, t)| (n.as_str(), t.as_str())),
        );
        let bytes = prepared.to_bytes(key).unwrap();
        let sources = serde_json::json!([{"name": "lib.sysml", "text": units[0].1}]).to_string();
        let held = |keep: Option<bool>| {
            let decoded = PreparedLibrary::from_snapshot(bytes.clone(), &sources, None, keep)
                .expect("the snapshot decodes");
            match decoded.inner {
                Library::Prepared(library) => library.take_host_part::<String>("table"),
                _ => unreachable!("a prepared library"),
            }
        };
        assert_eq!(held(None), None, "dropped by default");
        assert_eq!(held(Some(false)), None);
        assert_eq!(held(Some(true)).as_deref(), Some("shipped"));
    }
}
