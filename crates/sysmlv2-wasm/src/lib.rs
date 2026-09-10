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

use serde::Deserialize;
use serde_json::json;
use wasm_bindgen::prelude::*;

use sysmlv2_model::check::ConstraintVerdict;
use sysmlv2_model::eval::Value as EvalValue;
use sysmlv2_model::json::ElementRef;
use sysmlv2_solve::{PropagateConfig, PropagateOutcome};
use sysmlv2_syntax::parser::parse_expression;
use sysmlv2_syntax::span::LineIndex;
use sysmlv2_transform::{Indent, Library, Session as TSession, check_sources_with_library};

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
        let r = inner.resolved();
        let all: Vec<ElementRef> = r.user_elements().collect();
        all.into_iter()
            .find(|e| r.element_id(*e).to_string() == id)
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

fn parse_sources(json: &str) -> Result<Vec<(String, String)>, String> {
    let sources: Vec<SourceIn> =
        serde_json::from_str(json).map_err(|e| format!("sources must be [{{name, text}}]: {e}"))?;
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

fn default_view() -> String {
    "tree".to_string()
}

fn yes() -> bool {
    true
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
        names: &Option<Vec<String>>,
    ) -> Result<Option<Vec<ElementRef>>, String> {
        let Some(names) = names.as_ref().filter(|n| !n.is_empty()) else {
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

    fn value_to_json(&mut self, v: &EvalValue) -> serde_json::Value {
        match v {
            EvalValue::Boolean(b) => json!(b),
            EvalValue::Integer(i) => json!(i),
            EvalValue::Rational(f) => json!(f),
            EvalValue::String(s) => json!(s),
            EvalValue::Indeterminate => json!({ "@indeterminate": true }),
            EvalValue::Element(e) | EvalValue::Unbound(e) => json!({
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

#[wasm_bindgen]
impl Session {
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

    // ---- navigation ----

    /// The element's qualified name (undefined for anonymous elements).
    #[wasm_bindgen(js_name = qualifiedName)]
    pub fn qualified_name(&mut self, e: &Element) -> Result<Option<String>, String> {
        self.guard(e)?;
        Ok(self.inner.resolved().element_qualified_name(e.e))
    }

    /// The element's declared name.
    pub fn name(&mut self, e: &Element) -> Result<Option<String>, String> {
        self.guard(e)?;
        Ok(self.inner.resolved().element_name(e.e).map(str::to_string))
    }

    /// The element's declared short name (`<shortName>`), when it has one.
    #[wasm_bindgen(js_name = shortName)]
    pub fn short_name(&mut self, e: &Element) -> Result<Option<String>, String> {
        self.guard(e)?;
        Ok(self
            .inner
            .resolved()
            .element_short_name(e.e)
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
    pub fn to_compact_cbor_elided(&self) -> Vec<u8> {
        self.inner.to_compact_cbor_elided()
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
        Ok(apply_report_json(result, report))
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
        Ok(apply_report_json(result, report))
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
    #[wasm_bindgen(js_name = toPlantuml)]
    pub fn to_plantuml(&mut self, opts_json: Option<String>) -> Result<String, String> {
        // Absent options deserialize as `{}` so serde's field defaults
        // apply uniformly.
        let opts_json = opts_json.filter(|s| !s.is_empty());
        let opts: PlantumlOpts = serde_json::from_str(opts_json.as_deref().unwrap_or("{}"))
            .map_err(|e| format!("bad options: {e}"))?;
        let view = match opts.view.as_str() {
            "tree" => sysmlv2_viz::View::Tree,
            "interconnection" | "ic" => sysmlv2_viz::View::Interconnection,
            "state" => sysmlv2_viz::View::State,
            "action" => sysmlv2_viz::View::Action,
            "sequence" | "seq" => sysmlv2_viz::View::Sequence,
            "case" => sysmlv2_viz::View::Case,
            "mixed" => sysmlv2_viz::View::Mixed,
            other => {
                return Err(format!(
                    "unknown view: {other} (expected tree, interconnection, state, action, sequence, case, or mixed)"
                ));
            }
        };
        let line_style = match opts.line_style.as_deref() {
            None => sysmlv2_viz::LineStyle::Default,
            Some("polyline") => sysmlv2_viz::LineStyle::Polyline,
            Some("ortho") => sysmlv2_viz::LineStyle::Ortho,
            Some(other) => {
                return Err(format!(
                    "unknown line style: {other} (expected polyline or ortho)"
                ));
            }
        };
        let root = match opts.element.as_deref() {
            Some(name) => Some(
                self.inner
                    .resolved()
                    .resolve_qualified(name)
                    .ok_or_else(|| format!("element not found: {name}"))?,
            ),
            None => None,
        };
        let roots = self.resolve_roots(&opts.roots)?;
        let viz = sysmlv2_viz::VizOptions {
            direction: if opts.horizontal {
                sysmlv2_viz::Direction::LeftToRight
            } else {
                sysmlv2_viz::Direction::TopToBottom
            },
            show_values: opts.show_values,
            view,
            show_notes: opts.show_notes,
            show_metadata: opts.show_metadata,
            show_inherited: opts.show_inherited,
            show_lib: opts.show_lib,
            show_imported: opts.show_imported,
            line_style,
            std_color: opts.std_color,
            link_template: opts.link_template,
            roots,
        };
        Ok(sysmlv2_viz::plantuml(self.inner.resolved(), root, &viz))
    }

    /// Emit the structured diagram graph (nodes with element identity,
    /// source spans, and compartment rows; edges with kinds) for a
    /// view — the native renderer's input. Options as in
    /// [`Self::to_plantuml`]; views without a graph emitter yet error.
    #[wasm_bindgen(js_name = toGraph)]
    pub fn to_graph(&mut self, opts_json: Option<String>) -> Result<String, String> {
        let opts_json = opts_json.filter(|s| !s.is_empty());
        let opts: PlantumlOpts = serde_json::from_str(opts_json.as_deref().unwrap_or("{}"))
            .map_err(|e| format!("bad options: {e}"))?;
        let view = match opts.view.as_str() {
            "tree" => sysmlv2_viz::View::Tree,
            "interconnection" | "ic" => sysmlv2_viz::View::Interconnection,
            "state" => sysmlv2_viz::View::State,
            "action" => sysmlv2_viz::View::Action,
            other => return Err(format!("no structured-graph emitter for view: {other}")),
        };
        let root = match opts.element.as_deref() {
            Some(name) => Some(
                self.inner
                    .resolved()
                    .resolve_qualified(name)
                    .ok_or_else(|| format!("element not found: {name}"))?,
            ),
            None => None,
        };
        let roots = self.resolve_roots(&opts.roots)?;
        let viz = sysmlv2_viz::VizOptions {
            view,
            show_values: opts.show_values,
            show_notes: opts.show_notes,
            show_metadata: opts.show_metadata,
            show_inherited: opts.show_inherited,
            show_lib: opts.show_lib,
            show_imported: opts.show_imported,
            roots,
            ..Default::default()
        };
        sysmlv2_viz::graph(self.inner.resolved(), root, &viz).map(|v| v.to_string())
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
    pub fn edit(&mut self, ops_json: &str) -> Result<String, String> {
        let resolved = self.resolve_ops(Self::parse_ops(ops_json)?)?;
        let mut batch = self.inner.edit();
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
        let mut indexes: std::collections::HashMap<usize, LineIndex> = Default::default();
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
                        let pos = b.site.and_then(|(unit, span)| {
                            let src = inner.source(unit)?;
                            let lc = LineIndex::new(src).line_col(span.start);
                            Some((unit, lc))
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
                let li = indexes
                    .entry(c.unit)
                    .or_insert_with(|| LineIndex::new(inner.source(c.unit).unwrap_or("")));
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
    /// `{findings: [{rule, severity, message, unit, unitName, line,
    /// col, endLine, endCol, element, suggest, fix}], summary:
    /// {errors, warnings, infos, hints}}` — 1-based positions over the finding's
    /// name span; `unit` and the positions are null on `lint-config`
    /// findings. `element` (nullable) = the finding's edit-target
    /// spelling (`::`-qualified name or `@<id>`) for host quick fixes;
    /// `suggest` (nullable) = a naming finding's style-converted
    /// replacement name. `fix` (nullable)
    /// = `{label, deletes, edits: [{unit, unitName, start, end,
    /// replacement}]}` with **byte** offsets over the unit's current
    /// text (the splice currency every edit surface here uses);
    /// `deletes` marks fixes hosts must gate behind explicit opt-in.
    /// `alternatives` (array, same shape as `fix`) are equally-valid
    /// remedies for a quick-fix menu — a dimensionally ambiguous unit
    /// lists every compatible quantity type — never auto-applied.
    pub fn lint(&mut self, config_json: Option<String>) -> Result<String, String> {
        let cfg = match config_json.as_deref().filter(|s| !s.trim().is_empty()) {
            Some(text) => sysmlv2_lint::Config::from_json(text)?,
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
        let names: std::collections::HashMap<usize, String> = self
            .inner
            .units()
            .map(|(i, n, _)| (i, n.to_string()))
            .collect();
        let mut indexes: std::collections::HashMap<usize, LineIndex> = Default::default();
        let inner = &self.inner;
        let (mut errors, mut warnings, mut infos, mut hints) = (0usize, 0usize, 0usize, 0usize);
        let findings_json: Vec<serde_json::Value> = findings
            .iter()
            .map(|f| {
                let severity = match f.severity {
                    sysmlv2_lint::Severity::Error => {
                        errors += 1;
                        "error"
                    }
                    sysmlv2_lint::Severity::Info => {
                        infos += 1;
                        "info"
                    }
                    sysmlv2_lint::Severity::Hint => {
                        hints += 1;
                        "hint"
                    }
                    _ => {
                        warnings += 1;
                        "warn"
                    }
                };
                let pos = f.unit.zip(f.span).map(|(unit, span)| {
                    let li = indexes
                        .entry(unit)
                        .or_insert_with(|| LineIndex::new(inner.source(unit).unwrap_or("")));
                    (unit, li.line_col(span.start), li.line_col(span.end))
                });
                let fix_json = |fx: &sysmlv2_lint::Fix| {
                    let edits: Vec<serde_json::Value> = fx
                        .edits
                        .iter()
                        .map(|e| {
                            json!({
                                "unit": e.unit,
                                "unitName": names.get(&e.unit),
                                "start": e.span.start,
                                "end": e.span.end,
                                "replacement": e.replacement,
                            })
                        })
                        .collect();
                    json!({"label": fx.label, "deletes": fx.deletes, "edits": edits})
                };
                let alternatives: Vec<serde_json::Value> =
                    f.alternatives.iter().map(fix_json).collect();
                json!({
                    "rule": f.rule,
                    "severity": severity,
                    "message": f.message,
                    "unit": f.unit,
                    "unitName": f.unit.and_then(|u| names.get(&u)),
                    "line": pos.map(|(_, s, _)| s.line),
                    "col": pos.map(|(_, s, _)| s.col),
                    "endLine": pos.map(|(_, _, e)| e.line),
                    "endCol": pos.map(|(_, _, e)| e.col),
                    "element": f.element,
                    "suggest": f.suggest,
                    "fix": f.fix.as_ref().map(fix_json),
                    "alternatives": alternatives,
                })
            })
            .collect();
        Ok(json!({
            "findings": findings_json,
            "summary": {"errors": errors, "warnings": warnings, "infos": infos, "hints": hints},
        })
        .to_string())
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
#[wasm_bindgen(js_name = formatSource)]
pub fn format_source_js(text: &str, config_json: Option<String>) -> Result<String, String> {
    let config = match config_json.as_deref() {
        None | Some("") => sysmlv2_lint::Config::default(),
        Some(json) => sysmlv2_lint::Config::from_json(json)?,
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
#[wasm_bindgen(js_name = canonicalizationDigest)]
pub fn canonicalization_digest_js(config_json: Option<String>) -> Result<String, String> {
    let cfg = match config_json.as_deref().filter(|s| !s.trim().is_empty()) {
        Some(text) => sysmlv2_lint::Config::from_json(text)?,
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
                    let kind = match &o.kind {
                        sysmlv2_lint::OptionKind::Int { default, min, zero } => json!({
                            "kind": "int", "default": default, "min": min, "zero": zero,
                        }),
                        sysmlv2_lint::OptionKind::Choice { default, values } => json!({
                            "kind": "choice", "default": default, "values": values,
                        }),
                    };
                    let mut o = json!({"key": o.key, "label": o.label});
                    o.as_object_mut()
                        .unwrap()
                        .extend(kind.as_object().unwrap().clone());
                    o
                })
                .collect();
            json!({
                "id": r.id,
                "description": r.description,
                "default": r.default.as_str(),
                "styles": r.styles,
                "families": families,
                "scopes": scopes,
                "options": options,
            })
        })
        .collect();
    serde_json::to_string(&rules).unwrap()
}

/// Check sources (JSON `[{name, text}]`) the way `sysmlv2 check` does:
/// per-unit parse and body-context validation always; referential and
/// semantic checks against the standard library when `lib_sources_json`
/// (same shape) is given. Returns findings as a JSON string:
/// `[{severity, message, unit, line, col, endLine, endCol}]` (1-based
/// positions; the end pair spans the full diagnostic, so markers cover
/// the whole offending construct rather than just its start). A broken
/// parse is a finding, not an error.
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
    let indexes: std::collections::HashMap<&str, LineIndex> = sources
        .iter()
        .map(|(name, src)| (name.as_str(), LineIndex::new(src)))
        .collect();
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
    Ok(serde_json::Value::Array(findings).to_string())
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

fn apply_report_json(result: serde_json::Value, report: sysmlv2_cbor::ApplyReport) -> String {
    serde_json::json!({ "result": result, "report": apply_report_value(&report) }).to_string()
}

/// The canonical spelling of an element name:
/// JSON `{"spelling", "quoted"}` — `spelling` is exactly what the
/// printer emits (bare, or a single-quoted restricted name for reserved
/// words and non-basic characters) and `quoted` says which. Errors when
/// the string cannot be a name (empty). `dialect` is `"sysml"` (default)
/// or `"kerml"`; the reserved-word sets differ. Generators that mint
/// names from external vocabularies call this instead of copying the
/// parser's keyword table.
#[wasm_bindgen(js_name = canonicalName)]
pub fn canonical_name_js(name: &str, dialect: Option<String>) -> Result<String, String> {
    let dialect = match dialect.as_deref() {
        None | Some("") | Some("sysml") => sysmlv2_syntax::ast::Dialect::Sysml,
        Some("kerml") => sysmlv2_syntax::ast::Dialect::Kerml,
        Some(d) => return Err(format!("dialect must be \"sysml\" or \"kerml\", got {d:?}")),
    };
    let c = sysmlv2_syntax::name::canonical_name(dialect, name).map_err(|e| e.to_string())?;
    Ok(json!({ "spelling": c.spelling, "quoted": c.quoted }).to_string())
}

/// The toolkit version this module was built from.
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
    let opts = sysmlv2_cbor::DeltaOptions {
        portable,
        units,
        ..Default::default()
    };
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

#[wasm_bindgen]
impl LspServer {
    /// The syntax-tier-only server (no standard library).
    /// NOTE: a fallible `#[wasm_bindgen(constructor)]` (Result return)
    /// leaves the JS object with a null pointer — keep the constructor
    /// infallible and use [`Self::with_library`] for the library shape.
    #[wasm_bindgen(constructor)]
    #[allow(clippy::new_without_default)]
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
