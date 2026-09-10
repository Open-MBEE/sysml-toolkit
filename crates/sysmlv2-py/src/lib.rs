//! Python binding for the sysmlv2 stack: a thin,
//! generation-guarded mirror of `sysmlv2_transform::Session` +
//! `EditBuilder`. No Python-side model mirror — every call hits the
//! Rust session, so the workspace gates (round-trip, semantic identity,
//! splice minimality) apply identically.
//!
//! Handle discipline: [`Element`] and [`Reference`] handles are minted
//! against one committed state of a session (a *generation*). A
//! successful commit bumps the generation and invalidates outstanding
//! handles — using one afterwards raises `ValueError` instead of
//! silently denoting the wrong element.

use pyo3::IntoPyObjectExt;
use pyo3::exceptions::{PyRuntimeError, PyValueError};
use pyo3::prelude::*;
use pyo3::types::{PyBytes, PyList, PyTuple};

use sysmlv2_model::eval::Value as EvalValue;
use sysmlv2_model::json::{ElementRef, RefSite};
use sysmlv2_syntax::parser::parse_expression;
use sysmlv2_transform::{Session as TSession, TransformError};

/// An opaque handle to one element of a session's resolved model.
#[pyclass(frozen)]
#[derive(Clone)]
struct Element {
    e: ElementRef,
    gen: u64,
}

#[pymethods]
impl Element {
    fn __repr__(&self) -> String {
        format!("<Element {:?} gen {}>", self.e, self.gen)
    }

    fn __eq__(&self, other: &Element) -> bool {
        self.e == other.e && self.gen == other.gen
    }

    fn __hash__(&self) -> u64 {
        use std::collections::hash_map::DefaultHasher;
        use std::hash::{Hash, Hasher};
        let mut h = DefaultHasher::new();
        (self.e, self.gen).hash(&mut h);
        h.finish()
    }
}

/// One resolved reference site (see `Session.references`).
#[pyclass(frozen)]
#[derive(Clone)]
struct Reference {
    site: RefSite,
    gen: u64,
}

#[pymethods]
impl Reference {
    /// Model unit index the reference was written in.
    #[getter]
    fn unit(&self) -> usize {
        self.site.unit
    }

    /// The serialized property the resolution feeds (`type`,
    /// `redefinedFeature`, `qualifier`, …).
    #[getter]
    fn kind(&self) -> &str {
        &self.site.kind
    }

    /// Byte range of the whole qualified name in the unit's source.
    #[getter]
    fn span(&self) -> (u32, u32) {
        (self.site.span.start, self.site.span.end)
    }

    /// Byte range of the segment that names the target.
    #[getter]
    fn name_span(&self) -> (u32, u32) {
        (self.site.name_span.start, self.site.name_span.end)
    }

    /// The element the reference denotes.
    #[getter]
    fn target(&self) -> Element {
        Element {
            e: self.site.target,
            gen: self.gen,
        }
    }

    fn __repr__(&self) -> String {
        format!(
            "<Reference kind={} unit={} at {}..{}>",
            self.site.kind, self.site.unit, self.site.name_span.start, self.site.name_span.end
        )
    }
}

/// One committed batch's outcome.
#[pyclass(frozen)]
struct CommitReport {
    /// `(old id, new id)` for elements whose interchange id moved.
    #[pyo3(get)]
    id_map: Vec<(String, String)>,
    /// Non-fatal observations.
    #[pyo3(get)]
    findings: Vec<String>,
}

#[pymethods]
impl CommitReport {
    fn __repr__(&self) -> String {
        format!(
            "<CommitReport {} id move(s), {} finding(s)>",
            self.id_map.len(),
            self.findings.len()
        )
    }
}

enum Op {
    Rename(ElementRef, String),
    SetFeatureValue(ElementRef, String),
    InsertMember(ElementRef, String),
    InsertTopLevel(String, String),
    Remove(ElementRef),
    Retarget(RefSite, ElementRef),
    ExtractDefinition(ElementRef, Option<String>),
    InlineDefinition(ElementRef),
}

/// An edit batch recorded against one session generation; apply it with
/// `Session.commit`.
#[pyclass]
struct EditBatch {
    ops: Vec<Op>,
    gen: u64,
}

#[pymethods]
impl EditBatch {
    /// Rename `e`; every reference site written with its name respells.
    fn rename(&mut self, e: &Element, new_name: &str) -> PyResult<()> {
        self.guard(e.gen)?;
        self.ops.push(Op::Rename(e.e, new_name.to_string()));
        Ok(())
    }

    /// Replace `e`'s `= …` value (or add one to a `;`-terminated
    /// declaration).
    fn set_feature_value(&mut self, e: &Element, expr: &str) -> PyResult<()> {
        self.guard(e.gen)?;
        self.ops.push(Op::SetFeatureValue(e.e, expr.to_string()));
        Ok(())
    }

    /// Insert `text` as the last member of `owner`'s body.
    fn insert_member(&mut self, owner: &Element, text: &str) -> PyResult<()> {
        self.guard(owner.gen)?;
        self.ops.push(Op::InsertMember(owner.e, text.to_string()));
        Ok(())
    }

    /// Append `text` as a top-level member of the named unit.
    fn insert_top_level(&mut self, unit_name: &str, text: &str) {
        self.ops
            .push(Op::InsertTopLevel(unit_name.to_string(), text.to_string()));
    }

    /// Remove the member declaration that created `e`.
    fn remove(&mut self, e: &Element) -> PyResult<()> {
        self.guard(e.gen)?;
        self.ops.push(Op::Remove(e.e));
        Ok(())
    }

    /// Respell one reference site to denote `to`.
    fn retarget(&mut self, site: &Reference, to: &Element) -> PyResult<()> {
        self.guard(site.gen)?;
        self.guard(to.gen)?;
        self.ops.push(Op::Retarget(site.site.clone(), to.e));
        Ok(())
    }

    /// Extract `usage`'s inline body into a new definition typed back
    /// onto the usage. `name=None` synthesizes
    /// UpperCamel from the usage's declared name. The commit verifies
    /// every carried reference at its new home and rolls back on any
    /// structural change beyond the owned→inherited move.
    #[pyo3(signature = (usage, name = None))]
    fn extract_definition(&mut self, usage: &Element, name: Option<&str>) -> PyResult<()> {
        self.guard(usage.gen)?;
        self.ops
            .push(Op::ExtractDefinition(usage.e, name.map(str::to_string)));
        Ok(())
    }

    /// Inline `definition`'s body into its sole typed usage and delete
    /// it. Inlining a definition just produced by
    /// `extract_definition` restores the original text byte-for-byte.
    /// Imports the deletion leaves unused surface as report findings.
    fn inline_definition(&mut self, definition: &Element) -> PyResult<()> {
        self.guard(definition.gen)?;
        self.ops.push(Op::InlineDefinition(definition.e));
        Ok(())
    }

    fn __len__(&self) -> usize {
        self.ops.len()
    }
}

impl EditBatch {
    fn guard(&self, gen: u64) -> PyResult<()> {
        if gen != self.gen {
            return Err(PyValueError::new_err(
                "stale handle: it belongs to a different session state",
            ));
        }
        Ok(())
    }
}

/// A set of model sources (text files or interchange JSON) with their
/// resolved model. All navigation, querying, and editing goes through
/// the session; a successful `commit` re-resolves and bumps the handle
/// generation. Unsendable: a session lives on the thread that created
/// it (the model's library-cache slot is not thread-safe).
#[pyclass(unsendable)]
struct Session {
    inner: TSession,
    gen: u64,
}

fn runtime<E: std::fmt::Display>(e: E) -> PyErr {
    PyRuntimeError::new_err(e.to_string())
}

impl Session {
    fn mint(&self, e: ElementRef) -> Element {
        Element { e, gen: self.gen }
    }

    fn guard(&self, gen: u64) -> PyResult<()> {
        if gen != self.gen {
            return Err(PyValueError::new_err(
                "stale handle: the session was edited since it was minted \
                 (re-resolve after commit)",
            ));
        }
        Ok(())
    }

    fn value_to_py(&self, py: Python<'_>, v: &EvalValue) -> PyResult<PyObject> {
        match v {
            EvalValue::Boolean(b) => b.into_py_any(py),
            EvalValue::Integer(i) => i.into_py_any(py),
            EvalValue::Rational(f) => f.into_py_any(py),
            EvalValue::String(s) => s.into_py_any(py),
            EvalValue::Element(e) | EvalValue::Unbound(e) => {
                Ok(Py::new(py, self.mint(*e))?.into_any())
            }
            // An indeterminate result (an operation over an unbound
            // feature) has no element to hand back — Python sees None.
            EvalValue::Indeterminate => Ok(py.None()),
            EvalValue::Quantity(n, unit) => {
                let num = self.value_to_py(py, n)?;
                let unit = unit.display().into_py_any(py)?;
                Ok(PyTuple::new(py, [num, unit])?.unbind().into_any())
            }
            EvalValue::Instance {
                ty_name, fields, ..
            } => {
                let dict = pyo3::types::PyDict::new(py);
                dict.set_item("@type", ty_name)?;
                for (name, value) in fields {
                    dict.set_item(name, self.value_to_py(py, value)?)?;
                }
                Ok(dict.unbind().into_any())
            }
            EvalValue::Sequence(items) => {
                let list = PyList::empty(py);
                for item in items {
                    list.append(self.value_to_py(py, item)?)?;
                }
                Ok(list.unbind().into_any())
            }
        }
    }
}

#[pymethods]
impl Session {
    /// Open a session over `.sysml` / `.kerml` files.
    #[staticmethod]
    fn from_files(paths: Vec<String>) -> PyResult<Session> {
        let paths: Vec<std::path::PathBuf> =
            paths.into_iter().map(std::path::PathBuf::from).collect();
        Ok(Session {
            inner: TSession::open(&paths).map_err(runtime)?,
            gen: 0,
        })
    }

    /// Open a session over in-memory `(unit name, text)` sources.
    #[staticmethod]
    fn from_sources(sources: Vec<(String, String)>) -> PyResult<Session> {
        Ok(Session {
            inner: TSession::from_sources(sources).map_err(runtime)?,
            gen: 0,
        })
    }

    /// Open a session over an interchange JSON document (compact or full
    /// form; Flexo `{payload, identity}` wrapping accepted). Pass `lib`
    /// (a standard-library directory) to name library element ids
    /// during the lift and keep the library loaded for resolution — a
    /// library-typed payload generally needs it.
    #[staticmethod]
    #[pyo3(signature = (json, lib = None))]
    fn from_interchange_json(json: &str, lib: Option<&str>) -> PyResult<Session> {
        let value: serde_json::Value =
            serde_json::from_str(json).map_err(|e| PyValueError::new_err(e.to_string()))?;
        Ok(Session {
            inner: TSession::from_interchange_json_with_library(
                &value,
                lib.map(std::path::Path::new),
            )
            .map_err(runtime)?,
            gen: 0,
        })
    }

    /// Open a session over a compact-form CBOR payload (`bytes`) — the
    /// binary counterpart of `from_interchange_json`; `lib` as there.
    #[staticmethod]
    #[pyo3(signature = (data, lib = None))]
    fn from_compact_cbor(data: &[u8], lib: Option<&str>) -> PyResult<Session> {
        Ok(Session {
            inner: TSession::from_compact_cbor_with_library(data, lib.map(std::path::Path::new))
                .map_err(runtime)?,
            gen: 0,
        })
    }

    /// Resolve against a standard-library directory (the sealed-snapshot
    /// cache applies automatically). Invalidates outstanding handles.
    fn load_library(&mut self, dir: &str) -> PyResult<()> {
        self.inner
            .load_library(std::path::Path::new(dir))
            .map_err(runtime)?;
        self.gen += 1;
        Ok(())
    }

    /// Resolve a `::`-qualified name to an element handle.
    fn resolve(&mut self, qualified_name: &str) -> Option<Element> {
        let gen = self.gen;
        self.inner
            .resolved()
            .resolve_qualified(qualified_name)
            .map(|e| Element { e, gen })
    }

    /// Evaluate an ad-hoc KerML query expression at the root namespace
    /// (closed-world `istype`, `ownedMember(x)` / `ownedFeature(x)`
    /// reflection — the `sysmlv2 query` semantics).
    fn query(&mut self, py: Python<'_>, expr: &str) -> PyResult<PyObject> {
        let parsed = parse_expression(expr);
        let Some(ast) = parsed.expr else {
            let msg = parsed
                .diagnostics
                .first()
                .map(|d| d.message.clone())
                .unwrap_or_else(|| "not an expression".into());
            return Err(PyValueError::new_err(msg));
        };
        let root = self.inner.resolved().root_scope();
        let value = self.inner.resolved().query(root, &ast).map_err(runtime)?;
        self.value_to_py(py, &value)
    }

    /// Evaluate `e`'s bound feature value.
    fn evaluate(&mut self, py: Python<'_>, e: &Element) -> PyResult<PyObject> {
        self.guard(e.gen)?;
        let value = self.inner.resolved().evaluate(e.e).map_err(runtime)?;
        self.value_to_py(py, &value)
    }

    // ---- navigation ----

    /// The element's qualified name (None for anonymous elements).
    fn qualified_name(&mut self, e: &Element) -> PyResult<Option<String>> {
        self.guard(e.gen)?;
        Ok(self.inner.resolved().element_qualified_name(e.e))
    }

    /// The element's declared name.
    fn name(&mut self, e: &Element) -> PyResult<Option<String>> {
        self.guard(e.gen)?;
        Ok(self.inner.resolved().element_name(e.e).map(str::to_string))
    }

    /// The element's abstract-syntax metaclass (`PartUsage`, …).
    fn metaclass(&mut self, e: &Element) -> PyResult<&'static str> {
        self.guard(e.gen)?;
        Ok(self.inner.resolved().element_type(e.e))
    }

    /// The element's interchange `@id`.
    fn element_id(&mut self, e: &Element) -> PyResult<String> {
        self.guard(e.gen)?;
        Ok(self.inner.resolved().element_id(e.e).to_string())
    }

    /// The owning element (None for document roots).
    fn owner(&mut self, e: &Element) -> PyResult<Option<Element>> {
        self.guard(e.gen)?;
        let gen = self.gen;
        Ok(self.inner.resolved().owner(e.e).map(|e| Element { e, gen }))
    }

    /// Owned members, in declaration order (KerML `ownedMember`).
    fn members(&mut self, e: &Element) -> PyResult<Vec<Element>> {
        self.guard(e.gen)?;
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
    fn features(&mut self, e: &Element) -> PyResult<Vec<Element>> {
        self.guard(e.gen)?;
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
    fn typings(&mut self, e: &Element) -> PyResult<Vec<Element>> {
        self.guard(e.gen)?;
        let gen = self.gen;
        Ok(self
            .inner
            .resolved()
            .typings(e.e)
            .into_iter()
            .map(|e| Element { e, gen })
            .collect())
    }

    /// Does `e` reach `ancestor` through the explicit specialization
    /// closure?
    fn conforms(&mut self, e: &Element, ancestor: &Element) -> PyResult<bool> {
        self.guard(e.gen)?;
        self.guard(ancestor.gen)?;
        Ok(self.inner.resolved().conforms(e.e, ancestor.e))
    }

    /// Every element of the given metaclass.
    fn elements_of_metaclass(&mut self, ty: &str) -> Vec<Element> {
        let gen = self.gen;
        self.inner
            .resolved()
            .elements_of_metaclass(ty)
            .into_iter()
            .map(|e| Element { e, gen })
            .collect()
    }

    /// Whether the element belongs to a loaded library.
    fn is_library_element(&mut self, e: &Element) -> PyResult<bool> {
        self.guard(e.gen)?;
        Ok(self.inner.resolved().is_library_element(e.e))
    }

    /// The reference sites that resolve to `e` (find-usages).
    fn references(&mut self, e: &Element) -> PyResult<Vec<Reference>> {
        self.guard(e.gen)?;
        let gen = self.gen;
        Ok(self
            .inner
            .resolved()
            .references_to(e.e)
            .into_iter()
            .map(|site| Reference { site, gen })
            .collect())
    }

    // ---- sources and emission ----

    /// The user units as `(model unit index, name, text)`.
    fn units(&self) -> Vec<(usize, String, String)> {
        self.inner
            .units()
            .map(|(i, n, s)| (i, n.to_string(), s.to_string()))
            .collect()
    }

    /// Current text of a unit by model unit index (None for library
    /// units).
    fn source(&self, unit: usize) -> Option<String> {
        self.inner.source(unit).map(str::to_string)
    }

    /// How many references failed to resolve.
    fn unresolved_count(&self) -> usize {
        self.inner.resolved_ref().unresolved_count()
    }

    /// Non-fatal problems from lifting interchange JSON.
    fn warnings(&self) -> Vec<String> {
        self.inner.warnings().to_vec()
    }

    /// Compact interchange JSON (KerML 10.4) for the session's model.
    fn to_compact_json(&self) -> String {
        serde_json::to_string_pretty(&self.inner.to_compact_json()).expect("serializable")
    }

    /// Compact-form CBOR (`bytes`) for the session's model — the
    /// deterministic binary re-encoding of `to_compact_json`, decodable
    /// back to the identical element array.
    fn to_compact_cbor<'py>(&self, py: Python<'py>) -> Bound<'py, PyBytes> {
        PyBytes::new(py, &self.inner.to_compact_cbor())
    }

    /// Full-form CBOR (`bytes`) — the binary re-encoding of
    /// `to_full_json`. Emit view only; transport the compact form.
    #[pyo3(signature = (recover_refs = true))]
    fn to_full_cbor<'py>(&self, py: Python<'py>, recover_refs: bool) -> Bound<'py, PyBytes> {
        PyBytes::new(py, &self.inner.to_full_cbor(recover_refs))
    }

    /// Full interchange JSON (derived properties + implied
    /// relationships). With `recover_refs=True`, references that
    /// serialize as dangling ids also carry their source spelling, so a
    /// partial model survives emit → reload losslessly (the Flexo
    /// change-record path).
    #[pyo3(signature = (recover_refs = true))]
    fn to_full_json(&self, recover_refs: bool) -> String {
        serde_json::to_string_pretty(&self.inner.to_full_json_with(recover_refs))
            .expect("serializable")
    }

    /// Map an interchange document's ids to this session's ids by
    /// qualified name: `[(input id, session id)]`.
    fn id_map_from(&mut self, json: &str) -> PyResult<Vec<(String, String)>> {
        let value: serde_json::Value =
            serde_json::from_str(json).map_err(|e| PyValueError::new_err(e.to_string()))?;
        Ok(self
            .inner
            .id_map_from(&value)
            .into_iter()
            .map(|(a, b)| (a.to_string(), b.to_string()))
            .collect())
    }

    // ---- editing ----

    /// Respell every reference with the shortest spelling that still
    /// resolves to the same element: bare name where unambiguous,
    /// a qualified suffix where needed, the printed form as the
    /// untouched fallback — verified by reparse; declarations and
    /// interchange ids are untouched. Returns `(respelled, reverted)`
    /// counts. When anything was respelled the session rebuilt:
    /// outstanding handles go stale.
    fn minimize_qualifications(&mut self) -> PyResult<(usize, usize)> {
        let report = self
            .inner
            .minimize_qualifications()
            .map_err(|e| PyRuntimeError::new_err(e.to_string()))?;
        if report.respelled > 0 {
            self.gen += 1;
        }
        Ok((report.respelled, report.reverted))
    }

    /// Start an edit batch against the current session state.
    fn edit(&self) -> EditBatch {
        EditBatch {
            ops: Vec::new(),
            gen: self.gen,
        }
    }

    /// Apply an edit batch: splice, reparse, re-resolve, verify semantic
    /// identity — or raise with the session left untouched. A successful
    /// commit invalidates outstanding handles.
    fn commit(&mut self, batch: &mut EditBatch) -> PyResult<CommitReport> {
        self.guard(batch.gen)?;
        let ops = std::mem::take(&mut batch.ops);
        // Consumed: a batch cannot be committed twice.
        batch.gen = u64::MAX;
        let mut builder = self.inner.edit();
        for op in &ops {
            match op {
                Op::Rename(e, n) => {
                    builder.rename(*e, n);
                }
                Op::SetFeatureValue(e, x) => {
                    builder.set_feature_value(*e, x);
                }
                Op::InsertMember(o, t) => {
                    builder.insert_member(*o, t);
                }
                Op::InsertTopLevel(u, t) => {
                    builder.insert_top_level(u, t);
                }
                Op::Remove(e) => {
                    builder.remove(*e);
                }
                Op::Retarget(site, to) => {
                    builder.retarget(site.clone(), *to);
                }
                Op::ExtractDefinition(e, name) => {
                    builder.extract_definition(*e, name.as_deref());
                }
                Op::InlineDefinition(e) => {
                    builder.inline_definition(*e);
                }
            }
        }
        let report = builder.commit().map_err(|e| match e {
            TransformError::InvalidName(_)
            | TransformError::InvalidExpression { .. }
            | TransformError::InvalidMember { .. }
            | TransformError::UnknownUnit(_)
            | TransformError::ExtractIneligible { .. }
            | TransformError::InlineIneligible { .. }
            | TransformError::NameTaken { .. } => PyValueError::new_err(e.to_string()),
            other => PyRuntimeError::new_err(other.to_string()),
        })?;
        self.gen += 1;
        Ok(CommitReport {
            id_map: report
                .id_map
                .into_iter()
                .map(|(a, b)| (a.to_string(), b.to_string()))
                .collect(),
            findings: report.findings,
        })
    }

    /// Emit a PlantUML diagram of the session's model. `view`
    /// picks the diagram: `"tree"` (structure: packages, definitions,
    /// usages with attribute compartments, plus composition / typing /
    /// specialization edges), `"interconnection"` (parts as nested
    /// blocks with ports; connections, interfaces, bindings, and flows
    /// as edges), `"state"` (state machines: transitions labelled
    /// `trigger [guard] / effect`, entry/do/exit), `"action"`
    /// (action flows: control nodes, successions, dashed flow edges),
    /// `"sequence"` (lifelines and messages between events, ordered by
    /// event successions), `"case"` (use cases: actors, subjects,
    /// objectives, «include» edges), or `"mixed"` (everything on one
    /// canvas). `element` roots the diagram at one ::-qualified
    /// element; `horizontal` lays it out left-to-right;
    /// `show_values=False` omits `= value` on attribute lines (tree
    /// view). Comment/doc bodies attach as notes (`show_notes=False`
    /// omits); `show_metadata=False` hides metadata;
    /// `show_inherited=True` adds `^`-marked inherited compartment
    /// lines; `show_lib=True` gives referenced library types marked
    /// nodes; `show_imported=True` draws «import» edges;
    /// `line_style="polyline"|"ortho"` picks edge routing;
    /// `std_color=True` colors nodes by metaclass family;
    /// `link_template` embeds `[[hyperlinks]]` (placeholders `{file}`,
    /// `{line}`, `{col}`, `{qname}`, `{id}`) carried into rendered
    /// SVG. Feed the text to any PlantUML build.
    #[pyo3(signature = (element = None, view = "tree", horizontal = false, show_values = true,
                        show_notes = true, show_metadata = true, show_inherited = false,
                        show_lib = false, show_imported = false, line_style = None,
                        std_color = false, link_template = None))]
    // `&mut self`: rendering resolves lazily through the session's
    // model; the name is the Python API, not a Rust conversion.
    #[allow(clippy::too_many_arguments, clippy::wrong_self_convention)]
    fn to_plantuml(
        &mut self,
        element: Option<&str>,
        view: &str,
        horizontal: bool,
        show_values: bool,
        show_notes: bool,
        show_metadata: bool,
        show_inherited: bool,
        show_lib: bool,
        show_imported: bool,
        line_style: Option<&str>,
        std_color: bool,
        link_template: Option<String>,
    ) -> PyResult<String> {
        let view = match view {
            "tree" => sysmlv2_viz::View::Tree,
            "interconnection" | "ic" => sysmlv2_viz::View::Interconnection,
            "state" => sysmlv2_viz::View::State,
            "action" => sysmlv2_viz::View::Action,
            "sequence" | "seq" => sysmlv2_viz::View::Sequence,
            "case" => sysmlv2_viz::View::Case,
            "mixed" => sysmlv2_viz::View::Mixed,
            other => {
                return Err(PyValueError::new_err(format!(
                    "unknown view: {other} (expected tree, interconnection, state, action, sequence, case, or mixed)"
                )));
            }
        };
        let line_style = match line_style {
            None => sysmlv2_viz::LineStyle::Default,
            Some("polyline") => sysmlv2_viz::LineStyle::Polyline,
            Some("ortho") => sysmlv2_viz::LineStyle::Ortho,
            Some(other) => {
                return Err(PyValueError::new_err(format!(
                    "unknown line style: {other} (expected polyline or ortho)"
                )));
            }
        };
        let root = match element {
            Some(name) => Some(
                self.inner
                    .resolved()
                    .resolve_qualified(name)
                    .ok_or_else(|| PyValueError::new_err(format!("element not found: {name}")))?,
            ),
            None => None,
        };
        let opts = sysmlv2_viz::VizOptions {
            direction: if horizontal {
                sysmlv2_viz::Direction::LeftToRight
            } else {
                sysmlv2_viz::Direction::TopToBottom
            },
            show_values,
            view,
            show_notes,
            show_metadata,
            show_inherited,
            show_lib,
            show_imported,
            line_style,
            std_color,
            link_template,
            roots: None,
        };
        Ok(sysmlv2_viz::plantuml(self.inner.resolved(), root, &opts))
    }

    fn __repr__(&self) -> String {
        let names: Vec<String> = self.inner.units().map(|(_, n, _)| n.to_string()).collect();
        format!("<Session [{}] gen {}>", names.join(", "), self.gen)
    }
}

/// One `check` finding: the `sysmlv2 check` verdict shape with a 1-based
/// line/column position in its unit's source.
#[pyclass(frozen)]
struct Finding {
    /// `"error"` or `"warning"`.
    #[pyo3(get)]
    severity: String,
    #[pyo3(get)]
    message: String,
    /// Unit name of the source the finding is in (as passed to `check`).
    #[pyo3(get)]
    unit: String,
    #[pyo3(get)]
    line: u32,
    #[pyo3(get)]
    col: u32,
}

#[pymethods]
impl Finding {
    fn __repr__(&self) -> String {
        format!(
            "<Finding {}: {} at {}:{}:{}>",
            self.severity, self.message, self.unit, self.line, self.col
        )
    }
}

/// Check in-memory `(unit name, text)` sources the way `sysmlv2 check`
/// does: per-unit parse and body-context validation always; referential
/// and semantic checks against the standard library when `lib` is given
/// (loaded through the sealed-snapshot cache). Unit names ending in
/// `.kerml` parse as KerML.
///
/// Model problems come back as [`Finding`]s — a broken parse is a
/// finding, not an exception. Exceptions are reserved for operational
/// failures (unreadable library directory).
#[pyfunction]
#[pyo3(signature = (sources, lib = None))]
fn check(sources: Vec<(String, String)>, lib: Option<&str>) -> PyResult<Vec<Finding>> {
    let findings = sysmlv2_transform::check_sources(&sources, lib.map(std::path::Path::new))
        .map_err(runtime)?;
    Ok(findings
        .into_iter()
        .map(|f| Finding {
            severity: match f.severity {
                sysmlv2_transform::Severity::Error => "error".to_string(),
                sysmlv2_transform::Severity::Warning => "warning".to_string(),
            },
            message: f.message,
            unit: f.unit,
            line: f.line,
            col: f.col,
        })
        .collect())
}

/// Push-driven Language Server (`sysmlv2-lsp`): feed one client→server
/// LSP JSON-RPC message (as produced by any LSP client library — e.g.
/// `pygls`, or a hand-rolled `{"jsonrpc": "2.0", ...}` dict dumped to
/// text), get back the server→client messages it produced, each a
/// JSON-RPC string to parse and dispatch. This is the exact same
/// engine `sysmlv2 lsp` serves over stdio and the WASM binding drives
/// from the browser, so completion, semantic tokens (highlighting),
/// document symbols (outline), hover, definition, references, rename,
/// code actions, and diagnostics all come for free — there is nothing
/// here `Session` needs to duplicate.
///
/// Typical use from a Jupyter kernel/server extension: construct one
/// `LspServer` per process (or one per notebook), send `initialize` +
/// `initialized`, then `textDocument/didOpen` a cell's buffer and pull
/// `textDocument/completion` / `textDocument/semanticTokens/full` /
/// `textDocument/documentSymbol` as needed — no subprocess, no stdio
/// pipe, no JSON-RPC framing (`Content-Length` headers): each message
/// is a plain string in, plain strings out.
#[pyclass(unsendable)]
struct LspServer {
    inner: sysmlv2_lsp::PushServer,
}

#[pymethods]
impl LspServer {
    /// The syntax-tier-only server (no standard library): diagnostics,
    /// formatting, outline, and semantic tokens work fully; completion
    /// and navigation see only the open documents' own declarations.
    #[new]
    fn new() -> LspServer {
        LspServer {
            inner: sysmlv2_lsp::PushServer::new(),
        }
    }

    /// A server whose navigation and completions also see a standard
    /// library: `[(unit name, text)]` sources, optionally with a
    /// sealed resolution snapshot (`LibraryCache::to_bytes`) recorded
    /// against the same units — makes library resolution replay
    /// instead of search.
    #[staticmethod]
    #[pyo3(signature = (lib_sources, snapshot = None))]
    fn with_library(lib_sources: Vec<(String, String)>, snapshot: Option<Vec<u8>>) -> LspServer {
        LspServer {
            inner: sysmlv2_lsp::PushServer::with_library_sources(lib_sources, snapshot),
        }
    }

    /// Seed (or replace) the navigation workspace: every model unit the
    /// host knows about, as `[(uri string, text)]` — the same uri
    /// strings documents are opened under. Open-document texts overlay
    /// these, so definition/references/hover/completion cross into
    /// units that are not open. Returns server→client messages the
    /// re-seed produced (refresh requests for clients that support
    /// them) — relay them exactly like `handle`'s output.
    fn set_workspace(&mut self, units: Vec<(String, String)>) -> PyResult<Vec<String>> {
        self.inner.set_workspace_sources(units);
        self.inner.take_outbound().map_err(runtime)
    }

    /// Handle one JSON-RPC message string (a request or a
    /// notification); returns the server→client messages it produced,
    /// in order, each a JSON-RPC string. The first message of a
    /// session must be an `initialize` request.
    fn handle(&mut self, msg: &str) -> PyResult<Vec<String>> {
        self.inner.handle(msg).map_err(runtime)
    }

    /// Drop cached navigation sessions after a host-side engine
    /// reconfiguration (e.g. `set_unit_spelling_expansion`) that
    /// changes answers without any source changing. Returns the
    /// refresh requests to relay, like `set_workspace`.
    fn invalidate_sessions(&mut self) -> PyResult<Vec<String>> {
        self.inner.invalidate_sessions();
        self.inner.take_outbound().map_err(runtime)
    }

    /// Set whether evaluated-value inlay hints that restate the
    /// declared expression verbatim are suppressed (default on).
    /// Returns the refresh requests to relay, like `set_workspace`.
    fn set_hide_redundant_value_hints(&mut self, on: bool) -> PyResult<Vec<String>> {
        self.inner.set_hide_redundant_value_hints(on);
        self.inner.take_outbound().map_err(runtime)
    }

    /// Set whether accepting a unit completion inside an untyped
    /// attribute's quantity bracket also declares the type the unit
    /// determines (default on). Takes effect on the next completion
    /// request.
    fn set_infer_unit_types(&mut self, on: bool) {
        self.inner.set_infer_unit_types(on);
    }
}

/// Enable or disable expanding quoted power-product unit spellings
/// (`'m³⋅s⁻²'` parsed into `m³/s²` when the unit element carries no
/// definition or conversion of its own). On by default; process-wide.
#[pyfunction]
fn set_unit_spelling_expansion(on: bool) {
    sysmlv2_model::eval::set_unit_spelling_expansion(on);
}

/// SysML v2 / KerML toolkit: sessions over textual models or interchange
/// JSON, KerML-expression queries, and verified span-splice
/// transformations.
#[pymodule]
fn sysmlv2(m: &Bound<'_, PyModule>) -> PyResult<()> {
    m.add("__version__", env!("CARGO_PKG_VERSION"))?;
    m.add_class::<Session>()?;
    m.add_class::<Element>()?;
    m.add_class::<Reference>()?;
    m.add_class::<EditBatch>()?;
    m.add_class::<CommitReport>()?;
    m.add_class::<Finding>()?;
    m.add_class::<LspServer>()?;
    m.add_function(wrap_pyfunction!(check, m)?)?;
    m.add_function(wrap_pyfunction!(set_unit_spelling_expansion, m)?)?;
    Ok(())
}
