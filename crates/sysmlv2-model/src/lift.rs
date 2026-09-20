//! JSON reader: lift interchange JSON back into the syntax AST.
//!
//! The inverse of `json.rs`'s lowering. Accepts the compact form directly;
//! full-form input is normalized on the fly (relationships flagged
//! `isImplied: true` are skipped, derived properties are ignored — the lift
//! only reads owned properties).
//!
//! References come back as names: `{"@ref": "…"}` strings verbatim, and
//! `{"@id": …}` references as the target's root-qualified name (computed
//! from the ownership tree). IDs pointing outside the document resolve via
//! the optional extra-names table (see
//! [`crate::json::library_name_map`]) or are reported as errors.
//!
//! Round-trip invariant (gated over the corpus by `tests/roundtrip.rs`):
//! `emit(parse(print(lift(j)))) == j` for compact `j` emitted by this crate.

use serde_json::{Map, Value};
use std::collections::{HashMap, HashSet};
use sysmlv2_syntax::ast::*;
use sysmlv2_syntax::span::Span;

type El<'a> = &'a Map<String, Value>;

/// Result of lifting: the unit plus non-fatal problems (unknown constructs,
/// unresolvable references).
pub struct Lifted {
    pub unit: SourceUnit,
    pub errors: Vec<String>,
}

/// Why a payload could not be lifted at all. A problem inside an
/// otherwise well-formed payload may be reported in [`Lifted::errors`],
/// but a cycle or exhausted depth budget refuses the document: returning
/// a partial expression could change its value while still printing as
/// valid source.
///
/// Non-exhaustive: a payload shape the lift cannot start on may be
/// recognised later, and naming one is not a breaking change.
#[derive(Clone, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub enum LiftError {
    /// The payload is not the flat array of elements KerML 10.4.6
    /// describes.
    NotAnElementArray,
    /// An entry of the array is not a JSON object.
    NotAnElement,
    /// An element carries no `@id`, so nothing can point at it.
    ElementWithoutId,
    /// Following the ownership graph would lose a subtree or operand.
    Incomplete { errors: Vec<String> },
}

impl std::fmt::Display for LiftError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            LiftError::NotAnElementArray => {
                f.write_str("expected a flat JSON array of elements (KerML 10.4.6)")
            }
            LiftError::NotAnElement => f.write_str("expected every element to be a JSON object"),
            LiftError::ElementWithoutId => f.write_str("element without @id"),
            LiftError::Incomplete { errors } => {
                write!(
                    f,
                    "cannot lift the document without data loss: {}",
                    errors.join("; ")
                )
            }
        }
    }
}

impl std::error::Error for LiftError {}

impl From<LiftError> for String {
    fn from(error: LiftError) -> String {
        error.to_string()
    }
}

/// Lift a compact-JSON element array into a syntax AST.
pub fn from_compact_json(value: &Value) -> Result<Lifted, LiftError> {
    from_compact_json_with_names(value, &HashMap::new())
}

/// Qualified-name map over a whole element list: element `@id` → name
/// segments, built by walking the ownership closure from each root
/// namespace and collecting `declaredName`s. Feed it to
/// [`from_compact_json_with_names`] when lifting one document of a
/// multi-document list, so cross-document references print as
/// `$::`-rooted qualified names instead of unresolvable ids (the same
/// mechanism [`crate::json::library_name_map`] provides for standard-
/// library ids).
pub fn document_name_map(value: &Value) -> std::collections::HashMap<String, Vec<String>> {
    let mut out = std::collections::HashMap::new();
    let Some(elements) = value.as_array() else {
        return out;
    };
    let by_id: std::collections::HashMap<&str, usize> = elements
        .iter()
        .enumerate()
        .filter_map(|(i, e)| e.get("@id").and_then(|v| v.as_str()).map(|id| (id, i)))
        .collect();
    // Anonymous features are findable by their *effective* name (KerML
    // 8.2.3.5 — redefinition / reference-subsetting derived): a
    // whole-list Lifter supplies it exactly as an in-document lift
    // would, so a cross-document reference to an anonymous redefining
    // feature (a chain landing on `attribute :>> x = …;` in another
    // document) names the redefined feature instead of failing.
    let lifter_by_id: HashMap<&str, El> = elements
        .iter()
        .filter_map(|e| match e {
            Value::Object(m) => m.get("@id").and_then(|v| v.as_str()).map(|id| (id, m)),
            _ => None,
        })
        .collect();
    let no_extra_names = HashMap::new();
    let lifter = Lifter {
        by_id: lifter_by_id,
        unresolved_names: HashMap::new(),
        extra_names: &no_extra_names,
        qnames: HashMap::new(),
        dialect: Dialect::Sysml,
        next_featuring: true,
        body_featuring: false,
        errors: Vec::new(),
        reported: HashSet::new(),
        depth_reported: HashSet::new(),
        in_progress: HashSet::new(),
        depth: 0,
        incomplete: false,
    };
    let is_root = |e: &Value| {
        e.get("@type").and_then(|v| v.as_str()) == Some("Namespace")
            && e.get("owningRelationship")
                .is_none_or(|v| v.is_null() || v.as_str() == Some(""))
    };
    let mut seen = vec![false; elements.len()];
    // The bool marks nodes an unnamed occurrence may pass the parent
    // path through: relationship levels (memberships, feature values,
    // typings — reached via `ownedRelationship`) are unnamed wrappers
    // their members legitimately skip, and root namespaces carry the
    // (empty) document path. An unnamed *element* with no effective
    // name (an anonymous lambda body Expression, an unnameable
    // feature) breaks global reachability instead: its subtree records
    // no entries at all — mirroring the in-document `qname_of`, which
    // refuses a path through an unnameable ancestor — so references
    // into it fall back to relative suffix spellings that resolve at
    // the reference site (a lambda-local `in s` prints as `s`, never
    // as a collapsed `$::…::s` that skips the anonymous level).
    let mut stack: Vec<(usize, Vec<String>, bool)> = (0..elements.len())
        .filter(|&i| is_root(&elements[i]))
        .map(|i| (i, Vec::new(), true))
        .collect();
    while let Some((i, path, passthrough)) = stack.pop() {
        if seen[i] {
            continue;
        }
        seen[i] = true;
        let e = &elements[i];
        let effective = |e: &Value| match e {
            Value::Object(m) => lifter.effective_name(m, 0),
            _ => None,
        };
        let path = match e
            .get("declaredName")
            .and_then(|v| v.as_str())
            .map(str::to_owned)
            .or_else(|| effective(e))
        {
            Some(name) => {
                let mut p = path.clone();
                p.push(name);
                if let Some(id) = e.get("@id").and_then(|v| v.as_str()) {
                    out.insert(id.to_string(), p.clone());
                }
                p
            }
            None if passthrough => path,
            // Unnameable element: no global path reaches its subtree.
            None => continue,
        };
        for key in ["ownedRelationship", "ownedRelatedElement", "ownedElement"] {
            let Some(v) = e.get(key) else { continue };
            let refs: Vec<&Value> = match v {
                Value::Array(a) => a.iter().collect(),
                other => vec![other],
            };
            for r in refs {
                if let Some(id) = r.get("@id").and_then(|x| x.as_str()) {
                    if let Some(&j) = by_id.get(id) {
                        stack.push((j, path.clone(), key == "ownedRelationship"));
                    }
                }
            }
        }
    }
    out
}

/// [`document_name_map`] extended for *reference* naming: memberships
/// are unnamed, so the element walk never maps them — but membership
/// imports reference memberships directly, and a cross-document one
/// must still print its member's name. This map adds each membership
/// id → its member's path (`memberElement` where the payload carries
/// it, else the owned member itself). Use it as `extra_names` when
/// lifting; keep [`document_name_map`] where entries must be
/// *elements* (id-identity comparisons).
pub fn document_reference_name_map(
    value: &Value,
) -> std::collections::HashMap<String, Vec<String>> {
    let mut out = document_name_map(value);
    let Some(elements) = value.as_array() else {
        return out;
    };
    for e in elements {
        let t = e.get("@type").and_then(|v| v.as_str()).unwrap_or("");
        let Some(id) = e.get("@id").and_then(|v| v.as_str()) else {
            continue;
        };
        if !t.ends_with("Membership") || out.contains_key(id) {
            continue;
        }
        let member = e
            .get("memberElement")
            .and_then(|m| m.get("@id"))
            .and_then(|v| v.as_str())
            .or_else(|| {
                let owned = e.get("ownedRelatedElement")?;
                let first = match owned {
                    Value::Array(a) => a.first()?,
                    other => other,
                };
                first.get("@id").and_then(|v| v.as_str())
            });
        if let Some(path) = member.and_then(|mid| out.get(mid).cloned()) {
            out.insert(id.to_string(), path);
        }
    }
    out
}

/// Split a multi-document element list into per-root-namespace chunks.
///
/// Interchange JSON holds one root `Namespace` element per document (an
/// element of `@type` `Namespace` with no `owningRelationship`); every
/// other element is reachable from exactly one root through the ownership
/// closure (`ownedRelationship` on elements, `ownedRelatedElement` on
/// relationships). Returns one `(root_name, elements)` pair per root in
/// input order — `root_name` is the root's `qualifiedName`/`declaredName`
/// when present (the interchange convention stores the source file name
/// there). `None` when the input has no root namespaces or when any
/// element is unreachable from every root (callers then treat the input
/// as one document).
///
/// # Panics
///
/// Never: every element is assigned to a document before the split
/// begins, and a payload with an unassignable element returns `None`
/// rather than reaching the split.
pub fn split_documents(value: &Value) -> Option<Vec<(Option<String>, Value)>> {
    let elements = value.as_array()?;
    let id_of = |e: &Value| e.get("@id").and_then(|v| v.as_str()).map(str::to_owned);
    let by_id: std::collections::HashMap<String, usize> = elements
        .iter()
        .enumerate()
        .filter_map(|(i, e)| id_of(e).map(|id| (id, i)))
        .collect();
    let is_root = |e: &Value| {
        e.get("@type").and_then(|v| v.as_str()) == Some("Namespace")
            && e.get("owningRelationship")
                .is_none_or(|v| v.is_null() || v.as_str() == Some(""))
    };
    let roots: Vec<usize> = (0..elements.len())
        .filter(|&i| is_root(&elements[i]))
        .collect();
    if roots.len() < 2 {
        return None;
    }

    // Ownership edges: any `@id` object inside ownedRelationship /
    // ownedRelatedElement / ownedElement (full form carries the latter).
    let mut assigned: Vec<Option<usize>> = vec![None; elements.len()];
    for (doc, &root) in roots.iter().enumerate() {
        let mut stack = vec![root];
        while let Some(i) = stack.pop() {
            if assigned[i].is_some() {
                continue;
            }
            assigned[i] = Some(doc);
            for key in ["ownedRelationship", "ownedRelatedElement", "ownedElement"] {
                let Some(v) = elements[i].get(key) else {
                    continue;
                };
                let refs: Vec<&Value> = match v {
                    Value::Array(a) => a.iter().collect(),
                    other => vec![other],
                };
                for r in refs {
                    if let Some(id) = r.get("@id").and_then(|x| x.as_str()) {
                        if let Some(&j) = by_id.get(id) {
                            stack.push(j);
                        }
                    }
                }
            }
        }
    }
    if assigned.iter().any(|a| a.is_none()) {
        return None;
    }

    let name_of = |e: &Value| {
        e.get("qualifiedName")
            .or_else(|| e.get("declaredName"))
            .and_then(|v| v.as_str())
            .map(str::to_owned)
    };
    let mut docs: Vec<(Option<String>, Vec<Value>)> = roots
        .iter()
        .map(|&r| (name_of(&elements[r]), Vec::new()))
        .collect();
    for (i, e) in elements.iter().enumerate() {
        let doc = assigned[i].expect("checked above");
        docs[doc].1.push(e.clone());
    }
    Some(
        docs.into_iter()
            .map(|(name, els)| (name, Value::Array(els)))
            .collect(),
    )
}

/// Like [`from_compact_json`], with an extra `id → qualified-name segments`
/// table for references that point outside the document (e.g. the standard
/// library when the JSON was emitted with library resolution).
pub fn from_compact_json_with_names(
    value: &Value,
    extra_names: &HashMap<String, Vec<String>>,
) -> Result<Lifted, LiftError> {
    // The lift recurses once per membership and owned definition or
    // usage (expressions use a work stack), so its stack need is set by
    // [`MAX_LIFT_DEPTH`] rather than by whichever thread called it (a
    // language-server worker, a test thread), and it gets a thread of its
    // own to carry that need.
    //
    // Only a payload that nests deeply enough to want one takes it:
    // spawning costs several times what lifting a small document does,
    // and anything lifting many documents would pay that per document.
    // Depth decides it rather than size, because it is depth the stack
    // answers for — and a payload that does nest deeply is never the
    // small one the spawn would dominate.
    //
    // A target without threads, or a host that refuses one, lifts in
    // place; the depth guard applies either way.
    #[cfg(not(target_family = "wasm"))]
    if value
        .as_array()
        .is_some_and(|items| nests_deeper_than(items, IN_PLACE_DEPTH))
    {
        let spawned = std::thread::scope(|scope| {
            std::thread::Builder::new()
                .name("sysmlv2-lift".into())
                .stack_size(LIFT_STACK_BYTES)
                .spawn_scoped(scope, || lift_document(value, extra_names))
                .map(std::thread::ScopedJoinHandle::join)
        });
        match spawned {
            Ok(Ok(lifted)) => return lifted,
            Ok(Err(panic)) => std::panic::resume_unwind(panic),
            Err(_) => {}
        }
    }
    lift_document(value, extra_names)
}

/// [`from_compact_json_with_names`] without moving the lift onto a stack
/// of its own: what a target without threads does, and what a caller
/// already holding a stack sized for [`MAX_LIFT_DEPTH`] steps can ask
/// for. The depth guard applies here too — this is the same lift, on the
/// calling thread.
pub fn from_compact_json_on_this_stack(
    value: &Value,
    extra_names: &HashMap<String, Vec<String>>,
) -> Result<Lifted, LiftError> {
    lift_document(value, extra_names)
}

fn lift_document(
    value: &Value,
    extra_names: &HashMap<String, Vec<String>>,
) -> Result<Lifted, LiftError> {
    let Value::Array(items) = value else {
        return Err(LiftError::NotAnElementArray);
    };
    let mut by_id: HashMap<&str, El> = HashMap::new();
    let mut order: Vec<&str> = Vec::new();
    for item in items {
        let Value::Object(el) = item else {
            return Err(LiftError::NotAnElement);
        };
        let Some(id) = el.get("@id").and_then(|v| v.as_str()) else {
            return Err(LiftError::ElementWithoutId);
        };
        by_id.insert(id, el);
        order.push(id);
    }
    // Unresolved-reference recovery annotations: dangling id → spelling.
    let mut unresolved_names = HashMap::new();
    for el in by_id.values() {
        if ty(el) == "TextualRepresentation"
            && sval(el, "language") == Some(crate::full::UNRESOLVED_REP_LANGUAGE)
        {
            if let Some(body) = sval(el, "body") {
                let dangling = uuid::Uuid::new_v5(
                    &uuid::Uuid::NAMESPACE_OID,
                    format!("unresolved:{body}").as_bytes(),
                )
                .to_string();
                unresolved_names.insert(dangling, body.to_string());
            }
        }
    }
    let mut lifter = Lifter {
        by_id,
        unresolved_names,
        extra_names,
        qnames: HashMap::new(),
        dialect: Dialect::Sysml,
        next_featuring: true,
        body_featuring: false,
        errors: Vec::new(),
        reported: HashSet::new(),
        depth_reported: HashSet::new(),
        in_progress: HashSet::new(),
        depth: 0,
        incomplete: false,
    };
    lifter.dialect = lifter.detect_dialect();
    lifter.compute_qnames(&order);

    // Roots: elements with no *in-document* owner — not owned by a
    // relationship (`owningRelationship`) and not a relationship owned by
    // an element (`owningRelatedElement`). An owner reference naming an id
    // the document does not carry counts as unowned: ownership-closure
    // slices (element-scoped exports, API query results) arrive without
    // their enclosing root namespace, and their outermost elements must
    // still lift — as roots — rather than vanish behind the dangling
    // reference. A dangling member *relationship* (its owning namespace
    // outside the document) contributes its member the way it would under
    // that namespace.
    let in_doc = |lifter: &Lifter<'_>, el: El, key: &str| {
        el.get(key)
            .and_then(ref_id)
            .is_some_and(|id| lifter.by_id.contains_key(id))
    };
    let mut members = Vec::new();
    for id in &order {
        let el = lifter.by_id[id];
        let unowned = !in_doc(&lifter, el, "owningRelationship")
            && !in_doc(&lifter, el, "owningRelatedElement");
        if unowned {
            let t = ty(el);
            if t == "Namespace" {
                let rels = lifter.owned_rels(el);
                members.extend(lifter.lift_members(&rels));
            } else if t.ends_with("Membership") || t.ends_with("Import") || t.ends_with("Expose") {
                // Implied relationships are re-derived, never lifted —
                // same rule `owned_rels` applies in-document.
                if !bval(el, "isImplied") {
                    if let Some(m) = lifter.lift_member(el) {
                        members.push(m);
                    }
                }
            } else if let Some(m) = lifter.lift_owning_member_element(el, None, false) {
                members.push(m);
            }
        }
    }
    if lifter.incomplete {
        return Err(LiftError::Incomplete {
            errors: lifter.errors,
        });
    }
    Ok(Lifted {
        unit: SourceUnit {
            dialect: lifter.dialect,
            members,
        },
        errors: lifter.errors,
    })
}

fn ty<'a>(el: El<'a>) -> &'a str {
    el.get("@type").and_then(|v| v.as_str()).unwrap_or("")
}

fn id_of<'a>(el: El<'a>) -> &'a str {
    el.get("@id").and_then(|v| v.as_str()).unwrap_or("")
}

fn sval<'a>(el: El<'a>, key: &str) -> Option<&'a str> {
    el.get(key).and_then(|v| v.as_str())
}

fn bval(el: El, key: &str) -> bool {
    el.get(key).and_then(|v| v.as_bool()).unwrap_or(false)
}

fn ref_id(v: &Value) -> Option<&str> {
    v.get("@id").and_then(|x| x.as_str())
}

fn name(value: &str) -> Name {
    Name {
        value: value.to_string(),
        span: Span::default(),
    }
}

fn qn_from_segments(segments: &[String]) -> QualifiedName {
    QualifiedName {
        is_global: false,
        segments: segments.iter().map(|s| name(s)).collect(),
        span: Span::default(),
    }
}

/// Root-qualified name from an ownership path: printed with `$::` so it
/// cannot be shadowed by local members at the reference site.
fn qn_global(segments: &[String]) -> QualifiedName {
    QualifiedName {
        is_global: true,
        ..qn_from_segments(segments)
    }
}

/// One resolved-or-not link of an owned feature chain.
enum ChainLink<'a> {
    /// Unresolved link: its written (last-segment) name.
    Ref(String),
    /// Resolved link: the target element id.
    Id(&'a str),
}

/// Parse an `@ref` string back into a target (dotted → feature chain).
/// Inverse of [`QualifiedName::to_ref_string`]: honors `'…'` quoting with
/// backslash escapes, so restricted names containing `.` or `::` (e.g. the
/// range function `'..'`) survive the trip.
fn target_from_ref_string(s: &str) -> TargetRef {
    let mut links: Vec<QualifiedName> = Vec::new();
    // Each decoded segment remembers whether it was quoted: only a *bare*
    // leading `$` is the global-root marker — a name literally `$` is
    // always emitted quoted (`'$'`) by `escape_name`.
    let mut segments: Vec<(String, bool)> = Vec::new();
    let mut cur = String::new();
    let mut quoted = false;
    let mut chars = s.chars().peekable();
    while let Some(c) = chars.next() {
        match c {
            '\'' => {
                quoted = true;
                // Quoted restricted name; unescape mirroring `escape_name`.
                while let Some(c) = chars.next() {
                    match c {
                        '\\' => {
                            if let Some(e) = chars.next() {
                                cur.push(match e {
                                    'b' => '\u{0008}',
                                    't' => '\t',
                                    'n' => '\n',
                                    'f' => '\u{000C}',
                                    'r' => '\r',
                                    other => other,
                                });
                            }
                        }
                        '\'' => break,
                        c => cur.push(c),
                    }
                }
            }
            ':' if chars.peek() == Some(&':') => {
                chars.next();
                segments.push((std::mem::take(&mut cur), std::mem::take(&mut quoted)));
            }
            '.' => {
                segments.push((std::mem::take(&mut cur), std::mem::take(&mut quoted)));
                let segs = std::mem::take(&mut segments);
                links.push(ref_segments_to_qn(&segs));
            }
            c => cur.push(c),
        }
    }
    segments.push((cur, quoted));
    let last = ref_segments_to_qn(&segments);
    if links.is_empty() {
        TargetRef::Name(last)
    } else {
        links.push(last);
        TargetRef::Chain(links)
    }
}

/// Build a qualified name from decoded `@ref` segments, honoring a leading
/// *bare* `$` (global-root) marker — quoted `'$'` is an ordinary name.
fn ref_segments_to_qn(segments: &[(String, bool)]) -> QualifiedName {
    let strings = |segs: &[(String, bool)]| segs.iter().map(|(s, _)| s.clone()).collect::<Vec<_>>();
    match segments.first() {
        Some((s, false)) if s == "$" => qn_global(&strings(&segments[1..])),
        _ => qn_from_segments(&strings(segments)),
    }
}

/// Metaclasses the expression lifter understands.
fn is_expr_type(t: &str) -> bool {
    matches!(
        t,
        "LiteralBoolean"
            | "LiteralString"
            | "LiteralInteger"
            | "LiteralRational"
            | "LiteralInfinity"
            | "NullExpression"
            | "FeatureReferenceExpression"
            | "MetadataAccessExpression"
            | "FeatureChainExpression"
            | "IndexExpression"
            | "CollectExpression"
            | "SelectExpression"
            | "InvocationExpression"
            | "ConstructorExpression"
            | "OperatorExpression"
            | "Expression"
    )
}

const KERML_MARKERS: &[&str] = &[
    "Classifier",
    "Class",
    "Structure",
    "DataType",
    "Association",
    "AssociationStructure",
    "Behavior",
    "Interaction",
    "Function",
    "Predicate",
    "Metaclass",
    "Step",
    "Invariant",
    "BooleanExpression",
    "BindingConnector",
    "Connector",
    "MetadataFeature",
];

/// The most lift steps one ownership path may take: a step is a
/// membership or the package, definition or usage it owns. Expressions
/// use an iterative walk with a separate bound. Ownership pointers come from the payload, so a
/// chain that loops back on itself or nests without bound must end in an
/// error rather than exhaust the stack. A nesting level of written
/// notation costs two steps (its membership and the member). The parser
/// can accept a leaf member inside its deepest body, hence the extra pair.
pub const MAX_LIFT_DEPTH: usize = 2 * (sysmlv2_syntax::parser::MAX_NESTING as usize + 1);

/// Expressions are walked without recursive stack frames, but their AST
/// consumers still need a bound. Match the parser's operator budget plus
/// its leaf operand; expression bodies retain the structural budget.
pub const MAX_LIFT_EXPR_DEPTH: usize = sysmlv2_syntax::parser::MAX_EXPR_OPERATORS as usize + 1;

/// Stack reserved for the lift thread: enough for [`MAX_LIFT_DEPTH`]
/// steps in an unoptimized build, where one step costs up to about
/// 190 KiB (an optimized build needs a twentieth of that). Reserved
/// address space only — pages are committed as the recursion touches
/// them.
#[cfg(not(target_family = "wasm"))]
const LIFT_STACK_BYTES: usize = 128 << 20;

/// The deepest payload lifted on the caller's own stack.
///
/// Measured against the two megabytes a thread gets when it asks for
/// none, in an unoptimized build, where a step is at its most
/// expensive. That is the smallest stack a caller can be on: one that
/// parses has already reserved a larger one for the parser's own bound
/// (`sysmlv2_syntax::parser::MAX_NESTING_STACK_BYTES`), and a caller
/// that only lifts need not have. Past this the payload could nest
/// toward [`MAX_LIFT_DEPTH`], which needs a stack sized for it; a
/// nesting level of written notation costs two steps, so this is eight
/// levels of braces.
#[cfg(not(target_family = "wasm"))]
const IN_PLACE_DEPTH: usize = 16;

/// Whether the payload's ownership pointers reach more than `limit` steps
/// below a root — the question [`from_compact_json_with_names`] decides
/// by, answered in one pass without recursing and without lifting
/// anything.
///
/// A payload whose ownership is not a forest — an element owned twice, a
/// cycle, an element with no `@id` — counts as deep: the lift's own
/// guards handle those, and a stack sized for the bound is what they need
/// to reach.
#[cfg(not(target_family = "wasm"))]
fn nests_deeper_than(items: &[Value], limit: usize) -> bool {
    // A step enters an element no step on the path has entered, so a
    // payload of at most `limit` elements cannot nest past `limit`. This
    // is the common case and it costs nothing to answer.
    if items.len() <= limit {
        return false;
    }
    fn owned_ids(el: &Value) -> impl Iterator<Item = &str> {
        ["ownedRelationship", "ownedRelatedElement"]
            .into_iter()
            .filter_map(|key| el.get(key))
            .filter_map(Value::as_array)
            .flatten()
            .filter_map(|child| child.get("@id").and_then(Value::as_str))
    }
    let mut by_id: HashMap<&str, &Value> = HashMap::with_capacity(items.len());
    for item in items {
        let Some(id) = item.get("@id").and_then(Value::as_str) else {
            return true;
        };
        if by_id.insert(id, item).is_some() {
            return true;
        }
    }
    let mut owned: HashSet<&str> = HashSet::new();
    for item in items {
        for child in owned_ids(item) {
            if by_id.contains_key(child) && !owned.insert(child) {
                return true;
            }
        }
    }
    let mut level: Vec<&str> = by_id
        .keys()
        .copied()
        .filter(|id| !owned.contains(id))
        .collect();
    let mut seen: HashSet<&str> = level.iter().copied().collect();
    let mut depth = 0usize;
    while !level.is_empty() {
        depth += 1;
        if depth > limit {
            return true;
        }
        let mut next = Vec::new();
        for id in level {
            for child in owned_ids(by_id[id]) {
                if by_id.contains_key(child) && seen.insert(child) {
                    next.push(child);
                }
            }
        }
        level = next;
    }
    // Whatever no root reaches sits in a cycle.
    seen.len() != by_id.len()
}

struct Lifter<'a> {
    by_id: HashMap<&'a str, El<'a>>,
    /// Dangling id → source spelling, from unresolved-reference recovery
    /// annotations (`TextualRepresentation` with
    /// [`crate::full::UNRESOLVED_REP_LANGUAGE`]) — see `crate::full`.
    unresolved_names: HashMap<String, String>,
    extra_names: &'a HashMap<String, Vec<String>>,
    /// Element id → root-qualified name segments (None while/if unnameable).
    qnames: HashMap<&'a str, Option<Vec<String>>>,
    dialect: Dialect,
    /// Featuring flag for the next `lift_usage` call (pilot
    /// `UsageUtil.hasFeaturingType`): consumed at entry, defaulting back to
    /// true. Only namespace-owned members and variants override it.
    next_featuring: bool,
    /// Featuring flag of the usage whose body members are being lifted —
    /// a variant member inherits its variation's featuring.
    body_featuring: bool,
    errors: Vec<String>,
    /// The messages already in `errors`, so one condition met again and
    /// again over a payload is recorded once. The list is read by a
    /// person; its length should follow the payload's problems, not its
    /// size.
    reported: HashSet<String>,
    /// Roots of the subtrees already reported as truncated. Reaching the
    /// bound truncates the subtree under the element the step was about to
    /// enter; a later walk reaching the bound below one of these roots
    /// truncates the same subtree again and is not reported twice, so the
    /// list follows the number of subtrees the payload loses rather than
    /// the number of elements in them — while a payload losing two
    /// subtrees with nothing in common still says so twice.
    depth_reported: HashSet<&'a str>,
    /// Ids of the memberships, usages, definitions and expression
    /// elements on the current lift path — re-entering one means the
    /// payload's ownership pointers form a cycle.
    in_progress: HashSet<&'a str>,
    /// Lift steps on the current path (see [`MAX_LIFT_DEPTH`]).
    depth: usize,
    /// A structural failure must not escape as a successful partial AST.
    incomplete: bool,
}

impl<'a> Lifter<'a> {
    /// Record `message`, unless the same message is recorded already.
    fn record(&mut self, message: String) {
        if self.reported.insert(message.clone()) {
            self.errors.push(message);
        }
    }

    /// Take one lift step into `id`. `None` — with an error recorded —
    /// when the payload's ownership pointers loop back to an element
    /// already being lifted or nest past [`MAX_LIFT_DEPTH`]; the caller
    /// skips that subtree, diagnoses siblings, then refuses the document.
    fn enter(&mut self, id: &'a str) -> Option<()> {
        if self.depth >= MAX_LIFT_DEPTH {
            self.incomplete = true;
            // A walk that starts lower down the same chain reaches the
            // bound again a little further along it and truncates inside a
            // subtree already reported, which says nothing new; a payload
            // that loses two subtrees with nothing in common says so
            // twice.
            let inside_reported = self
                .depth_reported
                .iter()
                .any(|root| self.in_progress.contains(root));
            if !inside_reported && self.depth_reported.insert(id) {
                self.record(format!(
                    "ownership nesting deeper than {MAX_LIFT_DEPTH} at {id}"
                ));
            }
            return None;
        }
        if !self.in_progress.insert(id) {
            self.incomplete = true;
            self.record(format!("ownership cycle through {id}"));
            return None;
        }
        self.depth += 1;
        Some(())
    }

    fn leave(&mut self, id: &'a str) {
        self.in_progress.remove(id);
        self.depth -= 1;
    }

    fn detect_dialect(&self) -> Dialect {
        for el in self.by_id.values() {
            if KERML_MARKERS.contains(&ty(el)) {
                return Dialect::Kerml;
            }
        }
        Dialect::Sysml
    }

    fn owner_of(&self, el: El<'a>) -> Option<El<'a>> {
        let rel_id = el.get("owningRelationship").and_then(ref_id)?;
        let rel = self.by_id.get(rel_id)?;
        let owner_id = rel.get("owningRelatedElement").and_then(ref_id)?;
        self.by_id.get(owner_id).copied()
    }

    /// An element's declared (short) name, for anonymity tests.
    fn declared_name<'b>(el: El<'b>) -> Option<&'b str> {
        sval(el, "declaredName").or_else(|| sval(el, "declaredShortName"))
    }

    /// The findable (last-segment) name of an out-of-document id: a
    /// library element (`extra_names`) or a dangling patched `@ref`
    /// carrying a recovery annotation (`unresolved_names`).
    fn out_of_doc_name(&self, id: &str) -> Option<String> {
        if let Some(segs) = self.extra_names.get(id) {
            return segs.last().cloned();
        }
        match target_from_ref_string(self.unresolved_names.get(id)?) {
            TargetRef::Name(qn) => qn.segments.last().map(|n| n.value.clone()),
            TargetRef::Chain(links) => links
                .last()
                .and_then(|l| l.segments.last())
                .map(|n| n.value.clone()),
        }
    }

    /// The name an element is findable by: its declared (short) name, or —
    /// for unnamed features — the effective name taken from the first
    /// referenced or redefined feature (KerML 8.2.3.5 / SysML reference
    /// forms), mirroring the emitter's scope registration.
    ///
    /// One naming rule, four representations — an element is named by
    /// its declaration, else by its *naming feature*: the first feature
    /// it redefines, else the one it references, else the last link of
    /// its chain, each followed transitively. The implementations are
    /// this one (over payload JSON), `json::Builder::graph_effective_name`
    /// (over the lowered element graph, where `Builder::effective_name`
    /// is the declaration-only half), `full::effective_name_of` (over the
    /// full form's element maps, which also derives the positional
    /// implied names), and the fixpoint inside `ids::walk` (over a
    /// compact payload, for id segments). They agree by construction and
    /// by the differential test in the round-trip gate; a change to one
    /// belongs in all of them.
    fn effective_name(&self, el: El<'a>, depth: usize) -> Option<String> {
        // A binary connector-family end is findable only as `source`/
        // `target` (its implied redefinition of the BinaryConnection ends —
        // the emitter's `implied_ends` registration); positional naming
        // wins even over a declared end name, which is never registered.
        if let Some(n) = self.implied_end_name(el) {
            return Some(n.to_string());
        }
        if let Some(n) = sval(el, "declaredName").or_else(|| sval(el, "declaredShortName")) {
            return Some(n.to_string());
        }
        if depth > 8 {
            return None;
        }
        for rel in self.owned_rels(el) {
            let key = match ty(rel) {
                "ReferenceSubsetting" => "referencedFeature",
                "Redefinition" => "redefinedFeature",
                _ => continue,
            };
            let Some(v) = rel.get(key) else { break };
            if let Some(s) = v.get("@ref").and_then(|x| x.as_str()) {
                return match target_from_ref_string(s) {
                    TargetRef::Name(qn) => qn.segments.last().map(|n| n.value.clone()),
                    TargetRef::Chain(links) => links
                        .last()
                        .and_then(|l| l.segments.last())
                        .map(|n| n.value.clone()),
                };
            }
            if let Some(id) = ref_id(v) {
                if let Some(&target) = self.by_id.get(id) {
                    // A chained target (owned chain Feature) takes its name
                    // from the last link, mirroring the emitter.
                    if let Some(last) = self.last_chaining_target(target) {
                        return match last {
                            ChainLink::Ref(name) => Some(name),
                            ChainLink::Id(link_id) => match self.by_id.get(link_id) {
                                Some(&el) => self.effective_name(el, depth + 1),
                                None => self.out_of_doc_name(link_id),
                            },
                        };
                    }
                    return self.effective_name(target, depth + 1);
                }
                // Out-of-document target: the last segment is the
                // findable name.
                return self.out_of_doc_name(id);
            }
            // Only the first reference/redefinition provides the name.
            break;
        }
        None
    }

    /// The implied positional name of a binary connector-family end: the two
    /// bare ends of a `connect a to b` (ConnectionUsage / InterfaceUsage /
    /// AllocationUsage / KerML Connector) implicitly redefine the
    /// BinaryConnection ends and are findable only as `source`/`target` —
    /// mirroring the emitter's `implied_ends` registration exactly (same
    /// bare-end test, same exactly-two rule, bare-end order).
    fn implied_end_name(&self, el: El<'a>) -> Option<&'static str> {
        let rel_id = el.get("owningRelationship").and_then(ref_id)?;
        if ty(self.by_id.get(rel_id)?) != "EndFeatureMembership" {
            return None;
        }
        let owner = self.owner_of(el)?;
        if !matches!(
            ty(owner),
            "ConnectionUsage" | "InterfaceUsage" | "AllocationUsage" | "Connector"
        ) {
            return None;
        }
        let bare: Vec<El<'a>> = self
            .owned_rels(owner)
            .into_iter()
            .filter(|r| ty(r) == "EndFeatureMembership" && self.is_bare_end(r))
            .collect();
        match bare.as_slice() {
            [first, _] if id_of(first) == rel_id => Some("source"),
            [_, second] if id_of(second) == rel_id => Some("target"),
            _ => None,
        }
    }

    /// The last `FeatureChaining` link of an owned chain Feature, if `el`
    /// is one.
    fn last_chaining_target(&self, el: El<'a>) -> Option<ChainLink<'a>> {
        let last = self
            .owned_rels(el)
            .into_iter()
            .rfind(|r| ty(r) == "FeatureChaining")?;
        let v = last.get("chainingFeature")?;
        if let Some(s) = v.get("@ref").and_then(|x| x.as_str()) {
            let name = match target_from_ref_string(s) {
                TargetRef::Name(qn) => qn.segments.last()?.value.clone(),
                TargetRef::Chain(_) => return None,
            };
            return Some(ChainLink::Ref(name));
        }
        ref_id(v).map(ChainLink::Id)
    }

    fn compute_qnames(&mut self, order: &[&'a str]) {
        for id in order {
            self.qname_of(id);
        }
    }

    fn qname_of(&mut self, id: &'a str) -> Option<Vec<String>> {
        if let Some(cached) = self.qnames.get(id) {
            return cached.clone();
        }
        // Walk the owner chain up to the nearest named ancestor, a root,
        // or a cycle, then name downward — iteratively, so a deep chain
        // costs no stack. A placeholder entry guards cycles; an id outside
        // the document (library reference, dangling patched @ref) has no
        // in-document qualified name — callers fall through to
        // `extra_names` / recovery spellings.
        let mut chain: Vec<(&'a str, El<'a>)> = Vec::new();
        let mut cur = id;
        let base: Option<Vec<String>> = loop {
            if let Some(cached) = self.qnames.get(cur) {
                break cached.clone();
            }
            self.qnames.insert(cur, None);
            let Some(&el) = self.by_id.get(cur) else {
                break None;
            };
            chain.push((cur, el));
            match self.owner_of(el) {
                None => break Some(Vec::new()),
                Some(owner) if ty(owner) == "Namespace" && self.owner_of(owner).is_none() => {
                    break Some(Vec::new());
                }
                Some(owner) => cur = id_of(owner),
            }
        };
        let mut path = base;
        for (cid, el) in chain.into_iter().rev() {
            path = match (path, self.effective_name(el, 0)) {
                (Some(mut p), Some(own)) => {
                    p.push(own);
                    Some(p)
                }
                _ => None,
            };
            self.qnames.insert(cid, path.clone());
        }
        path
    }

    /// Whether `el` carries materialized derived properties (a full-form
    /// document) — `qualifiedName` is derived-only, never emitted compact.
    fn is_full_form(el: El<'a>) -> bool {
        el.get("qualifiedName").is_some()
    }

    /// Owned relationships of `el`, in order, skipping implied ones.
    fn owned_rels(&self, el: El<'a>) -> Vec<El<'a>> {
        let Some(Value::Array(rels)) = el.get("ownedRelationship") else {
            return Vec::new();
        };
        rels.iter()
            .filter_map(ref_id)
            .filter_map(|id| self.by_id.get(id).copied())
            .filter(|rel| !bval(rel, "isImplied"))
            .collect()
    }

    /// The elements owned *by* a relationship.
    fn related(&self, rel: El<'a>) -> Vec<El<'a>> {
        let Some(Value::Array(elems)) = rel.get("ownedRelatedElement") else {
            return Vec::new();
        };
        elems
            .iter()
            .filter_map(ref_id)
            .filter_map(|id| self.by_id.get(id).copied())
            .collect()
    }

    fn first_related(&self, rel: El<'a>) -> Option<El<'a>> {
        self.related(rel).into_iter().next()
    }

    /// The expression element carried by an argument/operand
    /// ParameterMembership. The pilot shape (matched by the emitter) wraps
    /// the expression: the membership owns an `in` parameter Feature whose
    /// FeatureValue owns the expression. Older/foreign payloads may own the
    /// expression directly — accept both.
    fn param_expr_el(&self, rel: El<'a>) -> Option<El<'a>> {
        let kid = self.first_related(rel)?;
        if !is_expr_type(ty(kid)) {
            for r in self.owned_rels(kid) {
                if ty(r) == "FeatureValue" {
                    return self.first_related(r);
                }
            }
            // A parameter Feature without a value (type references, result
            // parameters) is not an operand.
            return None;
        }
        Some(kid)
    }

    /// Lift a reference property (`{"@id"}` or `{"@ref"}`) into a target.
    fn target(&mut self, holder: El<'a>, key: &str) -> Option<TargetRef> {
        let v = holder.get(key)?;
        if let Some(s) = v.get("@ref").and_then(|x| x.as_str()) {
            return Some(target_from_ref_string(s));
        }
        let mut id = ref_id(v)?;
        // An `OwnedFeatureChain`: a Feature owned by the referencing
        // relationship itself, carrying FeatureChaining links — lift it back
        // to the dotted `a.b.c` form.
        if let Some(&el) = self.by_id.get(id) {
            if el.get("owningRelationship").and_then(ref_id) == Some(id_of(holder)) {
                if let Some(chain) = self.lift_feature_chain(el) {
                    return Some(chain);
                }
            }
        }
        // `importedMembership` is Membership-typed: an in-document
        // membership names its member element (an alias membership's
        // `memberElement` carries the canonical target). Library
        // memberships are not in the document and name themselves through
        // the library name map below.
        if key == "importedMembership" {
            if let Some(&mel) = self.by_id.get(id) {
                if ty(mel).ends_with("Membership") {
                    if let Some(s) = mel
                        .get("memberElement")
                        .and_then(|m| m.get("@ref"))
                        .and_then(|x| x.as_str())
                    {
                        return Some(target_from_ref_string(s));
                    }
                    if let Some(member) = mel
                        .get("memberElement")
                        .and_then(ref_id)
                        .or_else(|| self.first_related(mel).map(id_of))
                    {
                        id = member;
                    }
                }
            }
        }
        self.name_for_id(id)
    }

    /// Name a reference target by id: in-document qualified name, then
    /// the caller-provided map (library elements, other documents of a
    /// multi-document payload), then the longest all-named suffix path,
    /// then a recovery spelling. Records an error and returns `None`
    /// when nothing names the id.
    fn name_for_id(&mut self, id: &'a str) -> Option<TargetRef> {
        if let Some(segments) = self.qnames.get(id).cloned().flatten() {
            return Some(TargetRef::Name(qn_global(&segments)));
        }
        if let Some(segments) = self.extra_names.get(id) {
            return Some(TargetRef::Name(qn_global(segments)));
        }
        // Unnameable ancestry (anonymous parents): fall back to the longest
        // all-named suffix path — the reference site is structurally
        // unchanged, so a relative path resolves like the original text.
        if let Some(el) = self.by_id.get(id).copied() {
            let mut segments = Vec::new();
            let mut cur = Some(el);
            while let Some(e) = cur {
                match self.effective_name(e, 0) {
                    Some(n) => segments.push(n),
                    None => break,
                }
                cur = self.owner_of(e);
            }
            if !segments.is_empty() {
                segments.reverse();
                return Some(TargetRef::Name(qn_from_segments(&segments)));
            }
        }
        // A dangling id carrying a recovery annotation restores its
        // original spelling (partial models round-trip through the full
        // form — see `crate::full::UNRESOLVED_REP_LANGUAGE`).
        if let Some(name) = self.unresolved_names.get(id) {
            return Some(target_from_ref_string(name));
        }
        self.record(format!(
            "cannot name reference target {id} (element outside document?)"
        ));
        // Even unnameable, the reference must not silently vanish from
        // the lifted text (an invocation argument would drop with it):
        // spell the raw id as a quoted name — unresolvable, but visible
        // and arity-preserving alongside the recorded error.
        Some(TargetRef::Name(qn_from_segments(&[id.to_string()])))
    }

    /// Reconstruct `a.b.c` from an owned chain Feature's FeatureChaining
    /// links. Link 1 prints as a full (`$::`-rooted where possible)
    /// qualified name; later links print their single member name, which
    /// re-resolves inside the previous link's scope. `None` if the element
    /// has no chainings or a link cannot be named.
    fn lift_feature_chain(&mut self, el: El<'a>) -> Option<TargetRef> {
        let mut links: Vec<QualifiedName> = Vec::new();
        for rel in self.owned_rels(el) {
            if ty(rel) != "FeatureChaining" {
                continue;
            }
            let v = rel.get("chainingFeature")?;
            if let Some(s) = v.get("@ref").and_then(|x| x.as_str()) {
                match target_from_ref_string(s) {
                    TargetRef::Name(qn) => links.push(qn),
                    // A nested chain inside a link never occurs.
                    TargetRef::Chain(_) => return None,
                }
                continue;
            }
            let id = ref_id(v)?;
            if links.is_empty() {
                // First link: an absolute path keeps it unambiguous.
                if let Some(segments) = self.qname_of(id) {
                    links.push(qn_global(&segments));
                } else if let Some(segments) = self.extra_names.get(id) {
                    links.push(qn_global(segments));
                } else if let Some(name) = self.unresolved_names.get(id) {
                    // A dangling link id with a recovery annotation (the
                    // full form patches `@ref` spellings to dangling ids).
                    match target_from_ref_string(name) {
                        TargetRef::Name(qn) => links.push(qn),
                        TargetRef::Chain(_) => return None,
                    }
                } else {
                    let el = self.by_id.get(id).copied()?;
                    links.push(qn_from_segments(&[self.effective_name(el, 0)?]));
                }
            } else {
                // Later links: the member's own name within the previous
                // link's feature.
                let name = match self.by_id.get(id).copied() {
                    Some(el) => self.effective_name(el, 0)?,
                    None => self.out_of_doc_name(id)?,
                };
                links.push(qn_from_segments(&[name]));
            }
        }
        if links.len() < 2 {
            return None;
        }
        Some(TargetRef::Chain(links))
    }

    fn identification(el: El) -> Identification {
        Identification {
            short_name: sval(el, "declaredShortName").map(name),
            name: sval(el, "declaredName").map(name),
        }
    }

    // ---- members ----

    fn lift_members(&mut self, rels: &[El<'a>]) -> Vec<Member> {
        let mut members = Vec::new();
        let mut leading_then = false;
        let mut leading_then_multiplicity = None;
        for rel in rels {
            // Empty succession = implied `then` before the next member: an
            // unnamed SuccessionAsUsage owning only the two bare ends of the
            // pilot's EmptySuccession rule (or, in legacy emissions, no ends
            // at all).
            if ty(rel) == "FeatureMembership" {
                if let Some(el) = self.first_related(rel) {
                    if ty(el) == "SuccessionAsUsage" && Self::declared_name(el).is_none() {
                        let rels = self.owned_rels(el);
                        if rels.is_empty() {
                            leading_then = true;
                            continue;
                        }
                        if rels.len() == 2
                            && ty(rels[0]) == "EndFeatureMembership"
                            && self.is_unreferenced_end(rels[0])
                            && ty(rels[1]) == "EndFeatureMembership"
                            && self.is_empty_end(rels[1])
                        {
                            leading_then = true;
                            leading_then_multiplicity = self
                                .lift_connector_end(rels[0])
                                .and_then(|e| e.multiplicity);
                            continue;
                        }
                    }
                }
            }
            // A port definition's implicit ConjugatedPortDefinition member
            // is re-derived by the emitter — never lifted as text.
            if ty(rel) == "OwningMembership"
                && self
                    .first_related(rel)
                    .is_some_and(|el| ty(el) == "ConjugatedPortDefinition")
            {
                continue;
            }
            if let Some(mut m) = self.lift_member(rel) {
                m.leading_then = leading_then;
                m.leading_then_multiplicity = leading_then_multiplicity.take();
                leading_then = false;
                members.push(m);
            }
        }
        members
    }

    fn member(visibility: Option<Visibility>, kind: MemberKind) -> Member {
        Member {
            visibility,
            leading_then: false,
            leading_then_multiplicity: None,
            kind,
            span: Span::default(),
        }
    }

    fn visibility(rel: El) -> Option<Visibility> {
        match sval(rel, "visibility") {
            Some("private") => Some(Visibility::Private),
            Some("protected") => Some(Visibility::Protected),
            _ => None,
        }
    }

    fn lift_import(&mut self, rel: El<'a>, is_namespace: bool) -> Import {
        let key = if is_namespace {
            "importedNamespace"
        } else {
            "importedMembership"
        };
        let target = match self.target(rel, key) {
            Some(TargetRef::Name(qn)) => qn,
            _ => qn_from_segments(&["<unresolved>".to_string()]),
        };
        Import {
            // Exposes force isImportAll (pilot `*ExposeImpl`) — implied,
            // so never printed as an `all` keyword.
            is_import_all: bval(rel, "isImportAll") && !ty(rel).ends_with("Expose"),
            target,
            is_namespace,
            is_recursive: bval(rel, "isRecursive"),
            filters: Vec::new(),
        }
    }

    /// Reconstruct `import P::*[expr]` from an implicit *FilterPackage*: a
    /// namespace-kind import whose `importedNamespace` is its own owned
    /// anonymous Package holding the actual import plus one
    /// ElementFilterMembership per bracket. `None` when the shape doesn't
    /// match (a plain namespace import).
    fn lift_filtered_import(&mut self, rel: El<'a>) -> Option<Import> {
        let pkg_id = ref_id(rel.get("importedNamespace")?)?;
        let pkg = self.by_id.get(pkg_id).copied()?;
        if ty(pkg) != "Package"
            || pkg.get("owningRelationship").and_then(ref_id) != Some(id_of(rel))
        {
            return None;
        }
        let mut inner: Option<Import> = None;
        let mut filters = Vec::new();
        for r in self.owned_rels(pkg) {
            match ty(r) {
                "NamespaceImport" => inner = Some(self.lift_import(r, true)),
                "MembershipImport" => inner = Some(self.lift_import(r, false)),
                "ElementFilterMembership" => {
                    let el = self.first_related(r)?;
                    filters.push(self.lift_expr(el)?);
                }
                _ => return None,
            }
        }
        let mut imp = inner?;
        if filters.is_empty() {
            return None;
        }
        imp.filters = filters;
        // The `all` prefix rides the outer import (implied on exposes).
        imp.is_import_all = bval(rel, "isImportAll") && !ty(rel).ends_with("Expose");
        Some(imp)
    }

    /// [`Self::lift_import`], first trying the FilterPackage shape.
    fn lift_any_import(&mut self, rel: El<'a>) -> Import {
        match self.lift_filtered_import(rel) {
            Some(imp) => imp,
            None => self.lift_import(rel, true),
        }
    }

    /// An Annotation owned by the annotated element that owns its
    /// annotating element lifts that element as a member; an annotating
    /// element with `about` targets of its own keeps the owner among them.
    #[inline(never)]
    fn lift_prefix_annotation(&mut self, rel: El<'a>, vis: Option<Visibility>) -> Option<Member> {
        let Some(el) = self
            .first_related(rel)
            .filter(|el| crate::metaclass::conforms(ty(el), "AnnotatingElement"))
        else {
            self.errors
                .push("unsupported member relationship @type Annotation".to_string());
            return None;
        };
        let in_type = self.owner_is_type(rel);
        let mut member = self.lift_owning_member_element(el, vis, in_type)?;
        // An annotating element with `about` targets of its own
        // annotates only those; the owner it also annotated in this
        // shape joins the targets so nothing is lost.
        let owner = match self.target(rel, "owningRelatedElement") {
            Some(TargetRef::Name(qn)) => Some(qn),
            _ => None,
        };
        match &mut member.kind {
            MemberKind::Comment(c) if !c.about.is_empty() => {
                if let Some(owner) = owner {
                    c.about.insert(0, owner);
                }
            }
            MemberKind::Usage(u) => {
                if let UsageDetail::Metadata { about } = &mut u.detail {
                    if !about.is_empty() {
                        if let Some(owner) = owner {
                            about.insert(0, owner);
                        }
                    }
                }
            }
            _ => {}
        }
        Some(member)
    }

    fn lift_member(&mut self, rel: El<'a>) -> Option<Member> {
        let id = id_of(rel);
        self.enter(id)?;
        let member = self.lift_member_inner(rel);
        self.leave(id);
        member
    }

    fn lift_member_inner(&mut self, rel: El<'a>) -> Option<Member> {
        let vis = Self::visibility(rel);
        // The visibility indicator is mandatory on imports (`ImportPrefix`),
        // so a public import must print explicitly — unlike other members,
        // where public is the unwritten default.
        let import_vis = vis.or(Some(Visibility::Public));
        match ty(rel) {
            "NamespaceImport" => Some(Self::member(
                import_vis,
                MemberKind::Import(self.lift_any_import(rel)),
            )),
            "MembershipImport" => Some(Self::member(
                import_vis,
                MemberKind::Import(self.lift_import(rel, false)),
            )),
            "NamespaceExpose" => Some(Self::member(
                None,
                MemberKind::Expose(self.lift_any_import(rel)),
            )),
            "MembershipExpose" => Some(Self::member(
                None,
                MemberKind::Expose(self.lift_import(rel, false)),
            )),
            "Membership" => {
                // The full form materializes the *derived* member names —
                // the target's own spellings; only a differing name is an
                // alias (compact only spells names on aliases).
                let mut member_short = sval(rel, "memberShortName");
                let mut member_name = sval(rel, "memberName");
                if Self::is_full_form(rel) {
                    if let Some(tel) = rel
                        .get("memberElement")
                        .and_then(ref_id)
                        .and_then(|i| self.by_id.get(i).copied())
                    {
                        if member_name == sval(tel, "declaredName") {
                            member_name = None;
                        }
                        if member_short == sval(tel, "declaredShortName") {
                            member_short = None;
                        }
                    }
                }
                let id = Identification {
                    short_name: member_short.map(name),
                    name: member_name.map(name),
                };
                let target = self.target(rel, "memberElement")?;
                if id.is_empty() {
                    let TargetRef::Name(qn) = target else {
                        return None;
                    };
                    Some(Self::member(vis, MemberKind::InitialNode(qn)))
                } else {
                    let TargetRef::Name(qn) = target else {
                        return None;
                    };
                    Some(Self::member(
                        vis,
                        MemberKind::Alias(Alias { id, target: qn }),
                    ))
                }
            }
            "ElementFilterMembership" => {
                let el = self.first_related(rel)?;
                let expr = self.lift_expr(el)?;
                Some(Self::member(vis, MemberKind::Filter(expr)))
            }
            "OwningMembership" => {
                let el = self.first_related(rel)?;
                let in_type = self.owner_is_type(rel);
                self.lift_owning_member_element(el, vis, in_type)
            }
            // The prefix-annotation shape (KerML `ownedAnnotatingElement`):
            // the annotated element owns the Annotation, which owns the
            // annotating element — a body comment, documentation or
            // metadata of the owner, exactly what the owning-membership
            // shape spells.
            // The prefix-annotation shape (KerML `ownedAnnotatingElement`):
            // out of line, because this function recurses through every
            // member and its frame must stay small.
            "Annotation" => self.lift_prefix_annotation(rel, vis),
            "FeatureMembership" | "EndFeatureMembership" => {
                let el = self.first_related(rel)?;
                let usage = self.lift_usage(el, false)?;
                Some(Self::member(vis, MemberKind::Usage(usage)))
            }
            "VariantMembership" => {
                let el = self.first_related(rel)?;
                // Inside an enumeration definition, variant memberships
                // are enum literals and print *bare* (no `variant`
                // keyword, no usage keyword); everywhere else they are
                // explicit `variant` members of a variation.
                let in_enum = rel
                    .get("owningRelatedElement")
                    .and_then(|v| v.get("@id"))
                    .and_then(|v| v.as_str())
                    .and_then(|id| self.by_id.get(id))
                    .is_some_and(|owner| ty(owner) == "EnumerationDefinition");
                let usage = if in_enum {
                    self.next_featuring = false;
                    let mut u = self.lift_usage(el, false)?;
                    u.kind = UsageKind::Default;
                    u
                } else {
                    self.next_featuring = self.body_featuring;
                    self.lift_usage(el, true)?
                };
                Some(Self::member(vis, MemberKind::Usage(usage)))
            }
            "SubjectMembership" => {
                let el = self.first_related(rel)?;
                let mut u = self.lift_usage(el, false)?;
                u.prefix.direction = None; // membership-implied `in`
                Some(Self::member(vis, MemberKind::Subject(u)))
            }
            "ActorMembership" => {
                let el = self.first_related(rel)?;
                let mut u = self.lift_usage(el, false)?;
                u.prefix.direction = None; // membership-implied `in`
                Some(Self::member(vis, MemberKind::Actor(u)))
            }
            "StakeholderMembership" => {
                let el = self.first_related(rel)?;
                let mut u = self.lift_usage(el, false)?;
                u.prefix.direction = None; // membership-implied `in`
                Some(Self::member(vis, MemberKind::Stakeholder(u)))
            }
            "ObjectiveMembership" => {
                let el = self.first_related(rel)?;
                Some(Self::member(
                    vis,
                    MemberKind::Objective(self.lift_usage(el, false)?),
                ))
            }
            "RequirementConstraintMembership" => {
                let kind = if sval(rel, "kind") == Some("assumption") {
                    RequirementConstraintKind::Assumption
                } else {
                    RequirementConstraintKind::Requirement
                };
                let el = self.first_related(rel)?;
                Some(Self::member(
                    vis,
                    MemberKind::RequirementConstraint {
                        kind,
                        usage: self.lift_usage(el, false)?,
                    },
                ))
            }
            "FramedConcernMembership" => {
                let el = self.first_related(rel)?;
                Some(Self::member(
                    vis,
                    MemberKind::FramedConcern(self.lift_usage(el, false)?),
                ))
            }
            "RequirementVerificationMembership" => {
                let el = self.first_related(rel)?;
                Some(Self::member(
                    vis,
                    MemberKind::RequirementVerification(self.lift_usage(el, false)?),
                ))
            }
            "ViewRenderingMembership" => {
                let el = self.first_related(rel)?;
                Some(Self::member(
                    vis,
                    MemberKind::Render(self.lift_usage(el, false)?),
                ))
            }
            "ReturnParameterMembership" => {
                let el = self.first_related(rel)?;
                let mut u = self.lift_usage(el, false)?;
                u.prefix.direction = None; // membership-implied `out`
                Some(Self::member(vis, MemberKind::Return(u)))
            }
            "ResultExpressionMembership" => {
                let el = self.first_related(rel)?;
                Some(Self::member(vis, MemberKind::Result(self.lift_expr(el)?)))
            }
            "StateSubactionMembership" => {
                let kind = match sval(rel, "kind") {
                    Some("entry") => StateSubactionKind::Entry,
                    Some("exit") => StateSubactionKind::Exit,
                    _ => StateSubactionKind::Do,
                };
                let el = self.first_related(rel)?;
                let action = if self.owned_rels(el).is_empty() && Self::declared_name(el).is_none()
                {
                    None
                } else {
                    Some(self.lift_usage(el, false)?)
                };
                Some(Self::member(
                    vis,
                    MemberKind::StateSubaction { kind, action },
                ))
            }
            other => {
                self.record(format!("unsupported member relationship @type {other}"));
                None
            }
        }
    }

    /// Whether a membership's owner is a Type rather than a
    /// package/namespace (or the document root): a usage under a Type's
    /// OwningMembership is a KerML `member` type-member, while one under
    /// a namespace is a plain member (SysML `PackageMember`, KerML
    /// `NamespaceFeatureMember`) and prints bare.
    fn owner_is_type(&self, rel: El<'a>) -> bool {
        rel.get("owningRelatedElement")
            .and_then(|v| ref_id(v))
            .and_then(|id| self.by_id.get(id))
            .is_some_and(|owner| !matches!(ty(owner), "Namespace" | "Package" | "LibraryPackage"))
    }

    /// Elements under an OwningMembership (or a document root).
    /// `owner_is_type` marks memberships owned by a Type (see
    /// [`Self::owner_is_type`]); it only affects usages.
    fn lift_owning_member_element(
        &mut self,
        el: El<'a>,
        vis: Option<Visibility>,
        owner_is_type: bool,
    ) -> Option<Member> {
        let t = ty(el);
        // Packages / namespaces.
        if matches!(t, "Package" | "LibraryPackage" | "Namespace") {
            // The only owned element whose body is lifted here rather
            // than through `lift_definition` / `lift_usage`, so this is
            // where its own step is counted.
            self.enter(id_of(el))?;
            let rels = self.owned_rels(el);
            let (metadata, rest) = self.take_prefix_metadata(&rels);
            let members = self.lift_members(&rest);
            self.leave(id_of(el));
            return Some(Self::member(
                vis,
                MemberKind::Package(Package {
                    is_library: t == "LibraryPackage",
                    is_standard: bval(el, "isStandard"),
                    is_namespace: t == "Namespace",
                    metadata,
                    id: Self::identification(el),
                    body: if members.is_empty() {
                        None
                    } else {
                        Some(members)
                    },
                }),
            ));
        }
        // Annotating elements.
        match t {
            "Comment" => {
                let mut about = Vec::new();
                for rel in self.owned_rels(el) {
                    if ty(rel) == "Annotation" {
                        if let Some(TargetRef::Name(qn)) = self.target(rel, "annotatedElement") {
                            about.push(qn);
                        }
                    }
                }
                return Some(Self::member(
                    vis,
                    MemberKind::Comment(Comment {
                        id: Self::identification(el),
                        about,
                        locale: sval(el, "locale").map(|s| s.to_string()),
                        body: sval(el, "body").unwrap_or("").to_string(),
                    }),
                ));
            }
            "Documentation" => {
                return Some(Self::member(
                    vis,
                    MemberKind::Doc(Doc {
                        id: Self::identification(el),
                        locale: sval(el, "locale").map(|s| s.to_string()),
                        body: sval(el, "body").unwrap_or("").to_string(),
                    }),
                ));
            }
            "TextualRepresentation" => {
                // Recovery annotations are carriers, not model content —
                // their names were already restored at the reference sites.
                if sval(el, "language") == Some(crate::full::UNRESOLVED_REP_LANGUAGE) {
                    return None;
                }
                return Some(Self::member(
                    vis,
                    MemberKind::TextualRep(TextualRep {
                        id: Self::identification(el),
                        language: sval(el, "language").unwrap_or("").to_string(),
                        body: sval(el, "body").unwrap_or("").to_string(),
                    }),
                ));
            }
            "Dependency" => {
                let mut clients = Vec::new();
                let mut suppliers = Vec::new();
                for (key, out) in [("client", &mut clients), ("supplier", &mut suppliers)] {
                    if let Some(Value::Array(refs)) = el.get(key) {
                        for r in refs {
                            let id = ref_id(r);
                            if let Some(id) = id {
                                match self.name_for_id(id) {
                                    Some(TargetRef::Name(qn)) => out.push(qn),
                                    // Dependency ends are plain qualified
                                    // names; a (theoretical) chain keeps
                                    // its last link.
                                    Some(TargetRef::Chain(links)) => {
                                        out.extend(links.into_iter().last())
                                    }
                                    // `name_for_id` recorded the error;
                                    // dropping the end at least keeps the
                                    // damage visible in the warnings.
                                    None => {}
                                }
                            } else if let Some(s) = r.get("@ref").and_then(|x| x.as_str()) {
                                // `@ref` strings quote restricted names —
                                // parse them like every other reference.
                                match target_from_ref_string(s) {
                                    TargetRef::Name(qn) => out.push(qn),
                                    // Dependency ends are plain qualified
                                    // names; a (theoretical) chain keeps
                                    // its last link.
                                    TargetRef::Chain(links) => out.extend(links.into_iter().last()),
                                }
                            }
                        }
                    }
                }
                let rels = self.owned_rels(el);
                let (metadata, _) = self.take_prefix_metadata(&rels);
                return Some(Self::member(
                    vis,
                    MemberKind::Dependency(Dependency {
                        metadata,
                        id: Self::identification(el),
                        clients,
                        suppliers,
                    }),
                ));
            }
            // KerML standalone relationship declarations (as owned elements).
            "Specialization" | "Subclassification" | "FeatureTyping" | "Subsetting"
            | "Redefinition" | "Conjugation" | "Disjoining" | "FeatureInverting"
            | "TypeFeaturing" => {
                use RelationshipDeclKind::*;
                let (kind, skey, tkey) = match t {
                    "Specialization" => (Specialization, "specific", "general"),
                    "Subclassification" => (Subclassification, "subclassifier", "superclassifier"),
                    "FeatureTyping" => (FeatureTyping, "typedFeature", "type"),
                    "Subsetting" => (Subsetting, "subsettingFeature", "subsettedFeature"),
                    "Redefinition" => (Redefinition, "redefiningFeature", "redefinedFeature"),
                    "Conjugation" => (Conjugation, "conjugatedType", "originalType"),
                    "Disjoining" => (Disjoining, "typeDisjoined", "disjoiningType"),
                    "FeatureInverting" => (FeatureInverting, "featureInverted", "invertingFeature"),
                    _ => (TypeFeaturing, "featureOfType", "featuringType"),
                };
                let source = self.target(el, skey)?;
                let target = self.target(el, tkey)?;
                return Some(Self::member(
                    vis,
                    MemberKind::Relationship(RelationshipDecl {
                        kind,
                        id: Self::identification(el),
                        source,
                        target,
                    }),
                ));
            }
            "MultiplicityRange" | "Multiplicity" => {
                let mut subsets = None;
                let mut bounds = Vec::new();
                let mut body = Vec::new();
                let rels = self.owned_rels(el);
                for rel in &rels {
                    match ty(rel) {
                        "Subsetting" => subsets = self.target(rel, "subsettedFeature"),
                        "OwningMembership" => {
                            if let Some(inner) = self.first_related(rel) {
                                if is_expr_type(ty(inner)) {
                                    if let Some(e) = self.lift_expr(inner) {
                                        bounds.push(e);
                                        continue;
                                    }
                                }
                            }
                            if let Some(m) = self.lift_member(rel) {
                                body.push(m);
                            }
                        }
                        _ => {
                            if let Some(m) = self.lift_member(rel) {
                                body.push(m);
                            }
                        }
                    }
                }
                let range = self.bounds_to_multiplicity(bounds).map(|m| *m);
                return Some(Self::member(
                    vis,
                    MemberKind::MultiplicityDecl(MultiplicityDecl {
                        id: Self::identification(el),
                        subsets,
                        range,
                        body: if body.is_empty() { None } else { Some(body) },
                    }),
                ));
            }
            _ => {}
        }
        // Definitions.
        if let Some(kind) = def_kind_of(t) {
            return Some(Self::member(
                vis,
                MemberKind::Definition(self.lift_definition(el, kind)?),
            ));
        }
        // Usages under OwningMembership: package/namespace members (bare)
        // or KerML `member` type-members, by the owner's metaclass (or
        // prefix metadata, which the owner should have consumed).
        if usage_kind_of(t, self.dialect).is_some() {
            self.next_featuring = false;
            let mut usage = self.lift_usage(el, false)?;
            // The KerML `member` prefix; SysML has no such spelling —
            // metadata usages (and any other SysML usage under an
            // OwningMembership) print bare.
            usage.prefix.is_type_member = owner_is_type && self.dialect == Dialect::Kerml;
            return Some(Self::member(vis, MemberKind::Usage(usage)));
        }
        self.record(format!("unsupported owned element @type {t}"));
        None
    }

    /// Split leading bare metadata-usage memberships (prefix `#Meta`) from
    /// the rest of the owned relationships.
    fn take_prefix_metadata(&mut self, rels: &[El<'a>]) -> (Vec<QualifiedName>, Vec<El<'a>>) {
        let mut metadata = Vec::new();
        let mut rest = Vec::new();
        let mut prefix_zone = true;
        for rel in rels {
            if prefix_zone && ty(rel) == "OwningMembership" {
                if let Some(el) = self.first_related(rel) {
                    if matches!(ty(el), "MetadataUsage" | "MetadataFeature")
                        && Self::declared_name(el).is_none()
                    {
                        let inner = self.owned_rels(el);
                        if inner.len() == 1 && ty(inner[0]) == "FeatureTyping" {
                            if let Some(TargetRef::Name(qn)) = self.target(inner[0], "type") {
                                metadata.push(qn);
                                continue;
                            }
                        }
                    }
                }
            }
            prefix_zone = false;
            rest.push(*rel);
        }
        (metadata, rest)
    }

    fn bounds_to_multiplicity(&self, mut bounds: Vec<Expr>) -> Option<Box<Multiplicity>> {
        match bounds.len() {
            1 => Some(Box::new(Multiplicity {
                lower: None,
                upper: bounds.pop().unwrap(),
                span: Span::default(),
            })),
            2 => {
                let upper = bounds.pop().unwrap();
                let lower = bounds.pop().unwrap();
                Some(Box::new(Multiplicity {
                    lower: Some(lower),
                    upper,
                    span: Span::default(),
                }))
            }
            _ => None,
        }
    }

    // ---- definitions ----

    fn lift_definition(&mut self, el: El<'a>, kind: DefKind) -> Option<Definition> {
        let id = id_of(el);
        self.enter(id)?;
        let definition = self.lift_definition_inner(el, kind);
        self.leave(id);
        definition
    }

    fn lift_definition_inner(&mut self, el: El<'a>, kind: DefKind) -> Option<Definition> {
        let rels = self.owned_rels(el);
        let (metadata, rels) = self.take_prefix_metadata(&rels);
        let mut specializes = Vec::new();
        let mut conjugates = Vec::new();
        let mut disjoint_from = Vec::new();
        let mut unions = Vec::new();
        let mut intersects = Vec::new();
        let mut differences = Vec::new();
        let mut multiplicity = None;
        let mut body_rels = Vec::new();
        for rel in rels {
            match ty(rel) {
                "Subclassification" => {
                    if let Some(t) = self.target(rel, "superclassifier") {
                        specializes.push(t);
                    }
                }
                "Conjugation" => {
                    if let Some(t) = self.target(rel, "originalType") {
                        conjugates.push(t);
                    }
                }
                "Disjoining" => {
                    if let Some(t) = self.target(rel, "disjoiningType") {
                        disjoint_from.push(t);
                    }
                }
                "Unioning" => {
                    if let Some(t) = self.target(rel, "unioningType") {
                        unions.push(t);
                    }
                }
                "Intersecting" => {
                    if let Some(t) = self.target(rel, "intersectingType") {
                        intersects.push(t);
                    }
                }
                "Differencing" => {
                    if let Some(t) = self.target(rel, "differencingType") {
                        differences.push(t);
                    }
                }
                "OwningMembership" if multiplicity.is_none() => {
                    // Unnamed multiplicity range = the type's multiplicity.
                    if let Some(inner) = self.first_related(rel) {
                        if ty(inner) == "MultiplicityRange" && Self::declared_name(inner).is_none()
                        {
                            let bounds = self.range_bounds(inner);
                            multiplicity = self.bounds_to_multiplicity(bounds);
                            continue;
                        }
                    }
                    body_rels.push(rel);
                }
                _ => body_rels.push(rel),
            }
        }
        // Variants of a variation *definition* have no featuring type
        // (pilot `getExpectedFeaturingTypeOf` requires a Usage container).
        let saved_body = std::mem::replace(&mut self.body_featuring, false);
        let members = self.lift_members(&body_rels);
        self.body_featuring = saved_body;
        Some(Definition {
            prefix: DefPrefix {
                // A variation is implicitly abstract, and an enumeration
                // definition implicitly a variation — the emitter derives
                // both, so neither prints (not grammatical where implied).
                is_abstract: bval(el, "isAbstract") && !bval(el, "isVariation"),
                is_variation: bval(el, "isVariation") && ty(el) != "EnumerationDefinition",
                is_individual: bval(el, "isIndividual"),
                metadata,
            },
            kind: if kind == DefKind::Occurrence && bval(el, "isIndividual") {
                DefKind::Individual
            } else {
                kind
            },
            id: Self::identification(el),
            specializes,
            is_parallel: bval(el, "isParallel"),
            // Association-family definitions are sufficient by rule and the
            // full form materializes that (mirrors the emitter) — `all`
            // only prints from a compact/textual spelling.
            is_sufficient: bval(el, "isSufficient")
                && !(Self::is_full_form(el)
                    && matches!(
                        ty(el),
                        "InterfaceDefinition"
                            | "ConnectionDefinition"
                            | "AllocationDefinition"
                            | "Association"
                            | "AssociationStructure"
                    )),
            multiplicity,
            conjugates,
            disjoint_from,
            unions,
            intersects,
            differences,
            body: if members.is_empty() {
                None
            } else {
                Some(members)
            },
        })
    }

    fn range_bounds(&mut self, range_el: El<'a>) -> Vec<Expr> {
        let mut bounds = Vec::new();
        for rel in self.owned_rels(range_el) {
            if ty(rel) == "OwningMembership" {
                if let Some(inner) = self.first_related(rel) {
                    if let Some(e) = self.lift_expr(inner) {
                        bounds.push(e);
                    }
                }
            }
        }
        bounds
    }

    // ---- usages ----

    fn lift_usage(&mut self, el: El<'a>, is_variant: bool) -> Option<Usage> {
        let id = id_of(el);
        self.enter(id)?;
        let usage = self.lift_usage_inner(el, is_variant);
        self.leave(id);
        usage
    }

    #[allow(clippy::too_many_lines)]
    fn lift_usage_inner(&mut self, el: El<'a>, is_variant: bool) -> Option<Usage> {
        let t = ty(el);
        let featuring = std::mem::replace(&mut self.next_featuring, true);
        let kind = usage_kind_of(t, self.dialect).unwrap_or(UsageKind::Default);
        let rels = self.owned_rels(el);
        let (metadata, rels) = self.take_prefix_metadata(&rels);

        let mut prefix = UsagePrefix {
            direction: match sval(el, "direction") {
                Some("in") => Some(FeatureDirection::In),
                Some("out") => Some(FeatureDirection::Out),
                Some("inout") => Some(FeatureDirection::InOut),
                _ => None,
            },
            is_derived: bval(el, "isDerived"),
            // A variation is implicitly abstract (mirrors the emitter).
            is_abstract: bval(el, "isAbstract") && !bval(el, "isVariation"),
            is_variation: bval(el, "isVariation"),
            // End features are constant by rule (KerML 2025) and the full
            // form materializes that (mirrors the emitter) — `constant`
            // only prints from a compact/textual spelling.
            is_constant: bval(el, "isConstant") && !(Self::is_full_form(el) && bval(el, "isEnd")),
            is_ref: false,
            is_end: bval(el, "isEnd"),
            is_individual: bval(el, "isIndividual"),
            portion: match sval(el, "portionKind") {
                Some("snapshot") => Some(PortionKind::Snapshot),
                Some("timeslice") => Some(PortionKind::Timeslice),
                _ => None,
            },
            is_variant,
            metadata,
            end_cross: None,
            // `composite` is a KerML feature-prefix keyword; for SysML
            // usages isComposite is the derived-by-rule default (the `ref`
            // reconstruction below explains any non-default value).
            is_composite: bval(el, "isComposite") && self.dialect == Dialect::Kerml,
            is_portion: bval(el, "isPortion"),
            // `var` is a KerML feature prefix with no SysML spelling —
            // dropped for `*Usage` metaclasses (some producers mark
            // plain attribute usages `isVariable: true`; printing `var`
            // would not re-parse).
            is_variable: bval(el, "isVariable") && !ty(el).ends_with("Usage"),
            is_type_member: false,
        };

        // Invert the emitter's `isComposite` rule: a featured SysML usage
        // of a composite-by-default metaclass with no direction and not an
        // end can only be non-composite because `ref` was written. Ports
        // are composite only as sub-ports, so bare `ref` on a part-owned
        // port is not reconstructible (canonicalized away, same JSON).
        let owner_ty = el
            .get("owningRelationship")
            .and_then(|v| v.get("@id"))
            .and_then(|v| v.as_str())
            .and_then(|id| self.by_id.get(id))
            .and_then(|rel| rel.get("owningRelatedElement"))
            .and_then(|v| v.get("@id"))
            .and_then(|v| v.as_str())
            .and_then(|id| self.by_id.get(id))
            .map(|owner| ty(owner));
        // Interface-body ends are PortUsages in the pilot (the keywordless
        // DefaultInterfaceEnd / connect-part InterfaceEnd rules) — they
        // print keywordless, not as `port` usages. A leading cross feature
        // keeps the keyword (`end [1] port s : P` — the keywordless
        // spelling doesn't parse with a cross multiplicity).
        let has_cross = prefix.is_end
            && rels.first().is_some_and(|r| {
                ty(r) == "OwningMembership"
                    && self
                        .first_related(r)
                        .is_some_and(|inner| matches!(ty(inner), "ReferenceUsage" | "Feature"))
            });
        let kind = if t == "PortUsage"
            && prefix.is_end
            && !has_cross
            && matches!(owner_ty, Some("InterfaceDefinition" | "InterfaceUsage"))
        {
            UsageKind::Default
        } else {
            kind
        };
        if self.dialect == Dialect::Sysml
            && featuring
            && t.ends_with("Usage")
            && el.get("isComposite").and_then(|v| v.as_bool()) == Some(false)
            && prefix.direction.is_none()
            && !prefix.is_end
            && !matches!(
                t,
                "AttributeUsage"
                    | "EnumerationUsage"
                    | "ReferenceUsage"
                    | "BindingConnectorAsUsage"
                    | "SuccessionAsUsage"
                    | "EventOccurrenceUsage"
                    | "ExhibitStateUsage"
                    | "IncludeUseCaseUsage"
                    | "PerformActionUsage"
                    | "MetadataUsage"
            )
            && (t != "PortUsage" || matches!(owner_ty, Some("PortDefinition" | "PortUsage")))
        {
            prefix.is_ref = true;
        }

        let mut declaration = FeatureDeclaration {
            id: Self::identification(el),
            is_ordered: bval(el, "isOrdered"),
            is_nonunique: el
                .get("isUnique")
                .and_then(|v| v.as_bool())
                .map(|u| !u)
                .unwrap_or(false),
            is_sufficient: bval(el, "isSufficient"),
            ..Default::default()
        };
        let mut value = None;
        let mut body_rels: Vec<El<'a>> = Vec::new();
        let mut about = Vec::new();
        let mut ends: Vec<ConnectorEnd> = Vec::new();
        let mut flow_payload = None;
        let mut flow_ends: Vec<FlowEnd> = Vec::new();
        let mut params: Vec<El<'a>> = Vec::new();
        let mut transition_source = None;
        let mut transition_trigger = None;
        let mut transition_guard = None;
        let mut transition_effect = None;
        let mut transition_target = None;
        let mut satisfy_by = None;
        let mut chain_links: Vec<TargetRef> = Vec::new();

        // Connector-part ends are only lifted as a detail when *every* end
        // membership is bare (`connect a to b`); mixed or rich ends are body
        // members (`connection : C { end :>> end1 ::> d1; … }`).
        let connector_family = matches!(
            kind,
            UsageKind::Connection
                | UsageKind::Interface
                | UsageKind::Allocation
                | UsageKind::Connector
                | UsageKind::Binding
                | UsageKind::Succession
        );
        let end_rels: Vec<&El<'a>> = rels
            .iter()
            .filter(|r| ty(r) == "EndFeatureMembership")
            .collect();
        let min_detail_ends = match kind {
            // `then target;` successions have a single end; bindings two.
            UsageKind::Succession | UsageKind::Binding => 1,
            _ => 2,
        };
        let ends_as_detail = connector_family
            && end_rels.len() >= min_detail_ends
            && end_rels.iter().enumerate().all(|(i, r)| {
                // A succession's source end may be unspelled (`then x;`,
                // `then [1] x;` — no ReferenceSubsetting).
                self.is_bare_end(r)
                    || (kind == UsageKind::Succession && i == 0 && self.is_unreferenced_end(r))
            });

        let mut rel_iter = rels.iter().peekable();
        // Cross feature: leading OwningMembership + reference feature on an
        // end usage.
        if prefix.is_end {
            if let Some(rel) = rel_iter.peek() {
                if ty(rel) == "OwningMembership" {
                    if let Some(inner) = self.first_related(rel) {
                        if matches!(ty(inner), "ReferenceUsage" | "Feature") {
                            let cross = self.lift_usage(inner, false)?;
                            prefix.end_cross = Some(Box::new(CrossFeature {
                                direction: cross.prefix.direction,
                                is_derived: cross.prefix.is_derived,
                                is_abstract: cross.prefix.is_abstract,
                                is_variation: cross.prefix.is_variation,
                                is_constant: cross.prefix.is_constant,
                                is_ref: cross.prefix.is_ref,
                                is_composite: cross.prefix.is_composite,
                                is_portion: cross.prefix.is_portion,
                                is_variable: cross.prefix.is_variable,
                                decl: cross.declaration,
                            }));
                            rel_iter.next();
                        }
                    }
                }
            }
        }

        for rel in rel_iter {
            match ty(rel) {
                "FeatureTyping" | "ConjugatedPortTyping" => {
                    let is_conjugated = ty(rel) == "ConjugatedPortTyping";
                    if let Some(target) = self.target(rel, "type") {
                        let tr = TypeRef {
                            is_conjugated,
                            target: Self::unconjugate(is_conjugated, target),
                        };
                        if let Some(FeatureSpecialization::TypedBy(list)) =
                            declaration.specializations.last_mut()
                        {
                            list.push(tr);
                        } else {
                            declaration
                                .specializations
                                .push(FeatureSpecialization::TypedBy(vec![tr]));
                        }
                    }
                }
                "Subsetting" => {
                    if let Some(target) = self.target(rel, "subsettedFeature") {
                        if let Some(FeatureSpecialization::Subsets(list)) =
                            declaration.specializations.last_mut()
                        {
                            list.push(target);
                        } else {
                            declaration
                                .specializations
                                .push(FeatureSpecialization::Subsets(vec![target]));
                        }
                    }
                }
                "Redefinition" => {
                    if let Some(target) = self.target(rel, "redefinedFeature") {
                        if let Some(FeatureSpecialization::Redefines(list)) =
                            declaration.specializations.last_mut()
                        {
                            list.push(target);
                        } else {
                            declaration
                                .specializations
                                .push(FeatureSpecialization::Redefines(vec![target]));
                        }
                    }
                }
                "ReferenceSubsetting" => {
                    if let Some(target) = self.target(rel, "referencedFeature") {
                        declaration
                            .specializations
                            .push(FeatureSpecialization::References(target));
                    }
                }
                "CrossSubsetting" => {
                    if let Some(target) = self.target(rel, "crossedFeature") {
                        declaration
                            .specializations
                            .push(FeatureSpecialization::Crosses(target));
                    }
                }
                "Conjugation" => declaration.conjugates = self.target(rel, "originalType"),
                "FeatureChaining" => {
                    if let Some(t) = self.target(rel, "chainingFeature") {
                        chain_links.push(t);
                    }
                }
                "FeatureInverting" => declaration.inverse_of = self.target(rel, "invertingFeature"),
                "TypeFeaturing" => {
                    if let Some(t) = self.target(rel, "featuringType") {
                        declaration.featured_by.push(t);
                    }
                }
                "Disjoining" => {
                    if let Some(t) = self.target(rel, "disjoiningType") {
                        declaration.disjoint_from.push(t);
                    }
                }
                "Unioning" => {
                    if let Some(t) = self.target(rel, "unioningType") {
                        declaration.unions.push(t);
                    }
                }
                "Intersecting" => {
                    if let Some(t) = self.target(rel, "intersectingType") {
                        declaration.intersects.push(t);
                    }
                }
                "Differencing" => {
                    if let Some(t) = self.target(rel, "differencingType") {
                        declaration.differences.push(t);
                    }
                }
                "FeatureValue" => {
                    let is_initial = bval(rel, "isInitial");
                    let is_default = bval(rel, "isDefault");
                    if let Some(expr_el) = self.first_related(rel) {
                        if let Some(expr) = self.lift_expr(expr_el) {
                            value = Some(FeatureValue {
                                kind: match (is_default, is_initial) {
                                    (true, true) => ValueKind::DefaultInitial,
                                    (true, false) => ValueKind::Default,
                                    (false, true) => ValueKind::Initial,
                                    (false, false) => ValueKind::Bound,
                                },
                                expr,
                            });
                        }
                    }
                }
                "Annotation" => {
                    if let Some(TargetRef::Name(qn)) = self.target(rel, "annotatedElement") {
                        about.push(qn);
                    }
                }
                "OwningMembership" => {
                    let inner = self.first_related(rel);
                    match inner.map(ty) {
                        // A chain source (`first a.b`): the membership owns
                        // the synthesized chain feature and names it as its
                        // member.
                        Some("Feature")
                            if kind == UsageKind::Transition
                                && transition_source.is_none()
                                && self
                                    .owned_rels(inner.unwrap())
                                    .iter()
                                    .any(|r| ty(r) == "FeatureChaining") =>
                        {
                            // `memberElement` is derived on an
                            // OwningMembership; a producer may omit it.
                            transition_source = self
                                .target(rel, "memberElement")
                                .or_else(|| self.lift_feature_chain(inner.unwrap()));
                        }
                        Some("MultiplicityRange")
                            if declaration.multiplicity.is_none()
                                && Self::declared_name(inner.unwrap()).is_none() =>
                        {
                            let bounds = self.range_bounds(inner.unwrap());
                            declaration.multiplicity = self.bounds_to_multiplicity(bounds);
                        }
                        Some("SuccessionAsUsage") if kind == UsageKind::Transition => {
                            // Transition target succession: the referenced
                            // end (the first end is a bare EmptySourceEnd).
                            let succ = inner.unwrap();
                            for srel in self.owned_rels(succ) {
                                if ty(srel) == "EndFeatureMembership" {
                                    if let Some(end) = self.lift_connector_end(srel) {
                                        if !matches!(&end.target, TargetRef::Chain(l) if l.is_empty())
                                        {
                                            transition_target = Some(end);
                                        }
                                    }
                                }
                            }
                        }
                        _ => body_rels.push(rel),
                    }
                }
                "EndFeatureMembership" => {
                    if matches!(
                        t,
                        "FlowUsage" | "SuccessionFlowUsage" | "Flow" | "SuccessionFlow"
                    ) {
                        if let Some(fe) = self.first_related(rel) {
                            if ty(fe) == "FlowEnd" {
                                // Pilot FlowEnd: ReferenceSubsetting = chain
                                // prefix, owned ReferenceUsage's Redefinition
                                // = last step. (Legacy emissions carried the
                                // whole chain in the subsetting alone.)
                                let mut prefix = None;
                                let mut last = None;
                                for frel in self.owned_rels(fe) {
                                    match ty(frel) {
                                        "ReferenceSubsetting" => {
                                            prefix = self.target(frel, "referencedFeature")
                                        }
                                        "FeatureMembership" => {
                                            if let Some(ru) = self.first_related(frel) {
                                                for rrel in self.owned_rels(ru) {
                                                    if ty(rrel) == "Redefinition" {
                                                        last =
                                                            self.target(rrel, "redefinedFeature");
                                                    }
                                                }
                                            }
                                        }
                                        _ => {}
                                    }
                                }
                                let target = match (prefix, last) {
                                    (prefix, Some(TargetRef::Name(qn))) => {
                                        let mut links = match prefix {
                                            None => Vec::new(),
                                            Some(TargetRef::Name(p)) => vec![p],
                                            Some(TargetRef::Chain(ls)) => ls,
                                        };
                                        if links.is_empty() {
                                            Some(TargetRef::Name(qn))
                                        } else {
                                            links.push(qn);
                                            Some(TargetRef::Chain(links))
                                        }
                                    }
                                    (prefix, _) => prefix,
                                };
                                if let Some(target) = target {
                                    flow_ends.push(FlowEnd { target });
                                }
                                continue;
                            }
                        }
                    }
                    if ends_as_detail {
                        if let Some(end) = self.lift_connector_end(rel) {
                            ends.push(end);
                            continue;
                        }
                    }
                    body_rels.push(rel);
                }
                "ParameterMembership" => params.push(rel),
                "FeatureMembership"
                    if matches!(
                        t,
                        "FlowUsage" | "SuccessionFlowUsage" | "Flow" | "SuccessionFlow"
                    ) && flow_payload.is_none() =>
                {
                    // Payload feature.
                    if let Some(p) = self.first_related(rel) {
                        if ty(p) == "PayloadFeature" {
                            flow_payload = Some(self.lift_payload(p)?);
                            continue;
                        }
                    }
                    body_rels.push(rel);
                }
                "FeatureMembership"
                    if matches!(t, "AcceptActionUsage") && flow_payload.is_none() =>
                {
                    // Accept payload (emitted as a reference feature).
                    if let Some(p) = self.first_related(rel) {
                        flow_payload = Some(self.lift_payload(p)?);
                        continue;
                    }
                    body_rels.push(rel);
                }
                "FeatureMembership" if matches!(t, "ForLoopActionUsage") => {
                    // Loop variable.
                    if let Some(v) = self.first_related(rel) {
                        let lifted = self.lift_usage(v, false)?;
                        transition_effect = Some(Box::new(lifted)); // reuse slot for var
                        continue;
                    }
                    body_rels.push(rel);
                }
                // A plain-name source (`first s1`) rides a Membership; a
                // chain source is handled with the OwningMemberships above.
                "Membership" if matches!(t, "TransitionUsage") && transition_source.is_none() => {
                    transition_source = self.target(rel, "memberElement");
                }
                "TransitionFeatureMembership" => match sval(rel, "kind") {
                    Some("trigger") => {
                        if let Some(acc) = self.first_related(rel) {
                            let lifted = self.lift_usage(acc, false)?;
                            if let UsageDetail::Accept { .. } = lifted.detail {
                                transition_trigger = Some(Box::new(lifted.detail));
                            }
                        }
                    }
                    Some("guard") => {
                        if let Some(g) = self.first_related(rel) {
                            transition_guard = self.lift_expr(g);
                        }
                    }
                    Some("effect") => {
                        if let Some(e) = self.first_related(rel) {
                            transition_effect = self.lift_usage(e, false).map(Box::new);
                        }
                    }
                    _ => {}
                },
                "SubjectMembership" if t == "SatisfyRequirementUsage" => {
                    if let Some(su) = self.first_related(rel) {
                        for srel in self.owned_rels(su) {
                            match ty(srel) {
                                // Pilot SatisfactionFeatureValue: the `by`
                                // target binds as a FeatureValue whose
                                // FeatureReferenceExpression owns a
                                // FeatureChainMember.
                                "FeatureValue" => {
                                    if let Some(fre) = self.first_related(srel) {
                                        if ty(fre) == "FeatureReferenceExpression" {
                                            for frel in self.owned_rels(fre) {
                                                if ty(frel).ends_with("Membership") {
                                                    satisfy_by = self.target(frel, "memberElement");
                                                }
                                            }
                                        }
                                    }
                                }
                                // Legacy emissions carried a subsetting.
                                "ReferenceSubsetting" => {
                                    satisfy_by = self.target(srel, "referencedFeature");
                                }
                                _ => {}
                            }
                        }
                    }
                }
                _ => body_rels.push(rel),
            }
        }

        if !chain_links.is_empty() {
            declaration.chains = Some(if chain_links.len() == 1 {
                chain_links.pop().unwrap()
            } else {
                TargetRef::Chain(
                    chain_links
                        .into_iter()
                        .map(|t| match t {
                            TargetRef::Name(qn) => qn,
                            TargetRef::Chain(mut c) => c.pop().unwrap(),
                        })
                        .collect(),
                )
            });
        }

        // A cross feature is only grammatical on `ref` (or kind-keyword)
        // usages; `isReference` is not serialized, so reconstruct it.
        if prefix.end_cross.is_some() && kind == UsageKind::Default {
            prefix.is_ref = true;
        }

        // Kind-specific details.
        let detail = self.assemble_detail(
            t,
            kind,
            el,
            ends,
            flow_payload,
            flow_ends,
            &params,
            about,
            transition_source,
            transition_trigger,
            transition_guard,
            transition_effect,
            transition_target,
            satisfy_by,
        );

        let saved_body = std::mem::replace(&mut self.body_featuring, featuring);
        let members = self.lift_members(&body_rels);
        self.body_featuring = saved_body;
        Some(Usage {
            prefix,
            kind,
            declaration,
            detail,
            value: value.map(Box::new),
            is_parallel: bval(el, "isParallel"),
            body: if members.is_empty() {
                None
            } else {
                Some(members)
            },
        })
    }

    #[allow(clippy::too_many_arguments)]
    fn assemble_detail(
        &mut self,
        t: &str,
        kind: UsageKind,
        el: El<'a>,
        ends: Vec<ConnectorEnd>,
        flow_payload: Option<PayloadPart>,
        flow_ends: Vec<FlowEnd>,
        params: &[El<'a>],
        about: Vec<QualifiedName>,
        source: Option<TargetRef>,
        trigger: Option<Box<UsageDetail>>,
        guard: Option<Expr>,
        effect: Option<Box<Usage>>,
        target: Option<ConnectorEnd>,
        by: Option<TargetRef>,
    ) -> UsageDetail {
        match kind {
            UsageKind::Connection
            | UsageKind::Allocation
            | UsageKind::Interface
            | UsageKind::Connector
                if !ends.is_empty() =>
            {
                UsageDetail::Connector { ends }
            }
            UsageKind::Binding if ends.len() == 2 => UsageDetail::Binding { ends },
            UsageKind::Binding => {
                // A binding connector binds exactly two ends; any other
                // arity is a partial document — including none at all,
                // which is what a minimally populated payload builds.
                // Keep whatever ends are there visible as a plain
                // connector detail so the text shows what is there, and
                // report the arity either way: the printer's fallback
                // spelling relies on that report having been made.
                self.record(format!(
                    "binding connector {} has {} end(s), expected two",
                    id_of(el),
                    ends.len()
                ));
                UsageDetail::Connector { ends }
            }
            UsageKind::Succession if !ends.is_empty() => {
                let mut ends = ends;
                if ends.len() >= 2 {
                    let target = ends.remove(1);
                    let source = ends.remove(0);
                    // A completely bare source end is the target-succession
                    // shorthand `then x;` (a multiplicity-only source end is
                    // its `then [1] x;` variant, kept in `source`).
                    let source = if source.name.is_none()
                        && source.multiplicity.is_none()
                        && source.target.is_unspelled()
                    {
                        None
                    } else {
                        Some(source)
                    };
                    UsageDetail::Succession {
                        source: source.map(Box::new),
                        target: Box::new(target),
                    }
                } else {
                    UsageDetail::Succession {
                        source: None,
                        target: Box::new(ends.remove(0)),
                    }
                }
            }
            UsageKind::Flow | UsageKind::Message | UsageKind::SuccessionFlow
                if flow_payload.is_some() || !flow_ends.is_empty() =>
            {
                let mut fe = flow_ends;
                let (s, tt) = if fe.len() >= 2 {
                    let t2 = fe.remove(1);
                    let s = fe.remove(0);
                    (Some(s), Some(t2))
                } else {
                    (None, None)
                };
                UsageDetail::Flow {
                    payload: flow_payload.map(Box::new),
                    source: s,
                    target: tt,
                }
            }
            UsageKind::Metadata => UsageDetail::Metadata { about },
            UsageKind::Satisfy => UsageDetail::Satisfy {
                asserted: false,
                negated: bval(el, "isNegated"),
                by,
            },
            UsageKind::AssertConstraint | UsageKind::Invariant => UsageDetail::Assert {
                negated: bval(el, "isNegated"),
            },
            UsageKind::Transition => UsageDetail::Transition {
                source,
                trigger,
                guard: guard.map(Box::new),
                effect,
                target: target.map(Box::new),
                is_default: false,
            },
            UsageKind::Accept => {
                // Payload is a ParameterMembership-owned parameter (legacy
                // emissions used FeatureMembership → flow_payload);
                // trigger/via also arrive as params.
                let mut payload_part = flow_payload;
                let mut trigger_part = None;
                let mut via = None;
                for rel in params {
                    if let Some(inner) = self.first_related(rel) {
                        if ty(inner) == "TriggerInvocationExpression" {
                            let kind = match sval(inner, "kind") {
                                Some("at") => TriggerKind::At,
                                Some("after") => TriggerKind::After,
                                _ => TriggerKind::When,
                            };
                            for arel in self.owned_rels(inner) {
                                if ty(arel) == "ParameterMembership" {
                                    if let Some(ex) = self.first_related(arel) {
                                        if let Some(expr) = self.lift_expr(ex) {
                                            trigger_part = Some(Trigger { kind, expr });
                                        }
                                    }
                                }
                            }
                        } else if let Some(expr) = self.param_value(inner) {
                            via = Some(expr);
                        } else if payload_part.is_none() {
                            payload_part = self.lift_payload(inner);
                        }
                    }
                }
                UsageDetail::Accept {
                    payload: Box::new(payload_part.unwrap_or_default()),
                    trigger: trigger_part.map(Box::new),
                    via: via.map(Box::new),
                }
            }
            UsageKind::Send => {
                let mut slots = params
                    .iter()
                    .map(|rel| {
                        self.first_related(rel)
                            .and_then(|inner| self.param_value(inner))
                    })
                    .collect::<Vec<_>>();
                while slots.len() < 3 {
                    slots.push(None);
                }
                let to = slots.pop().unwrap();
                let via = slots.pop().unwrap();
                let payload = slots.pop().unwrap();
                UsageDetail::Send {
                    payload: payload.map(Box::new),
                    via: via.map(Box::new),
                    to: to.map(Box::new),
                }
            }
            UsageKind::Assign => {
                let mut exprs = Vec::new();
                for rel in params {
                    if let Some(inner) = self.first_related(rel) {
                        if let Some(e) = self.param_value(inner) {
                            exprs.push(e);
                        }
                    }
                }
                if exprs.len() == 2 {
                    let value = exprs.pop().unwrap();
                    let target = exprs.pop().unwrap();
                    UsageDetail::Assign {
                        target: Box::new(target),
                        value: Box::new(value),
                    }
                } else {
                    UsageDetail::None
                }
            }
            UsageKind::Terminate => {
                let mut target = None;
                for rel in params {
                    if target.is_none() {
                        if let Some(inner) = self.first_related(rel) {
                            target = self.param_value(inner);
                        }
                    }
                }
                UsageDetail::Terminate {
                    target: target.map(Box::new),
                }
            }
            UsageKind::IfNode => {
                let mut cond = None;
                let mut bodies: Vec<Usage> = Vec::new();
                for rel in params {
                    if let Some(inner) = self.first_related(rel) {
                        if matches!(ty(inner), "ActionUsage" | "IfActionUsage") {
                            if let Some(u) = self.lift_usage(inner, false) {
                                bodies.push(u);
                            }
                        } else if cond.is_none() {
                            cond = self.param_value(inner).or_else(|| self.lift_expr(inner));
                        }
                    }
                }
                let then_body = if bodies.is_empty() {
                    return UsageDetail::None;
                } else {
                    Box::new(bodies.remove(0))
                };
                UsageDetail::IfNode {
                    cond: Box::new(cond.unwrap_or_else(|| Expr {
                        kind: ExprKind::Null,
                        span: Span::default(),
                    })),
                    then_body,
                    else_body: if bodies.is_empty() {
                        None
                    } else {
                        Some(Box::new(bodies.remove(0)))
                    },
                }
            }
            UsageKind::WhileLoop => {
                let mut cond = None;
                let mut until = None;
                let mut body = None;
                for rel in params {
                    if let Some(inner) = self.first_related(rel) {
                        if ty(inner) == "ActionUsage" {
                            body = self.lift_usage(inner, false).map(Box::new);
                        } else if let Some(expr) =
                            self.param_value(inner).or_else(|| self.lift_expr(inner))
                        {
                            if body.is_none() {
                                cond = Some(expr);
                            } else {
                                until = Some(expr);
                            }
                        }
                    }
                }
                match body {
                    Some(body) => UsageDetail::WhileLoop {
                        cond: cond.map(Box::new),
                        body,
                        until: until.map(Box::new),
                    },
                    None => UsageDetail::None,
                }
            }
            UsageKind::ForLoop => {
                // Loop variable was stashed in `effect` by the caller.
                let var = effect.map(|u| u.declaration).unwrap_or_default();
                let mut seq = None;
                let mut body = None;
                for rel in params {
                    if let Some(inner) = self.first_related(rel) {
                        if ty(inner) == "ActionUsage" {
                            body = self.lift_usage(inner, false).map(Box::new);
                        } else if seq.is_none() {
                            seq = self.param_value(inner).or_else(|| self.lift_expr(inner));
                        }
                    }
                }
                match (seq, body) {
                    (Some(seq), Some(body)) => UsageDetail::ForLoop {
                        var: Box::new(var),
                        seq: Box::new(seq),
                        body,
                    },
                    _ => UsageDetail::None,
                }
            }
            _ if t == "OccurrenceUsage" => UsageDetail::None,
            _ => UsageDetail::None,
        }
    }

    /// The expression bound as a parameter's FeatureValue.
    fn param_value(&mut self, param_el: El<'a>) -> Option<Expr> {
        for rel in self.owned_rels(param_el) {
            if ty(rel) == "FeatureValue" {
                if let Some(ex) = self.first_related(rel) {
                    return self.lift_expr(ex);
                }
            }
        }
        None
    }

    /// Is this end membership a bare connector-part end (exactly what the
    /// emitter produces for `connect a to b` ends)?
    fn is_bare_end(&self, rel: El<'a>) -> bool {
        let Some(el) = self.first_related(rel) else {
            return false;
        };
        if !matches!(ty(el), "ReferenceUsage" | "Feature" | "PortUsage") {
            return false;
        }
        let rels = self.owned_rels(el);
        // A connector end always references its connected feature.
        rels.iter().any(|r| ty(r) == "ReferenceSubsetting")
            && rels.iter().all(|r| match ty(r) {
                "ReferenceSubsetting" => true,
                "OwningMembership" => self
                    .first_related(r)
                    .map(|inner| ty(inner) == "MultiplicityRange")
                    .unwrap_or(false),
                _ => false,
            })
    }

    /// Is this end membership a completely bare end feature — no reference,
    /// no multiplicity, no name (the pilot's EmptySourceEnd / EmptyTargetEnd
    /// rules, and MultiplicitySourceEnd with nothing spelled)?
    fn is_empty_end(&self, rel: El<'a>) -> bool {
        self.first_related(rel).is_some_and(|el| {
            matches!(ty(el), "ReferenceUsage" | "Feature")
                && Self::declared_name(el).is_none()
                && self.owned_rels(el).is_empty()
        })
    }

    /// A succession source end the text leaves unspelled: no reference, no
    /// declared name, at most an owned multiplicity (`then x;` /
    /// `then [1] x;`).
    fn is_unreferenced_end(&self, rel: El<'a>) -> bool {
        let Some(el) = self.first_related(rel) else {
            return false;
        };
        if !matches!(ty(el), "ReferenceUsage" | "Feature") || Self::declared_name(el).is_some() {
            return false;
        }
        self.owned_rels(el).iter().all(|r| {
            ty(r) == "OwningMembership"
                && self
                    .first_related(r)
                    .is_some_and(|inner| ty(inner) == "MultiplicityRange")
        })
    }

    fn lift_connector_end(&mut self, rel: El<'a>) -> Option<ConnectorEnd> {
        let el = self.first_related(rel)?;
        let mut multiplicity = None;
        let mut target = None;
        for r in self.owned_rels(el) {
            match ty(r) {
                "OwningMembership" => {
                    if let Some(inner) = self.first_related(r) {
                        if ty(inner) == "MultiplicityRange" {
                            let bounds = self.range_bounds(inner);
                            multiplicity = self.bounds_to_multiplicity(bounds);
                        }
                    }
                }
                "ReferenceSubsetting" => target = self.target(r, "referencedFeature"),
                _ => {}
            }
        }
        Some(ConnectorEnd {
            multiplicity,
            name: sval(el, "declaredName").map(name),
            target: target.unwrap_or_else(TargetRef::unspelled),
        })
    }

    /// A ConjugatedPortTyping's target is the implicit
    /// ConjugatedPortDefinition (`Pkg::P::'~P'`); the `~` in the text
    /// spells the conjugation, so the reference prints the original port
    /// definition — drop the trailing `~`-named segment.
    fn unconjugate(is_conjugated: bool, target: TargetRef) -> TargetRef {
        if !is_conjugated {
            return target;
        }
        match target {
            TargetRef::Name(mut qn)
                if qn.segments.len() > 1
                    && qn.segments.last().is_some_and(|s| s.value.starts_with('~')) =>
            {
                qn.segments.pop();
                TargetRef::Name(qn)
            }
            other => other,
        }
    }

    fn lift_payload(&mut self, el: El<'a>) -> Option<PayloadPart> {
        let mut payload = PayloadPart {
            id: Self::identification(el),
            is_ordered: bval(el, "isOrdered"),
            is_nonunique: el
                .get("isUnique")
                .and_then(Value::as_bool)
                .is_some_and(|unique| !unique),
            ..Default::default()
        };
        for rel in self.owned_rels(el) {
            match ty(rel) {
                "FeatureTyping" | "ConjugatedPortTyping" => {
                    if let Some(target) = self.target(rel, "type") {
                        let is_conjugated = ty(rel) == "ConjugatedPortTyping";
                        payload
                            .specializations
                            .push(FeatureSpecialization::TypedBy(vec![TypeRef {
                                target: Self::unconjugate(is_conjugated, target),
                                is_conjugated,
                            }]));
                    }
                }
                "Subsetting" => {
                    if let Some(t) = self.target(rel, "subsettedFeature") {
                        payload
                            .specializations
                            .push(FeatureSpecialization::Subsets(vec![t]));
                    }
                }
                "Redefinition" => {
                    if let Some(t) = self.target(rel, "redefinedFeature") {
                        payload
                            .specializations
                            .push(FeatureSpecialization::Redefines(vec![t]));
                    }
                }
                "OwningMembership" => {
                    if let Some(inner) = self.first_related(rel) {
                        if ty(inner) == "MultiplicityRange" {
                            let bounds = self.range_bounds(inner);
                            payload.multiplicity = self.bounds_to_multiplicity(bounds);
                        }
                    }
                }
                "FeatureValue" => {
                    if let Some(ex) = self.first_related(rel) {
                        if let Some(expr) = self.lift_expr(ex) {
                            payload.value = Some(Box::new(FeatureValue {
                                kind: ValueKind::Bound,
                                expr,
                            }));
                        }
                    }
                }
                _ => {}
            }
        }
        Some(payload)
    }

    // ---- expressions ----

    fn lift_expr(&mut self, el: El<'a>) -> Option<Expr> {
        // Postorder on an explicit work stack: even a left-associated
        // operator chain consumes no recursive lift frames. Each occurrence
        // is evaluated separately, so shared payload operands keep their
        // position without cloning an ever-growing expression subtree.
        enum Work<'a> {
            Enter(El<'a>, usize),
            Finish(El<'a>, usize),
        }
        let mut work = vec![Work::Enter(el, 0)];
        let mut values = Vec::new();
        while let Some(step) = work.pop() {
            match step {
                Work::Enter(el, depth) => {
                    let id = id_of(el);
                    if depth >= MAX_LIFT_EXPR_DEPTH {
                        self.incomplete = true;
                        self.record(format!(
                            "expression nesting deeper than {MAX_LIFT_EXPR_DEPTH} at {id}"
                        ));
                        values.push(None);
                        continue;
                    }
                    if !self.in_progress.insert(id) {
                        self.incomplete = true;
                        self.record(format!("ownership cycle through {id}"));
                        values.push(None);
                        continue;
                    }
                    let children = self.expression_children(el);
                    work.push(Work::Finish(el, children.len()));
                    work.extend(
                        children
                            .into_iter()
                            .rev()
                            .map(|child| Work::Enter(child, depth + 1)),
                    );
                }
                Work::Finish(el, count) => {
                    let children = values.split_off(values.len() - count);
                    let missing = children.iter().any(Option::is_none);
                    let implicit_subject = ty(el) == "OperatorExpression"
                        && matches!(
                            sval(el, "operator"),
                            Some("istype" | "hastype" | "@" | "@@" | "as" | "meta")
                        );
                    let expr = if missing && !implicit_subject {
                        None
                    } else {
                        self.lift_expr_inner(el, &mut children.into_iter())
                    };
                    // An implicit subject is the one intentional empty
                    // expression: classification operators read it as self.
                    let self_reference = ty(el) == "FeatureReferenceExpression"
                        && self
                            .owned_rels(el)
                            .iter()
                            .any(|r| ty(r) == "ReturnParameterMembership");
                    if expr.is_none() && !self_reference && !self.incomplete {
                        self.incomplete = true;
                        self.record(format!(
                            "cannot lift expression {} at {}",
                            ty(el),
                            id_of(el)
                        ));
                    }
                    self.in_progress.remove(id_of(el));
                    values.push(expr);
                }
            }
        }
        values.pop().flatten()
    }

    /// Children in precisely the order the expression assembler consumes
    /// them. Parameter wrappers and type-reference parameters add no AST
    /// depth. An expression body goes through the bounded member lifter.
    fn expression_children(&mut self, el: El<'a>) -> Vec<El<'a>> {
        match ty(el) {
            "FeatureReferenceExpression" => {
                for rel in self.owned_rels(el) {
                    if ty(rel) == "ReturnParameterMembership" {
                        continue;
                    }
                    if self.target(rel, "memberElement").is_some() {
                        break;
                    }
                    if let Some(inner) = self.first_related(rel) {
                        return vec![inner];
                    }
                }
                Vec::new()
            }
            "FeatureChainExpression"
            | "IndexExpression"
            | "CollectExpression"
            | "SelectExpression"
            | "InvocationExpression"
            | "ConstructorExpression"
            | "OperatorExpression" => self
                .owned_rels(el)
                .into_iter()
                .filter(|rel| ty(rel) == "ParameterMembership")
                .filter_map(|rel| self.param_expr_el(rel))
                .collect(),
            _ => Vec::new(),
        }
    }

    fn lift_expr_inner(
        &mut self,
        el: El<'a>,
        children: &mut std::vec::IntoIter<Option<Expr>>,
    ) -> Option<Expr> {
        let mk = |kind: ExprKind| {
            Some(Expr {
                kind,
                span: Span::default(),
            })
        };
        match ty(el) {
            "LiteralBoolean" => mk(ExprKind::Literal(Literal::Bool(bval(el, "value")))),
            "LiteralString" => mk(ExprKind::Literal(Literal::String(
                sval(el, "value").unwrap_or("").to_string(),
            ))),
            "LiteralInteger" => {
                let raw = match el.get("value") {
                    Some(Value::Number(n)) => n.to_string(),
                    Some(Value::String(s)) => s.clone(),
                    _ => "0".to_string(),
                };
                mk(ExprKind::Literal(Literal::Integer(raw)))
            }
            "LiteralRational" => {
                // A real literal must contain a fraction or exponent.
                // The value is a JSON number when a double denotes it
                // exactly and the written text otherwise (a decimal with
                // more digits than a double holds, an exponent past its
                // range); both spellings read back the same way.
                // The fraction is appended only to a written whole
                // number. A value the payload spells some other way — a
                // rational's `1/3`, say — is kept verbatim: appending to
                // it changes what it denotes, and `1/3.0` reads back as a
                // division by a different number.
                let whole = |s: &str| {
                    let digits = s.strip_prefix(['+', '-']).unwrap_or(s);
                    !digits.is_empty() && digits.bytes().all(|b| b.is_ascii_digit())
                };
                let real = |s: &str| {
                    if whole(s) {
                        format!("{s}.0")
                    } else {
                        s.to_string()
                    }
                };
                let raw = match el.get("value") {
                    Some(Value::Number(n)) => real(&n.to_string()),
                    Some(Value::String(s)) => real(s),
                    _ => "0.0".to_string(),
                };
                mk(ExprKind::Literal(Literal::Real(raw)))
            }
            "LiteralInfinity" => mk(ExprKind::Literal(Literal::Infinity)),
            "NullExpression" => mk(ExprKind::Null),
            "FeatureReferenceExpression" => {
                for rel in self.owned_rels(el) {
                    // A self-reference (`istype T` with no left side): a
                    // return-parameter member owning an empty feature.
                    if ty(rel) == "ReturnParameterMembership" {
                        continue;
                    }
                    if let Some(target) = self.target(rel, "memberElement") {
                        return Some(target_to_expr(target));
                    }
                    // Nested expression member (lazy operand wrapper).
                    if self.first_related(rel).is_some() {
                        return children.next().flatten();
                    }
                }
                None
            }
            "MetadataAccessExpression" => {
                for rel in self.owned_rels(el) {
                    if let Some(TargetRef::Name(qn)) = self.target(rel, "memberElement") {
                        return mk(ExprKind::MetadataAccess { target: qn });
                    }
                }
                None
            }
            "FeatureChainExpression" => {
                let mut target_expr = None;
                let mut member = None;
                for rel in self.owned_rels(el) {
                    match ty(rel) {
                        "ParameterMembership" => {
                            if self.param_expr_el(rel).is_some() {
                                target_expr = children.next().flatten();
                            }
                        }
                        "Membership" | "OwningMembership" => {
                            member = self.target(rel, "memberElement");
                        }
                        _ => {}
                    }
                }
                mk(ExprKind::ChainStep {
                    target: Box::new(target_expr?),
                    member: member?,
                })
            }
            "IndexExpression" => {
                let ops = children.by_ref().flatten().collect::<Vec<_>>();
                let mut it = ops.into_iter();
                mk(ExprKind::Index {
                    target: Box::new(it.next()?),
                    index: Box::new(it.next()?),
                })
            }
            "CollectExpression" | "SelectExpression" => {
                let is_select = ty(el) == "SelectExpression";
                let ops = children.by_ref().flatten().collect::<Vec<_>>();
                let mut it = ops.into_iter();
                let target = Box::new(it.next()?);
                let body = Box::new(it.next()?);
                if is_select {
                    mk(ExprKind::Select { target, body })
                } else {
                    mk(ExprKind::Collect { target, body })
                }
            }
            "InvocationExpression" | "ConstructorExpression" => {
                let mut fn_ty = None;
                let mut fnref = None;
                let mut args = Vec::new();
                for rel in self.owned_rels(el) {
                    match ty(rel) {
                        // A chained callee (`a.b(x)`) rides an
                        // OwningMembership owning the chain feature.
                        "Membership" | "OwningMembership" => {
                            fn_ty = self.target(rel, "memberElement")
                        }
                        "FeatureMembership" => {
                            fnref = self.target(rel, "memberElement").and_then(|t| match t {
                                TargetRef::Name(qn) => Some(qn),
                                _ => None,
                            });
                        }
                        "ParameterMembership" => {
                            // Named arguments carry a ParameterRedefinition
                            // of the callee's parameter inside the argument
                            // Feature (pilot NamedArgument); legacy
                            // emissions spelled the name as `memberName`.
                            // The full form materializes a *derived*
                            // `memberName` on positional arguments too (the
                            // argument feature's effective name via its
                            // implied parameter redefinition) — there the
                            // derived `ownedMemberName` rides along, so its
                            // presence disqualifies the legacy spelling.
                            let mut arg_name = if rel.get("ownedMemberName").is_none() {
                                sval(rel, "memberName").map(|s| {
                                    qn_from_segments(
                                        &s.split("::").map(|x| x.to_string()).collect::<Vec<_>>(),
                                    )
                                })
                            } else {
                                None
                            };
                            if arg_name.is_none() {
                                if let Some(f) = self.first_related(rel) {
                                    for frel in self.owned_rels(f) {
                                        if ty(frel) == "Redefinition" {
                                            if let Some(TargetRef::Name(qn)) =
                                                self.target(frel, "redefinedFeature")
                                            {
                                                arg_name = Some(qn);
                                            }
                                        }
                                    }
                                }
                            }
                            if self.param_expr_el(rel).is_some() {
                                if let Some(value) = children.next().flatten() {
                                    args.push(Arg {
                                        name: arg_name,
                                        value,
                                    });
                                }
                            }
                        }
                        "ReturnParameterMembership" => {}
                        _ => {}
                    }
                }
                let ty_target = fn_ty?;
                if ty(el) == "ConstructorExpression" {
                    return mk(ExprKind::Constructor {
                        ty: Box::new(ty_target),
                        args,
                    });
                }
                if let Some(f) = fnref {
                    // Arrow with function reference: first arg is the target.
                    let mut it = args.into_iter();
                    let target = it.next()?.value;
                    return mk(ExprKind::Arrow {
                        target: Box::new(target),
                        ty: Box::new(ty_target),
                        args: ArrowArgs::FunctionRef(f),
                    });
                }
                mk(ExprKind::Invocation {
                    ty: Box::new(ty_target),
                    args,
                })
            }
            "OperatorExpression" => self.lift_operator_expr(el, children),
            "Expression" => {
                let rels = self.owned_rels(el);
                let members = self.lift_members(&rels);
                mk(ExprKind::Body { members })
            }
            other => {
                self.record(format!("unsupported expression @type {other}"));
                None
            }
        }
    }

    fn lift_operator_expr(
        &mut self,
        el: El<'a>,
        children: &mut std::vec::IntoIter<Option<Expr>>,
    ) -> Option<Expr> {
        let op = sval(el, "operator").unwrap_or("");
        let mk = |kind: ExprKind| {
            Some(Expr {
                kind,
                span: Span::default(),
            })
        };
        // Type-reference member for classification / extent operators:
        // an owned parameter Feature with a FeatureTyping (pilot
        // `TypeReferenceMember` / `TypeResultMember`); `memberElement`
        // reference spellings are accepted for foreign payloads.
        let mut ty_target = None;
        for rel in self.owned_rels(el) {
            if !matches!(ty(rel), "ParameterMembership" | "ReturnParameterMembership") {
                continue;
            }
            if let Some(kid) = self.first_related(rel) {
                if !is_expr_type(ty(kid)) {
                    for r in self.owned_rels(kid) {
                        if ty(r) == "FeatureTyping" {
                            ty_target = self.target(r, "type");
                        }
                    }
                }
            } else if rel.get("memberElement").is_some() {
                // Reference spelling only counts when the membership owns
                // nothing — the full form materializes the derived
                // `memberElement` on owning memberships too, where it names
                // the anonymous parameter Feature, not the type.
                ty_target = self.target(rel, "memberElement");
            }
        }
        let ops = children.by_ref().flatten().collect::<Vec<_>>();

        if op == "if" {
            let mut it = ops.into_iter();
            return mk(ExprKind::Conditional {
                cond: Box::new(it.next()?),
                then_branch: Box::new(it.next()?),
                else_branch: Box::new(it.next()?),
            });
        }
        if op == "," {
            return mk(ExprKind::Sequence(ops));
        }
        if op == "all" {
            return mk(ExprKind::Extent {
                ty: Box::new(ty_target?),
            });
        }
        if op == "[" {
            let mut it = ops.into_iter();
            return mk(ExprKind::Bracket {
                target: Box::new(it.next()?),
                arg: Box::new(it.next()?),
            });
        }
        let class_op = match op {
            "istype" => Some(ClassificationOp::IsType),
            "hastype" => Some(ClassificationOp::HasType),
            "@" => Some(ClassificationOp::AtType),
            "@@" => Some(ClassificationOp::MetaAtType),
            "as" => Some(ClassificationOp::As),
            "meta" => Some(ClassificationOp::Meta),
            _ => None,
        };
        if let Some(cop) = class_op {
            let operand = ops
                .into_iter()
                .next()
                .map(|e| match e.kind {
                    // `x meta T`: the left side serializes as a
                    // MetadataAccessExpression — print it as the name.
                    ExprKind::MetadataAccess { target } => Expr {
                        kind: ExprKind::Ref(target),
                        span: Span::default(),
                    },
                    _ => e,
                })
                .map(Box::new);
            return mk(ExprKind::Classification {
                op: cop,
                operand,
                ty: Box::new(ty_target?),
            });
        }
        if ops.len() == 1 {
            let uop = match op {
                "+" => Some(UnaryOp::Plus),
                "-" => Some(UnaryOp::Minus),
                "~" => Some(UnaryOp::Tilde),
                "not" => Some(UnaryOp::Not),
                _ => None,
            };
            if let Some(uop) = uop {
                return mk(ExprKind::Unary {
                    op: uop,
                    operand: Box::new(ops.into_iter().next().unwrap()),
                });
            }
        }
        let bop = match op {
            "??" => BinaryOp::NullCoalescing,
            "implies" => BinaryOp::Implies,
            "|" => BinaryOp::OrBar,
            "or" => BinaryOp::CondOr,
            "xor" => BinaryOp::Xor,
            "&" => BinaryOp::AndAmp,
            "and" => BinaryOp::CondAnd,
            "==" => BinaryOp::Eq,
            "!=" => BinaryOp::NotEq,
            "===" => BinaryOp::Same,
            "!==" => BinaryOp::NotSame,
            "<" => BinaryOp::Lt,
            ">" => BinaryOp::Gt,
            "<=" => BinaryOp::LtEq,
            ">=" => BinaryOp::GtEq,
            ".." => BinaryOp::Range,
            "+" => BinaryOp::Add,
            "-" => BinaryOp::Sub,
            "*" => BinaryOp::Mul,
            "/" => BinaryOp::Div,
            "%" => BinaryOp::Rem,
            "**" => BinaryOp::Pow,
            "^" => BinaryOp::Caret,
            other => {
                self.record(format!("unknown operator {other:?}"));
                return None;
            }
        };
        let mut it = ops.into_iter();
        mk(ExprKind::Binary {
            op: bop,
            lhs: Box::new(it.next()?),
            rhs: Box::new(it.next()?),
        })
    }
}

fn target_to_expr(target: TargetRef) -> Expr {
    match target {
        TargetRef::Name(qn) => Expr {
            span: Span::default(),
            kind: ExprKind::Ref(qn),
        },
        TargetRef::Chain(links) => {
            let mut iter = links.into_iter();
            let first = iter.next().unwrap_or_else(|| qn_from_segments(&[]));
            let mut expr = Expr {
                span: Span::default(),
                kind: ExprKind::Ref(first),
            };
            for link in iter {
                expr = Expr {
                    span: Span::default(),
                    kind: ExprKind::ChainStep {
                        target: Box::new(expr),
                        member: TargetRef::Name(link),
                    },
                };
            }
            expr
        }
    }
}

pub(crate) fn def_kind_of(t: &str) -> Option<DefKind> {
    Some(match t {
        "AttributeDefinition" => DefKind::Attribute,
        "EnumerationDefinition" => DefKind::Enum,
        "OccurrenceDefinition" => DefKind::Occurrence,
        "ItemDefinition" => DefKind::Item,
        "MetadataDefinition" => DefKind::Metadata,
        "PartDefinition" => DefKind::Part,
        "PortDefinition" => DefKind::Port,
        "ConnectionDefinition" => DefKind::Connection,
        "InterfaceDefinition" => DefKind::Interface,
        "AllocationDefinition" => DefKind::Allocation,
        "FlowDefinition" => DefKind::Flow,
        "ActionDefinition" => DefKind::Action,
        "StateDefinition" => DefKind::State,
        "CalculationDefinition" => DefKind::Calc,
        "ConstraintDefinition" => DefKind::Constraint,
        "RequirementDefinition" => DefKind::Requirement,
        "ConcernDefinition" => DefKind::Concern,
        "CaseDefinition" => DefKind::Case,
        "AnalysisCaseDefinition" => DefKind::Analysis,
        "VerificationCaseDefinition" => DefKind::Verification,
        "UseCaseDefinition" => DefKind::UseCase,
        "ViewDefinition" => DefKind::View,
        "ViewpointDefinition" => DefKind::Viewpoint,
        "RenderingDefinition" => DefKind::Rendering,
        "Definition" => DefKind::Extended,
        "Type" => DefKind::Type,
        "Classifier" => DefKind::Classifier,
        "Class" => DefKind::Class,
        "Structure" => DefKind::Struct,
        "DataType" => DefKind::DataType,
        "Association" => DefKind::Assoc,
        "AssociationStructure" => DefKind::AssocStruct,
        "Behavior" => DefKind::Behavior,
        "Interaction" => DefKind::Interaction,
        "Function" => DefKind::Function,
        "Predicate" => DefKind::Predicate,
        "Metaclass" => DefKind::Metaclass,
        _ => return None,
    })
}

pub(crate) fn usage_kind_of(t: &str, dialect: Dialect) -> Option<UsageKind> {
    Some(match t {
        "AttributeUsage" => UsageKind::Attribute,
        "EnumerationUsage" => UsageKind::Enum,
        "OccurrenceUsage" => UsageKind::Occurrence,
        "ItemUsage" => UsageKind::Item,
        "MetadataUsage" | "MetadataFeature" => UsageKind::Metadata,
        "PartUsage" => UsageKind::Part,
        "PortUsage" => UsageKind::Port,
        "ConnectionUsage" => UsageKind::Connection,
        "InterfaceUsage" => UsageKind::Interface,
        "AllocationUsage" => UsageKind::Allocation,
        "FlowUsage" => UsageKind::Flow,
        "ActionUsage" => UsageKind::Action,
        "StateUsage" => UsageKind::State,
        "CalculationUsage" => UsageKind::Calc,
        "ConstraintUsage" => UsageKind::Constraint,
        "RequirementUsage" => UsageKind::Requirement,
        "ConcernUsage" => UsageKind::Concern,
        "CaseUsage" => UsageKind::Case,
        "AnalysisCaseUsage" => UsageKind::Analysis,
        "VerificationCaseUsage" => UsageKind::Verification,
        "UseCaseUsage" => UsageKind::UseCase,
        "ViewUsage" => UsageKind::View,
        "ViewpointUsage" => UsageKind::Viewpoint,
        "RenderingUsage" => UsageKind::Rendering,
        "ReferenceUsage" => UsageKind::Default,
        "Usage" => UsageKind::Extended,
        "PerformActionUsage" => UsageKind::Perform,
        "ExhibitStateUsage" => UsageKind::Exhibit,
        "IncludeUseCaseUsage" => UsageKind::Include,
        "EventOccurrenceUsage" => UsageKind::Event,
        "SatisfyRequirementUsage" => UsageKind::Satisfy,
        "AssertConstraintUsage" => UsageKind::AssertConstraint,
        "SuccessionAsUsage" | "Succession" => UsageKind::Succession,
        "SuccessionFlowUsage" | "SuccessionFlow" => UsageKind::SuccessionFlow,
        "BindingConnectorAsUsage" | "BindingConnector" => UsageKind::Binding,
        "TransitionUsage" => UsageKind::Transition,
        "MergeNode" => UsageKind::Merge,
        "DecisionNode" => UsageKind::Decide,
        "JoinNode" => UsageKind::Join,
        "ForkNode" => UsageKind::Fork,
        "AcceptActionUsage" => UsageKind::Accept,
        "SendActionUsage" => UsageKind::Send,
        "AssignmentActionUsage" => UsageKind::Assign,
        "TerminateActionUsage" => UsageKind::Terminate,
        "IfActionUsage" => UsageKind::IfNode,
        "WhileLoopActionUsage" => UsageKind::WhileLoop,
        "ForLoopActionUsage" => UsageKind::ForLoop,
        "Feature" => UsageKind::Feature,
        "Step" => UsageKind::Step,
        "BooleanExpression" => UsageKind::BoolExpr,
        "Invariant" => UsageKind::Invariant,
        "Connector" => UsageKind::Connector,
        "Flow" => UsageKind::Flow,
        "PayloadFeature" => UsageKind::Default,
        "Expression" if dialect == Dialect::Kerml => UsageKind::Expr,
        _ => return None,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A chain of `depth` parts, each owned by the one above through a
    /// membership: the shape whose ownership pointers the lift follows.
    fn chain(depth: usize) -> Vec<Value> {
        chain_named("", depth)
    }

    /// The same chain with every id under `prefix`, so two of them are
    /// independent subtrees of one payload.
    ///
    /// Ownership is spelled both ways round, as a payload spells it: the
    /// chain then has the one root it reads as, rather than as many roots
    /// as it has elements.
    fn chain_named(prefix: &str, depth: usize) -> Vec<Value> {
        let mut items = Vec::new();
        for i in 0..depth {
            let mut membership = serde_json::json!({
                "@id": format!("{prefix}m{i}"),
                "@type": "OwningMembership",
                "ownedRelatedElement": [{ "@id": format!("{prefix}p{i}") }],
            });
            if i > 0 {
                membership["owningRelatedElement"] =
                    serde_json::json!({ "@id": format!("{prefix}p{}", i - 1) });
            }
            items.push(membership);
            let owned = if i + 1 < depth {
                serde_json::json!([{ "@id": format!("{prefix}m{}", i + 1) }])
            } else {
                serde_json::json!([])
            };
            items.push(serde_json::json!({
                "@id": format!("{prefix}p{i}"),
                "@type": "PartUsage",
                "declaredName": format!("{prefix}p{i}"),
                "owningRelationship": { "@id": format!("{prefix}m{i}") },
                "ownedRelationship": owned,
            }));
        }
        items
    }

    /// The decision that keeps a small document off a thread of its own
    /// reads the payload's depth, not its size: a wide document stays in
    /// place however many elements it holds, and a deep one does not.
    #[test]
    fn the_in_place_decision_follows_the_payload_depth() {
        // Two steps per level, so the chain crosses the bound at half of
        // it.
        assert!(!nests_deeper_than(&chain(4), IN_PLACE_DEPTH));
        assert!(nests_deeper_than(&chain(IN_PLACE_DEPTH), IN_PLACE_DEPTH));

        // Many siblings under one owner is one level, whatever the count.
        let mut wide = vec![serde_json::json!({
            "@id": "root",
            "@type": "Namespace",
            "ownedRelationship": (0..500)
                .map(|i| serde_json::json!({ "@id": format!("m{i}") }))
                .collect::<Vec<_>>(),
        })];
        for i in 0..500 {
            wide.push(serde_json::json!({
                "@id": format!("m{i}"),
                "@type": "OwningMembership",
                "ownedRelatedElement": [],
            }));
        }
        assert!(!nests_deeper_than(&wide, IN_PLACE_DEPTH));

        // A payload whose ownership is not a forest takes the stack the
        // lift's own guards need to report it.
        let cycle = vec![
            serde_json::json!({
                "@id": "a", "@type": "OwningMembership",
                "ownedRelatedElement": [{ "@id": "b" }],
            }),
            serde_json::json!({
                "@id": "b", "@type": "PartUsage",
                "ownedRelationship": [{ "@id": "a" }],
            }),
        ];
        assert!(nests_deeper_than(&cycle, 1));
    }

    /// The deepest payload the lift takes in place fits the smallest
    /// stack an ordinary caller runs on: a worker thread given one
    /// megabyte. Overflowing here would end the process rather than
    /// report anything, so the bound is measured by lifting that payload
    /// on such a thread — in an unoptimized build, where a step costs the
    /// most.
    #[test]
    fn the_deepest_in_place_payload_fits_a_small_stack() {
        // Two steps per level of nesting, so the deepest chain taken in
        // place is half the step bound.
        let items = chain(IN_PLACE_DEPTH / 2);
        assert!(!nests_deeper_than(&items, IN_PLACE_DEPTH));
        let lifted = std::thread::Builder::new()
            .stack_size(1 << 20)
            .spawn(move || from_compact_json(&Value::Array(items)))
            .unwrap()
            .join()
            .unwrap()
            .expect("a well-formed payload lifts");
        assert!(lifted.errors.is_empty(), "{:?}", lifted.errors);
    }

    /// A payload nesting past the bound is reported rather than followed,
    /// and reported once however far past it goes.
    #[test]
    fn nesting_past_the_bound_is_reported_once() {
        let Err(LiftError::Incomplete { errors }) =
            from_compact_json(&Value::Array(chain(MAX_LIFT_DEPTH * 2)))
        else {
            panic!("an over-budget document must not return a partial AST")
        };
        assert_eq!(
            errors
                .iter()
                .filter(|e| e.contains("ownership nesting deeper than"))
                .count(),
            1,
            "{:?}",
            errors
        );
    }

    /// Each truncated subtree is reported: two independent chains past the
    /// bound lose their elements at two different places, and a reader
    /// given one entry would take the other loss for elements the payload
    /// never held.
    #[test]
    fn every_truncated_subtree_is_reported() {
        let mut items = chain_named("a", MAX_LIFT_DEPTH * 2);
        items.extend(chain_named("b", MAX_LIFT_DEPTH * 2));
        let Err(LiftError::Incomplete { errors }) = from_compact_json(&Value::Array(items)) else {
            panic!("an over-budget document must not return a partial AST")
        };
        let reports: Vec<&String> = errors
            .iter()
            .filter(|e| e.contains("ownership nesting deeper than"))
            .collect();
        assert_eq!(reports.len(), 2, "{:?}", errors);
        assert!(
            reports.iter().any(|e| e.contains(" at am"))
                && reports.iter().any(|e| e.contains(" at bm")),
            "{reports:?}"
        );
    }

    /// A binding connector with no ends at all is as much a partial
    /// document as one with three, and it is what a minimally populated
    /// payload builds. Its arity is reported, and the usage keeps the
    /// plain connector detail the notation can still spell — a bare
    /// binding has no spelling of its own.
    #[test]
    fn a_binding_with_no_ends_is_reported() {
        let items = vec![
            serde_json::json!({
                "@id": "m0",
                "@type": "OwningMembership",
                "ownedRelatedElement": [{ "@id": "b0" }],
            }),
            serde_json::json!({
                "@id": "b0",
                "@type": "BindingConnectorAsUsage",
                "owningRelationship": { "@id": "m0" },
                "ownedRelationship": [],
            }),
        ];
        let lifted = from_compact_json(&Value::Array(items)).expect("a well-formed payload lifts");
        assert!(
            lifted
                .errors
                .iter()
                .any(|e| e.contains("binding connector b0 has 0 end(s), expected two")),
            "{:?}",
            lifted.errors
        );
        let sysmlv2_syntax::ast::MemberKind::Usage(u) = &lifted.unit.members[0].kind else {
            panic!("expected a usage: {:#?}", lifted.unit.members[0].kind)
        };
        assert!(
            matches!(&u.detail, UsageDetail::Connector { ends } if ends.is_empty()),
            "{:?}",
            u.detail
        );
    }
}
