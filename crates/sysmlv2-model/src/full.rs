//! Full-form JSON serialization (KerML 10.4 with `includesDerived` /
//! `includesImplied`): the compact element graph plus materialized **implied
//! relationships** (SysML 8.4.2 Tables 31/32 kind→library-base, with the
//! anti-redundancy rule) and **derived properties** for every metaclass.
//!
//! Property completeness is guaranteed by the schema-generated catalog
//! (`schema_props.rs`): every property of the published `SysML.json` schema
//! is present — computed from the graph where the derivation is structural
//! (ownership, names, memberships, features, kind-filtered lists,
//! relationship endpoints), or a type-correct empty value otherwise.
//! Partially-derived properties (notably `inheritedMembership` /
//! `inheritedFeature` and import closures) are emitted empty — the
//! "passthrough" conformance level of the Systems Modeling API — and are
//! called out in the README.

use crate::json::model_to_compact_json;
use crate::json::{CLOSURE_NAMES, ClosurePolicy};
use crate::lift::usage_kind_of;
use crate::metaclass::conforms;
use crate::model::Model;
use crate::schema_props::METACLASS_PROPS;
use serde_json::{Map, Value, json};
use std::collections::HashMap;
use sysmlv2_syntax::ast::{Dialect, SourceUnit};
use uuid::Uuid;

/// How full-form interchange handles compact `{"@ref": ...}` values. The
/// published full schema permits only `@id` references, so preserving a
/// partial model requires schema-valid textual recovery annotations.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Default)]
pub enum UnresolvedReferencePolicy {
    /// Emit deterministic recovery annotations. This is the default and is
    /// lossless when lifted by this toolkit.
    #[default]
    Preserve,
    /// Refuse full-form emission when any unresolved reference remains.
    Reject,
    /// Historical behavior: replace the spelling with a deterministic
    /// dangling ID without a recovery annotation.
    LegacyDanglingId,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct UnresolvedReferenceError {
    pub references: Vec<String>,
}

impl std::fmt::Display for UnresolvedReferenceError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "full interchange contains {} unresolved reference(s): {}",
            self.references.len(),
            self.references.join(", ")
        )
    }
}

impl std::error::Error for UnresolvedReferenceError {}

/// How a full-form emission answers the inheritance-aware properties and
/// the unresolved references.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Default)]
pub struct EmissionPolicy {
    pub unresolved: UnresolvedReferencePolicy,
    /// [`ClosurePolicy::Passthrough`] (the default) writes the owned side
    /// of the inheritance-aware properties and the type-correct empty
    /// value for the four closure names — the payload stays proportional
    /// to the model; [`ClosurePolicy::Closure`] writes the specification's
    /// values, the closures materialized per element.
    pub closures: ClosurePolicy,
}

/// Why a full-form emission was refused.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum EmissionError {
    /// The [`UnresolvedReferencePolicy::Reject`] policy met unresolved
    /// references.
    UnresolvedReferences(UnresolvedReferenceError),
    /// Under [`ClosurePolicy::Closure`], the inheritance or import walk of
    /// these elements (by interchange id) hit the resolver's depth budget:
    /// their closures would be incomplete, and a cut enumeration is not
    /// written as the closure.
    TruncatedClosures { elements: Vec<String> },
}

impl std::fmt::Display for EmissionError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::UnresolvedReferences(e) => e.fmt(f),
            Self::TruncatedClosures { elements } => write!(
                f,
                "the inheritance walk of {} element(s) exceeded the depth budget, so their closures cannot be written: {}",
                elements.len(),
                elements.join(", ")
            ),
        }
    }
}

impl std::error::Error for EmissionError {}

impl From<UnresolvedReferenceError> for EmissionError {
    fn from(e: UnresolvedReferenceError) -> Self {
        Self::UnresolvedReferences(e)
    }
}

/// Serialize a model to the full interchange form. Library units provide
/// the implied-relationship targets (normative IDs) and are not emitted.
///
/// # Panics
///
/// Never in practice: this spelling preserves unresolved references, the
/// one policy that cannot reject a model.
pub fn model_to_full_json(model: &Model) -> Value {
    model_to_full_json_with_policy(model, UnresolvedReferencePolicy::Preserve)
        .expect("the preserve policy cannot reject")
}

/// [`model_to_full_json`] with optional **unresolved-reference recovery**:
/// when `recover_refs` is set, every reference that serializes as a
/// deterministic dangling `@id` also gets a schema-valid
/// `TextualRepresentation` annotation (language
/// [`UNRESOLVED_REP_LANGUAGE`], body = the reference's exact source
/// spelling) owned by its document's root namespace. Foreign tools see
/// ordinary annotations; this toolkit's lift restores the references, so
/// *partial models round-trip losslessly through the full form*.
///
/// # Panics
///
/// Never in practice: both spellings of `recover_refs` select a policy
/// that cannot reject a model.
pub fn model_to_full_json_with(model: &Model, recover_refs: bool) -> Value {
    model_to_full_json_with_policy(
        model,
        if recover_refs {
            UnresolvedReferencePolicy::Preserve
        } else {
            UnresolvedReferencePolicy::LegacyDanglingId
        },
    )
    .expect("the boolean compatibility policies cannot reject")
}

pub fn model_to_full_json_with_policy(
    model: &Model,
    policy: UnresolvedReferencePolicy,
) -> Result<Value, UnresolvedReferenceError> {
    let mut resolved = crate::json::ResolvedModel::build(model);
    resolved_to_full_json_with_policy(&mut resolved, model, policy)
}

/// [`model_to_full_json_with_policy`] over an already resolved model:
/// the derived properties the derivation layer computes
/// ([`crate::json::computed_names`]) are projected from it, the rest
/// from the compact element array. The ids of `resolved` must agree
/// with `model`'s compact emission (a resolved model carrying an
/// explicit-id overlay does not): elements the projection cannot find
/// by id keep the array-level derivations.
pub fn resolved_to_full_json_with_policy(
    resolved: &mut crate::json::ResolvedModel,
    model: &Model,
    policy: UnresolvedReferencePolicy,
) -> Result<Value, UnresolvedReferenceError> {
    match resolved_to_full_json(
        resolved,
        model,
        EmissionPolicy {
            unresolved: policy,
            closures: ClosurePolicy::Passthrough,
        },
    ) {
        Ok(v) => Ok(v),
        Err(EmissionError::UnresolvedReferences(e)) => Err(e),
        Err(EmissionError::TruncatedClosures { .. }) => {
            unreachable!("no closure is written at the passthrough level")
        }
    }
}

/// [`resolved_to_full_json_with_policy`] with a full [`EmissionPolicy`]:
/// under [`ClosurePolicy::Closure`] the inheritance-aware properties carry
/// their specification values over the inherited and imported memberships
/// and the four closure names (`inheritedMembership`, `inheritedFeature`,
/// `importedMembership`, `featuringType`) are written; an element whose
/// walk hit the depth budget refuses the emission
/// ([`EmissionError::TruncatedClosures`]). The resolved model's closure
/// policy is set for the emission and restored after it. Both forms are
/// schema-valid and this toolkit reads either (INTEROP.md).
pub fn resolved_to_full_json(
    resolved: &mut crate::json::ResolvedModel,
    model: &Model,
    policy: EmissionPolicy,
) -> Result<Value, EmissionError> {
    let compact = model_to_compact_json(model);
    // Elements only: membership ids share their member's qualified name and
    // must not win the name→id inversion (implied bases target elements).
    let lib_names = crate::json::library_element_name_map(model);
    let mut by_name = HashMap::new();
    for (id, segments) in &lib_names {
        by_name.insert(segments.join("::"), id.clone());
    }
    let previous = resolved.closure_policy();
    resolved.set_closure_policy(policy.closures);
    let mut truncated: Vec<String> = Vec::new();
    let result = full_from_compact_policy(
        compact,
        &by_name,
        policy.unresolved,
        Some(resolved),
        policy.closures,
        &mut truncated,
    );
    resolved.set_closure_policy(previous);
    let value = result?;
    if truncated.is_empty() {
        Ok(value)
    } else {
        Err(EmissionError::TruncatedClosures {
            elements: truncated,
        })
    }
}

/// Serialize a single unit to the full form. Without a library, implied
/// relationships cannot be resolved and are omitted (`isImpliedIncluded`
/// stays `false`); derived properties are still completed.
///
/// # Panics
///
/// Never in practice: this spelling preserves unresolved references, the
/// one policy that cannot reject a unit.
pub fn to_full_json(unit: &SourceUnit) -> Value {
    to_full_json_with_policy(unit, UnresolvedReferencePolicy::Preserve)
        .expect("the preserve policy cannot reject")
}

/// [`to_full_json`] with unresolved-reference recovery annotations — see
/// [`model_to_full_json_with`].
///
/// # Panics
///
/// Never in practice: both spellings of `recover_refs` select a policy
/// that cannot reject a unit.
pub fn to_full_json_with(unit: &SourceUnit, recover_refs: bool) -> Value {
    to_full_json_with_policy(
        unit,
        if recover_refs {
            UnresolvedReferencePolicy::Preserve
        } else {
            UnresolvedReferencePolicy::LegacyDanglingId
        },
    )
    .expect("the boolean compatibility policies cannot reject")
}

pub fn to_full_json_with_policy(
    unit: &SourceUnit,
    policy: UnresolvedReferencePolicy,
) -> Result<Value, UnresolvedReferenceError> {
    // The unit's compact form completed in place: the ids are the ones
    // the compact route derives (a one-unit *model* would seed its root
    // from a unit name and shift every id), and the document is loaded
    // through the model with those ids kept, so the derivation layer
    // answers the full form as it does for any payload.
    from_compact_value_with_policy(crate::json::to_compact_json(unit), &HashMap::new(), policy)
}

/// Language tag of the recovery annotations emitted by the
/// `recover_refs` mode: a `TextualRepresentation` whose `body` is the
/// unresolved reference's exact source spelling.
pub const UNRESOLVED_REP_LANGUAGE: &str = "x-sysmlv2-unresolved-reference";

/// Complete a compact element list to the full form **in place** — every
/// element keeps its `@id`; derived properties are (re)computed from the
/// compact structure, and implied relationships are added when
/// `lib_by_name` (qualified name → id, built from
/// [`crate::json::library_name_map`]) is non-empty. This is the
/// compact→full re-derivation cell of the conversion matrix: unlike
/// lifting to text and rebuilding, element identities survive, so a
/// stored payload can be upgraded without breaking external references.
pub fn from_compact_value(
    compact: Value,
    lib_by_name: &HashMap<String, String>,
    recover_refs: bool,
) -> Value {
    from_compact_value_with_policy(
        compact,
        lib_by_name,
        if recover_refs {
            UnresolvedReferencePolicy::Preserve
        } else {
            UnresolvedReferencePolicy::LegacyDanglingId
        },
    )
    .expect("the boolean compatibility policies cannot reject")
}

pub fn from_compact_value_with_policy(
    compact: Value,
    lib_by_name: &HashMap<String, String>,
    policy: UnresolvedReferencePolicy,
) -> Result<Value, UnresolvedReferenceError> {
    if policy == UnresolvedReferencePolicy::Reject {
        let mut references = Vec::new();
        unresolved_ref_spellings(&compact, &mut references);
        references.sort();
        references.dedup();
        if !references.is_empty() {
            return Err(UnresolvedReferenceError { references });
        }
    }
    // The payload path goes through the model: the document is loaded
    // (ids kept as explicit ids) and the full form emitted from it, so
    // there is one derivation implementation. The library is known by
    // name only, as before: implied relationships target the named ids,
    // and library references stay the ids the document spelled.
    let names: HashMap<String, Vec<String>> = lib_by_name
        .iter()
        .map(|(qn, id)| (id.clone(), qn.split("::").map(str::to_string).collect()))
        .collect();
    // Keep the payload's owned graph intact. The loaded model supplies
    // derived properties for the elements it represents; it is never the
    // source of the emitted owned elements. In particular, an unsupported
    // or over-budget subtree must not disappear during full-form export.
    let loaded = crate::loader::load_document(&compact, &names);
    let mut projection = loaded.ok().and_then(|(_, mut resolved, _, warnings)| {
        // A normalized or incomplete model can carry relationships absent
        // from the original payload. Do not project those phantom ids;
        // derive directly from the original array when the loader warns.
        warnings.is_empty().then(|| {
            resolved.set_library_names(&names);
            resolved
        })
    });
    full_from_compact_policy(
        compact,
        lib_by_name,
        policy,
        projection.as_mut(),
        ClosurePolicy::Passthrough,
        &mut Vec::new(),
    )
}

/// A derived value of the layer as the full form spells it.
fn derived_to_json(resolved: &crate::json::ResolvedModel, v: &crate::json::DerivedValue) -> Value {
    use crate::json::DerivedValue as V;
    let id = |e| id_ref(&resolved.element_id(e).to_string());
    match v {
        V::Null => Value::Null,
        V::Bool(b) => Value::Bool(*b),
        V::Str(s) => Value::String(s.clone()),
        V::Element(e) => id(*e),
        V::Elements(es) => Value::Array(es.iter().map(|&e| id(e)).collect()),
        V::Reference(r) => reference_to_json(resolved, r),
        V::References(rs) => {
            Value::Array(rs.iter().map(|r| reference_to_json(resolved, r)).collect())
        }
        V::Strings(ss) => Value::Array(ss.iter().map(|s| Value::String(s.clone())).collect()),
    }
}

/// A reference of the layer as the full form spells it: an external id
/// as it is, an unresolved spelling as the same deterministic dangling
/// id `patch_refs` derives (the schema forbids `@ref`).
fn reference_to_json(resolved: &crate::json::ResolvedModel, r: &crate::json::Reference) -> Value {
    use crate::json::Reference as R;
    match r {
        R::Element(e) => id_ref(&resolved.element_id(*e).to_string()),
        R::External(id) => id_ref(&id.to_string()),
        R::Unresolved(spelling) => id_ref(&dangling_id(spelling)),
    }
}

use crate::json::dangling_id;

fn id_ref(id: &str) -> Value {
    json!({ "@id": id })
}

fn ty(el: &Map<String, Value>) -> &str {
    el.get("@type").and_then(|v| v.as_str()).unwrap_or("")
}

fn eid(el: &Map<String, Value>) -> &str {
    el.get("@id").and_then(|v| v.as_str()).unwrap_or("")
}

/// The schema's property list for a concrete metaclass. Both the
/// metaclass table and each property list are sorted by name (asserted in
/// this module's tests), so both lookups are searches over the static
/// tables — no per-export map, no per-element set.
fn metaclass_props(metaclass: &str) -> Option<&'static [(&'static str, u8)]> {
    METACLASS_PROPS
        .binary_search_by_key(&metaclass, |(name, _)| name)
        .ok()
        .map(|i| METACLASS_PROPS[i].1)
}

fn ref_of(v: &Value) -> Option<String> {
    v.get("@id").and_then(|x| x.as_str()).map(|s| s.to_string())
}

/// The AnnotatingElement an Annotation owns (`ownedAnnotatingElement`):
/// spelled by the payload, or the first owned related element of that
/// kind. Present only in the prefix-annotation shape, where the Annotation
/// is owned by the element it annotates.
fn owned_annotating_element(
    elements: &[Map<String, Value>],
    related_elems: &[Vec<usize>],
    index: &HashMap<String, usize>,
    r: usize,
) -> Option<usize> {
    elements[r]
        .get("ownedAnnotatingElement")
        .and_then(ref_of)
        .and_then(|id| index.get(&id).copied())
        .or_else(|| {
            related_elems[r]
                .iter()
                .copied()
                .find(|&k| conforms(ty(&elements[k]), "AnnotatingElement"))
        })
}

fn is_membership(t: &str) -> bool {
    // FeatureValue and ElementFilterMembership are OwningMembership
    // subtypes in the metamodel.
    t == "Membership" || t.ends_with("Membership") || t == "FeatureValue"
}

fn is_import(t: &str) -> bool {
    matches!(
        t,
        "NamespaceImport" | "MembershipImport" | "NamespaceExpose" | "MembershipExpose"
    )
}

fn unresolved_ref_spellings(value: &Value, out: &mut Vec<String>) {
    match value {
        Value::Object(object) => {
            if let Some(spelling) = object.get("@ref").and_then(Value::as_str) {
                // An id-shaped spelling is a reference by id (kept as such
                // on the wire), not an unresolved name.
                if Uuid::parse_str(spelling.trim_matches('\'')).is_err() {
                    out.push(spelling.to_string());
                }
            }
            for value in object.values() {
                unresolved_ref_spellings(value, out);
            }
        }
        Value::Array(values) => {
            for value in values {
                unresolved_ref_spellings(value, out);
            }
        }
        _ => {}
    }
}

fn full_from_compact_policy(
    compact: Value,
    lib_by_name: &HashMap<String, String>,
    policy: UnresolvedReferencePolicy,
    projection: Option<&mut crate::json::ResolvedModel>,
    closures: ClosurePolicy,
    truncated: &mut Vec<String>,
) -> Result<Value, UnresolvedReferenceError> {
    if policy == UnresolvedReferencePolicy::Reject {
        let mut references = Vec::new();
        unresolved_ref_spellings(&compact, &mut references);
        references.sort();
        references.dedup();
        if !references.is_empty() {
            return Err(UnresolvedReferenceError { references });
        }
    }
    Ok(full_from_compact_with(
        compact,
        lib_by_name,
        policy == UnresolvedReferencePolicy::Preserve,
        projection,
        closures,
        truncated,
    ))
}

pub(crate) fn full_from_compact_with(
    compact: Value,
    lib_by_name: &HashMap<String, String>,
    recover_refs: bool,
    mut projection: Option<&mut crate::json::ResolvedModel>,
    closures: ClosurePolicy,
    truncated: &mut Vec<String>,
) -> Value {
    let Value::Array(items) = compact else {
        return compact;
    };
    let mut elements: Vec<Map<String, Value>> = items
        .into_iter()
        .filter_map(|v| match v {
            Value::Object(m) => Some(m),
            _ => None,
        })
        .collect();

    if recover_refs {
        inject_unresolved_reps(&mut elements);
    }

    // Replace `{"@ref": name}` placeholders with deterministic dangling IDs
    // (`additionalProperties: false` forbids @ref in the published schema).
    for el in &mut elements {
        for v in el.values_mut() {
            patch_refs(v);
        }
    }

    // ---- implied relationships ----
    // The layer synthesizes them (`json/implied.rs`) when the library
    // bases are known (a loaded library or a name table — the layer
    // synthesizes none otherwise, so `isImpliedIncluded` stays false
    // exactly where no implied relationship is listed); the full form
    // lists them under their owner's `ownedRelationship` and as elements
    // of the array. Without a model to project from, none can be offered.
    if let Some(resolved) = projection.as_deref_mut() {
        add_implied_relationships(&mut elements, resolved);
    }
    let implied_included = projection.is_some() && !lib_by_name.is_empty();

    // ---- graph indexes ----
    let index: HashMap<String, usize> = elements
        .iter()
        .enumerate()
        .map(|(i, el)| (eid(el).to_string(), i))
        .collect();
    // Element → owning relationship index; relationship → owner element idx.
    let owner_rel: Vec<Option<usize>> = elements
        .iter()
        .map(|el| {
            el.get("owningRelationship")
                .and_then(ref_of)
                .and_then(|id| index.get(&id).copied())
        })
        .collect();
    let rel_owner: Vec<Option<usize>> = elements
        .iter()
        .map(|el| {
            el.get("owningRelatedElement")
                .and_then(ref_of)
                .and_then(|id| index.get(&id).copied())
        })
        .collect();
    let owned_rels: Vec<Vec<usize>> = elements
        .iter()
        .map(|el| {
            el.get("ownedRelationship")
                .and_then(|v| v.as_array())
                .map(|a| {
                    a.iter()
                        .filter_map(ref_of)
                        .filter_map(|id| index.get(&id).copied())
                        .collect()
                })
                .unwrap_or_default()
        })
        .collect();
    let related_elems: Vec<Vec<usize>> = elements
        .iter()
        .map(|el| {
            el.get("ownedRelatedElement")
                .and_then(|v| v.as_array())
                .map(|a| {
                    a.iter()
                        .filter_map(ref_of)
                        .filter_map(|id| index.get(&id).copied())
                        .collect()
                })
                .unwrap_or_default()
        })
        .collect();

    // Effective names (pilot `Feature::namingFeature`): an unnamed
    // feature is named by the first feature it explicitly redefines or
    // references (`:>> uid = 4;`, `perform a;`), and a chain feature by
    // its last chaining target. The pilot derives `Element::name` via
    // `effectiveName()` and `Membership.memberName` from the member's
    // name, so the full form materializes both.
    // Redefinition targets resolved into the standard library are not in
    // this document — name them from the library map so `:>> mass` still
    // yields an effective name.
    let lib_id_names: HashMap<&str, &str> = lib_by_name
        .iter()
        .map(|(name, id)| {
            (
                id.as_str(),
                name.rsplit("::").next().unwrap_or(name.as_str()),
            )
        })
        .collect();
    let eff_names: Vec<Option<String>> = (0..elements.len())
        .map(|i| effective_name_of(i, &elements, &owned_rels, &index, &lib_id_names, 0))
        .collect();

    // Qualified names (escaped segments joined with ::), owner chains.
    let mut qnames: Vec<Option<String>> = vec![None; elements.len()];
    for i in 0..elements.len() {
        qname_of(
            i,
            &elements,
            &owner_rel,
            &rel_owner,
            &eff_names,
            &mut qnames,
        );
    }

    // Element::isLibraryElement (KerML deriveElementIsLibraryElement):
    // true when `libraryNamespace()` is non-null, i.e. the element is a
    // LibraryPackage or sits anywhere in the ownership tree of one.
    // Ownership steps through the owning relationship (an element's
    // `owningRelationship`, then that relationship's owner); a
    // relationship's own owner is its `owningRelatedElement`.
    // Library membership by ownership walk, for elements the layer does
    // not project (implied relationships).
    let library_element: Vec<bool> = {
        let parent = |i: usize| -> Option<usize> {
            rel_owner[i].or_else(|| owner_rel[i].and_then(|r| rel_owner[r]))
        };
        let mut memo: Vec<Option<bool>> = vec![None; elements.len()];
        for start in 0..elements.len() {
            if memo[start].is_some() {
                continue;
            }
            let mut path = Vec::new();
            let mut at = Some(start);
            let mut found = false;
            while let Some(i) = at {
                if let Some(v) = memo[i] {
                    found = v;
                    break;
                }
                if path.contains(&i) {
                    break; // malformed ownership cycle: not a library tree
                }
                path.push(i);
                if ty(&elements[i]) == "LibraryPackage" {
                    found = true;
                    break;
                }
                at = parent(i);
            }
            for i in path {
                memo[i] = Some(found);
            }
        }
        memo.into_iter().map(|v| v.unwrap_or(false)).collect()
    };

    // ---- derived properties ----
    for i in 0..elements.len() {
        let t = ty(&elements[i]).to_string();
        let this_id = eid(&elements[i]).to_string();
        let mut derived: Map<String, Value> = Map::new();
        // Projection: every name the derivation layer computes comes from
        // the resolved model; the array-level code below only fills the
        // families not ported yet.
        // Elements with no model counterpart — the implied relationships
        // this pass synthesizes — keep the array-level derivations until
        // the layer synthesizes them itself.
        let mut projected = false;
        if let Some(resolved) = projection.as_deref_mut() {
            // Same id *and* same metaclass: a model holding two elements
            // under one id (a unit-name collision) must not lend one
            // element's lists to the other.
            if let Some(e) = resolved
                .element_by_id(&this_id)
                .filter(|&e| resolved.element_type(e) == t)
            {
                projected = true;
                // Under the closure policy a walk that hit the depth
                // budget refuses the emission rather than writing a cut
                // closure.
                if closures != ClosurePolicy::Passthrough && resolved.closure_truncated(e) {
                    truncated.push(this_id.clone());
                }
                // The names the layer computes on this metaclass, decided
                // once per metaclass rather than once per element.
                let names = resolved.computable_names(resolved.element_type(e));
                for name in names.iter() {
                    // The four closure names are written under the closure
                    // policy only; the catalog's empty value stands for
                    // them at the passthrough level.
                    if closures == ClosurePolicy::Passthrough && CLOSURE_NAMES.contains(name) {
                        continue;
                    }
                    if let crate::json::Derived::Value(v) = resolved.derived_computable(e, name) {
                        derived.insert((*name).to_string(), derived_to_json(resolved, &v));
                    }
                }
                // Relationships this pass added to the array and the model
                // does not hold — the unresolved-reference recovery
                // annotations' memberships — still belong to their owner's
                // lists, so the full form stays self-consistent.
                let extra: Vec<usize> = owned_rels[i]
                    .iter()
                    .copied()
                    .filter(|&r| resolved.element_by_id(eid(&elements[r])).is_none())
                    .collect();
                for &r in &extra {
                    let rel = id_ref(eid(&elements[r]));
                    let kids: Vec<Value> = related_elems[r]
                        .iter()
                        .map(|&k| id_ref(eid(&elements[k])))
                        .collect();
                    let push = |derived: &mut Map<String, Value>, name: &str, vals: &[Value]| {
                        if let Some(Value::Array(a)) = derived.get_mut(name) {
                            a.extend(vals.iter().cloned());
                        }
                    };
                    push(&mut derived, "ownedElement", &kids);
                    // Recovery annotations are TextualRepresentations.
                    for &k in &related_elems[r] {
                        if ty(&elements[k]) == "TextualRepresentation" {
                            let kid = id_ref(eid(&elements[k]));
                            push(&mut derived, "textualRepresentation", &[kid]);
                        }
                    }
                    if is_membership(ty(&elements[r])) {
                        push(&mut derived, "ownedMembership", std::slice::from_ref(&rel));
                        push(&mut derived, "membership", std::slice::from_ref(&rel));
                        push(&mut derived, "ownedMember", &kids);
                        push(&mut derived, "member", &kids);
                    }
                }
            }
        }
        // Owned Annotation relationships and whether one annotates this
        // very element (the prefix-annotation shape) — shared by the
        // annotation-family derivations below.
        let owned_annotations: Vec<usize> = owned_rels[i]
            .iter()
            .copied()
            .filter(|&r| ty(&elements[r]) == "Annotation")
            .collect();
        let annotates_self = |r: usize| match elements[r].get("annotatedElement").and_then(ref_of) {
            Some(annotated) => annotated == this_id,
            // Unspelled: completed from the owner below, in the shape where
            // the Annotation owns its annotating element.
            None => owned_annotating_element(&elements, &related_elems, &index, r).is_some(),
        };
        // Derivations that must win over a compact-spelled value (the
        // pilot computes these at the model level regardless of the
        // textual spelling): applied with insert, not or_insert.
        let mut overrides: Map<String, Value> = Map::new();

        // Ownership (owner, owningMembership, owningNamespace and
        // isLibraryElement are projected from the layer; an unprojected
        // element gets the array-level derivation).
        let owner_idx = owner_rel[i].and_then(|r| rel_owner[r]);
        if !projected {
            derived.insert(
                "owner".into(),
                owner_idx
                    .map(|o| id_ref(eid(&elements[o])))
                    .unwrap_or(Value::Null),
            );
            let owning_membership = owner_rel[i].filter(|&r| is_membership(ty(&elements[r])));
            derived.insert(
                "owningMembership".into(),
                owning_membership
                    .map(|r| id_ref(eid(&elements[r])))
                    .unwrap_or(Value::Null),
            );
            derived.insert(
                "owningNamespace".into(),
                owning_membership
                    .and(owner_idx)
                    .map(|o| id_ref(eid(&elements[o])))
                    .unwrap_or(Value::Null),
            );
            derived.insert("isLibraryElement".into(), Value::Bool(library_element[i]));
        }
        // Feature::owningType — the owner through a FeatureMembership
        // kind — with its membership, the SysML Definition/Usage
        // narrowings, and `endOwningType` when the membership is an
        // EndFeatureMembership (the catalog filter drops undeclared
        // entries).
        let owning_fm =
            owner_rel[i].filter(|&r| crate::json::is_feature_membership(ty(&elements[r])));
        if let Some(r) = owning_fm {
            let is_end = ty(&elements[r]) == "EndFeatureMembership";
            // The owning-type family is projected from the layer; an
            // unprojected element gets the array-level derivation.
            if !projected {
                derived.insert("owningFeatureMembership".into(), id_ref(eid(&elements[r])));
                if let Some(o) = owner_idx.filter(|&o| conforms(ty(&elements[o]), "Type")) {
                    let oty = ty(&elements[o]);
                    let oref = id_ref(eid(&elements[o]));
                    if conforms(oty, "Definition") {
                        derived.insert("owningDefinition".into(), oref.clone());
                    }
                    if conforms(oty, "Usage") {
                        derived.insert("owningUsage".into(), oref.clone());
                    }
                    if is_end {
                        derived.insert("endOwningType".into(), oref.clone());
                    }
                    derived.insert("owningType".into(), oref);
                }
            }
            // End features are constant (KerML 2025 metamodel); the pilot's
            // FlowEnds are not.
            if is_end && t != "FlowEnd" {
                derived.insert("isConstant".into(), Value::Bool(true));
            }
        }
        if !projected {
            // Type::multiplicity — the owned member that is a Multiplicity: the
            // MultiplicityRange a `[n..m]` part declares, or a KerML
            // `multiplicity` member. A Type owns at most one. (KerML's derive
            // rule adds a fallback to the general Type's multiplicity through an
            // owned Specialization; that contradicts the property's `subsets
            // ownedMember`, and the property definition wins here.)
            if let Some(m) = owned_rels[i]
                .iter()
                .filter(|&&r| is_membership(ty(&elements[r])))
                .find_map(|&r| {
                    related_elems[r]
                        .iter()
                        .copied()
                        .find(|&k| conforms(ty(&elements[k]), "Multiplicity"))
                })
            {
                derived.insert("multiplicity".into(), id_ref(eid(&elements[m])));
            }
        }
        // Annotation ends. This toolkit lowers every Annotation as owned by
        // its annotating element (the `about` shape), so `annotatingElement`
        // is the owner. A payload that instead owns the annotating element
        // under the Annotation (KerML's `ownedAnnotatingElement`, the
        // prefix-annotation shape) makes the owner the annotated element;
        // the `owning*` narrowings and the endpoint fill below follow the
        // same test. `annotatedElement` is an *owned* property here, so the
        // layer never projects it and this completion runs for every
        // Annotation; the projected names it also writes agree with the
        // layer's.
        // The Annotation-side family is projected; this is the fallback.
        if !projected && t == "Annotation" {
            let owned_annotating = owned_annotating_element(&elements, &related_elems, &index, i);
            match (owned_annotating, rel_owner[i]) {
                (Some(k), owner) => {
                    let kref = id_ref(eid(&elements[k]));
                    derived.insert("ownedAnnotatingElement".into(), kref.clone());
                    derived.insert("annotatingElement".into(), kref);
                    // The owner is the annotated element when the spelled
                    // annotatedElement agrees; when it is absent, the required
                    // end is completed from the owner rather than left to the
                    // self-reference placeholder.
                    if let Some(o) = owner {
                        let oref = id_ref(eid(&elements[o]));
                        match elements[i].get("annotatedElement").and_then(ref_of) {
                            None => {
                                derived.insert("annotatedElement".into(), oref.clone());
                                derived.insert("owningAnnotatedElement".into(), oref);
                            }
                            Some(a) if a == eid(&elements[o]) => {
                                derived.insert("owningAnnotatedElement".into(), oref);
                            }
                            Some(_) => {}
                        }
                    }
                }
                (None, Some(o)) if conforms(ty(&elements[o]), "AnnotatingElement") => {
                    let oref = id_ref(eid(&elements[o]));
                    derived.insert("annotatingElement".into(), oref.clone());
                    derived.insert("owningAnnotatingElement".into(), oref);
                }
                _ => {}
            }
        }
        // AnnotatingElement::owningAnnotatingRelationship — the owning
        // relationship when it is an Annotation (prefix-annotation shape).
        if !projected {
            if let Some(r) = owner_rel[i].filter(|&r| ty(&elements[r]) == "Annotation") {
                derived.insert(
                    "owningAnnotatingRelationship".into(),
                    id_ref(eid(&elements[r])),
                );
            }
        }
        // End *usages* are constant, variable, and time-varying regardless
        // of how they are owned (interface-body ends ride a plain
        // FeatureMembership) — but the pilot's FlowEnds are none of these.
        // Overrides: the compact form spells the textual defaults.
        if elements[i].get("isEnd").and_then(|v| v.as_bool()) == Some(true)
            && t != "FlowEnd"
            && t.ends_with("Usage")
        {
            overrides.insert("isConstant".into(), Value::Bool(true));
            overrides.insert("isVariable".into(), Value::Bool(true));
            overrides.insert("mayTimeVary".into(), Value::Bool(true));
        }
        // A state's *inline* entry/do/exit action is composite at the
        // model level; perform-references (`do performedAction;`) stay
        // referential.
        if t == "ActionUsage"
            && owner_rel[i].is_some_and(|r| ty(&elements[r]) == "StateSubactionMembership")
        {
            overrides.insert("isComposite".into(), Value::Bool(true));
        }

        // Names: the layer projects `name`, `shortName` and
        // `qualifiedName` (the graph-effective naming rule, KerML
        // 8.2.3.5); the array-level rule is the fallback.
        if !projected {
            let declared_name = elements[i]
                .get("declaredName")
                .filter(|v| !v.is_null())
                .cloned()
                .or_else(|| eff_names[i].clone().map(Value::String))
                .unwrap_or(Value::Null);
            let declared_short = elements[i]
                .get("declaredShortName")
                .cloned()
                .unwrap_or(Value::Null);
            derived.insert("name".into(), declared_name);
            derived.insert("shortName".into(), declared_short);
            derived.insert(
                "qualifiedName".into(),
                qnames[i].clone().map(Value::String).unwrap_or(Value::Null),
            );
            // Usage::isReference is derived as the negation of isComposite
            // (pilot `Usage_isReference_SettingDelegate`); the catalog
            // filter drops this for metaclasses without the property.
            if let Some(c) = elements[i].get("isComposite").and_then(|v| v.as_bool()) {
                derived.insert("isReference".into(), Value::Bool(!c));
            }
        }

        // Annotating members.
        let owned_kids: Vec<usize> = owned_rels[i]
            .iter()
            .flat_map(|&r| related_elems[r].iter().copied())
            .collect();
        let kids_of_type = |name: &str| -> Vec<Value> {
            owned_kids
                .iter()
                .filter(|&&k| ty(&elements[k]) == name)
                .map(|&k| id_ref(eid(&elements[k])))
                .collect()
        };
        if !projected {
            derived.insert(
                "documentation".into(),
                Value::Array(kids_of_type("Documentation")),
            );
        }
        // Requirement/concern `text` is the owned documentation bodies
        // (pilot `RequirementDefinition_text_SettingDelegate`); the catalog
        // filter drops it for metaclasses without the property.
        let texts: Vec<Value> = owned_kids
            .iter()
            .filter(|&&k| ty(&elements[k]) == "Documentation")
            .filter_map(|&k| elements[k].get("body").filter(|v| !v.is_null()).cloned())
            .collect();
        if !projected {
            derived.insert("text".into(), Value::Array(texts));
        }
        if !projected {
            derived.insert(
                "textualRepresentation".into(),
                Value::Array(kids_of_type("TextualRepresentation")),
            );
        }
        // Element::ownedAnnotation — the owned Annotations that annotate
        // this element (the prefix-annotation shape). An `about` clause's
        // Annotation is owned by the annotating element and annotates
        // another, so it is that element's `ownedAnnotatingRelationship`,
        // not its `ownedAnnotation`.
        if !projected {
            derived.insert(
                "ownedAnnotation".into(),
                Value::Array(
                    owned_annotations
                        .iter()
                        .filter(|&&r| annotates_self(r))
                        .map(|&r| id_ref(eid(&elements[r])))
                        .collect(),
                ),
            );
        }

        // The namespace membership family and the type-level feature
        // family (ownedElement, ownedMembership, membership, ownedMember,
        // member, ownedImport, ownedFeatureMembership, featureMembership,
        // ownedFeature, feature) are projected from the layer; an
        // unprojected element gets the array-level derivation. The owned
        // features feed the direction-filtered families below either way.
        let feature_memberships: Vec<usize> = owned_rels[i]
            .iter()
            .copied()
            .filter(|&r| crate::json::is_feature_membership(ty(&elements[r])))
            .collect();
        let features: Vec<usize> = feature_memberships
            .iter()
            .flat_map(|&r| related_elems[r].iter().copied())
            .collect();
        if !projected {
            let mut owned_elements = Vec::new();
            for &r in &owned_rels[i] {
                for &k in &related_elems[r] {
                    owned_elements.push(id_ref(eid(&elements[k])));
                }
            }
            derived.insert("ownedElement".into(), Value::Array(owned_elements));
            let memberships: Vec<Value> = owned_rels[i]
                .iter()
                .filter(|&&r| is_membership(ty(&elements[r])))
                .map(|&r| id_ref(eid(&elements[r])))
                .collect();
            derived.insert("ownedMembership".into(), Value::Array(memberships.clone()));
            derived.insert("membership".into(), Value::Array(memberships));
            let owned_members: Vec<Value> = owned_rels[i]
                .iter()
                .filter(|&&r| is_membership(ty(&elements[r])))
                .flat_map(|&r| related_elems[r].iter().map(|&k| id_ref(eid(&elements[k]))))
                .collect();
            derived.insert("ownedMember".into(), Value::Array(owned_members.clone()));
            derived.insert("member".into(), Value::Array(owned_members));
            derived.insert(
                "ownedImport".into(),
                Value::Array(
                    owned_rels[i]
                        .iter()
                        .filter(|&&r| is_import(ty(&elements[r])))
                        .map(|&r| id_ref(eid(&elements[r])))
                        .collect(),
                ),
            );
            let fm_refs: Vec<Value> = feature_memberships
                .iter()
                .map(|&r| id_ref(eid(&elements[r])))
                .collect();
            derived.insert(
                "ownedFeatureMembership".into(),
                Value::Array(fm_refs.clone()),
            );
            derived.insert("featureMembership".into(), Value::Array(fm_refs));
            let feature_refs: Vec<Value> = features
                .iter()
                .map(|&k| id_ref(eid(&elements[k])))
                .collect();
            derived.insert("ownedFeature".into(), Value::Array(feature_refs.clone()));
            derived.insert("feature".into(), Value::Array(feature_refs));
        }
        let ends: Vec<Value> = features
            .iter()
            .filter(|&&k| {
                elements[k]
                    .get("isEnd")
                    .and_then(|v| v.as_bool())
                    .unwrap_or(false)
            })
            .map(|&k| id_ref(eid(&elements[k])))
            .collect();
        if !projected {
            derived.insert("ownedEndFeature".into(), Value::Array(ends.clone()));
            derived.insert("endFeature".into(), Value::Array(ends));
        }
        let by_direction = |dir: &str| -> Vec<Value> {
            features
                .iter()
                .filter(|&&k| {
                    elements[k].get("direction").and_then(|v| v.as_str()) == Some(dir)
                        || (dir == "inout"
                            && elements[k].get("direction").and_then(|v| v.as_str())
                                == Some("inout"))
                })
                .map(|&k| id_ref(eid(&elements[k])))
                .collect()
        };
        let mut input = by_direction("in");
        input.extend(by_direction("inout"));
        let mut output = by_direction("out");
        output.extend(by_direction("inout"));
        if !projected {
            derived.insert("input".into(), Value::Array(input));
            derived.insert("output".into(), Value::Array(output));
        }
        let directed: Vec<Value> = features
            .iter()
            .filter(|&&k| {
                elements[k]
                    .get("direction")
                    .map(|v| v.is_string())
                    .unwrap_or(false)
            })
            .map(|&k| id_ref(eid(&elements[k])))
            .collect();
        if !projected {
            derived.insert("directedFeature".into(), Value::Array(directed.clone()));
            derived.insert("directedUsage".into(), Value::Array(directed));
        }

        // Specializations owned by this element (projected from the
        // layer, implied ones included; the fallback below selects by
        // exact metaclass name).
        let rels_of = |names: &[&str]| -> Vec<Value> {
            owned_rels[i]
                .iter()
                .filter(|&&r| names.contains(&ty(&elements[r])))
                .map(|&r| id_ref(eid(&elements[r])))
                .collect()
        };
        if !projected {
            derived.insert(
                "ownedSpecialization".into(),
                Value::Array(rels_of(&[
                    "Specialization",
                    "Subclassification",
                    "FeatureTyping",
                    "Subsetting",
                    "Redefinition",
                    "ReferenceSubsetting",
                    "CrossSubsetting",
                ])),
            );
            derived.insert(
                "ownedSubclassification".into(),
                Value::Array(rels_of(&["Subclassification"])),
            );
            derived.insert(
                "ownedTyping".into(),
                Value::Array(rels_of(&["FeatureTyping", "ConjugatedPortTyping"])),
            );
            derived.insert(
                "ownedSubsetting".into(),
                Value::Array(rels_of(&[
                    "Subsetting",
                    "Redefinition",
                    "ReferenceSubsetting",
                    "CrossSubsetting",
                ])),
            );
            derived.insert(
                "ownedRedefinition".into(),
                Value::Array(rels_of(&["Redefinition"])),
            );
            derived.insert(
                "ownedReferenceSubsetting".into(),
                rels_of(&["ReferenceSubsetting"])
                    .into_iter()
                    .next()
                    .unwrap_or(Value::Null),
            );
        }
        if !projected {
            derived.insert(
                "ownedCrossSubsetting".into(),
                rels_of(&["CrossSubsetting"])
                    .into_iter()
                    .next()
                    .unwrap_or(Value::Null),
            );
        }
        if !projected {
            derived.insert(
                "ownedConjugator".into(),
                rels_of(&["Conjugation", "PortConjugation"])
                    .into_iter()
                    .next()
                    .unwrap_or(Value::Null),
            );
        }
        derived.insert(
            "ownedDisjoining".into(),
            Value::Array(rels_of(&["Disjoining"])),
        );

        // Feature typing targets.
        let typing_targets: Vec<Value> = owned_rels[i]
            .iter()
            .filter(|&&r| matches!(ty(&elements[r]), "FeatureTyping" | "ConjugatedPortTyping"))
            .filter_map(|&r| elements[r].get("type").cloned())
            .collect();
        if !projected {
            derived.insert("type".into(), Value::Array(typing_targets.clone()));
            if t.ends_with("Usage") || usage_kind_of(&t, Dialect::Sysml).is_some() {
                derived.insert("definition".into(), Value::Array(typing_targets));
            }
        }

        // Usage kind-filtered lists (ownedPart / nestedPart / …).
        let usage_kids: Vec<usize> = features
            .iter()
            .copied()
            .filter(|&k| usage_kind_of(ty(&elements[k]), Dialect::Sysml).is_some())
            .collect();
        let usage_kid_refs: Vec<Value> = usage_kids
            .iter()
            .map(|&k| id_ref(eid(&elements[k])))
            .collect();
        if !projected {
            derived.insert("ownedUsage".into(), Value::Array(usage_kid_refs.clone()));
            derived.insert("nestedUsage".into(), Value::Array(usage_kid_refs.clone()));
            derived.insert("usage".into(), Value::Array(usage_kid_refs));
            let variant_rels: Vec<Value> = rels_of(&["VariantMembership"]);
            derived.insert("variantMembership".into(), Value::Array(variant_rels));
            derived.insert(
                "variant".into(),
                Value::Array(
                    owned_rels[i]
                        .iter()
                        .filter(|&&r| ty(&elements[r]) == "VariantMembership")
                        .flat_map(|&r| related_elems[r].iter().map(|&k| id_ref(eid(&elements[k]))))
                        .collect(),
                ),
            );
        }

        // Relationship endpoints (`source`/`target` are owned on the
        // wire; `relatedElement` is projected).
        fill_relationship_endpoints(
            &mut derived,
            &elements,
            i,
            &rel_owner,
            &related_elems,
            projected,
        );

        // Relationship-side owners (owningType, owningClassifier,
        // owningFeature, owningFeatureOfType) are projected from the layer;
        // an implied specialization, which has no model counterpart, is
        // owned by its specific side and says so.
        if !projected {
            if let Some(o) = rel_owner[i].filter(|_| !is_membership(&t) && !is_import(&t)) {
                let owner_props: &[(&str, &str)] = if conforms(&t, "Subclassification") {
                    &[("owningType", "Type"), ("owningClassifier", "Classifier")]
                } else if conforms(&t, "Subsetting") || conforms(&t, "FeatureTyping") {
                    &[("owningType", "Type"), ("owningFeature", "Feature")]
                } else if conforms(&t, "Specialization")
                    || conforms(&t, "Conjugation")
                    || conforms(&t, "Disjoining")
                {
                    &[("owningType", "Type")]
                } else if t == "FeatureInverting" {
                    &[("owningFeature", "Feature")]
                } else if t == "TypeFeaturing" {
                    &[("owningFeatureOfType", "Feature")]
                } else {
                    &[]
                };
                let owner_id = eid(&elements[o]);
                let owner_is_source = derived
                    .get("source")
                    .and_then(Value::as_array)
                    .and_then(|ends| ends.first())
                    .is_none_or(|source| ref_of(source).as_deref() == Some(owner_id));
                if owner_is_source {
                    let oty = ty(&elements[o]);
                    let oref = id_ref(owner_id);
                    for (prop, kind) in owner_props {
                        if conforms(oty, kind) {
                            derived.insert((*prop).into(), oref.clone());
                        }
                    }
                }
            }
        }

        // Derived redefinitions with non-nullable schema types.
        if is_membership(&t) {
            // Owning-membership family: the owned member element under
            // redefining names.
            let owned_member = related_elems[i].first().map(|&k| id_ref(eid(&elements[k])));
            if let Some(m) = &owned_member {
                if !projected {
                    derived.insert("ownedMemberElement".into(), m.clone());
                    derived.insert("ownedMemberFeature".into(), m.clone());
                }
                if let (Some(id), false) = (ref_of(m), projected) {
                    derived.insert("ownedMemberElementId".into(), Value::String(id.clone()));
                    if let Some(&k) = index.get(&id) {
                        // An unnamed member falls back to its effective
                        // name (reference/chain/implied positional — the
                        // same table memberName derives from), then the
                        // membership's own implied positional name.
                        let mut member_name = elements[k]
                            .get("declaredName")
                            .cloned()
                            .unwrap_or(Value::Null);
                        if member_name.is_null() {
                            member_name = eff_names[k]
                                .clone()
                                .map(Value::String)
                                .unwrap_or(Value::Null);
                        }
                        if member_name.is_null() {
                            member_name = match t.as_str() {
                                "ReturnParameterMembership" => json!("result"),
                                "ObjectiveMembership" => json!("obj"),
                                _ => Value::Null,
                            };
                        }
                        derived.insert("ownedMemberName".into(), member_name);
                        derived.insert(
                            "ownedMemberShortName".into(),
                            elements[k]
                                .get("declaredShortName")
                                .cloned()
                                .unwrap_or(Value::Null),
                        );
                    }
                }
            }
            // The type owning a feature membership.
            if !projected {
                if let Some(o) = rel_owner[i] {
                    derived.insert("owningType".into(), id_ref(eid(&elements[o])));
                }
            }
        }
        // Import-side names (importOwningNamespace, importedElement) are
        // projected from the layer; an unprojected import gets the
        // array-level derivation (an in-document membership target is
        // dereferenced to its member, a library one stays the membership).
        if !projected && is_import(&t) {
            if let Some(o) = rel_owner[i] {
                derived.insert("importOwningNamespace".into(), id_ref(eid(&elements[o])));
            }
            if let Some(target) = elements[i]
                .get("importedNamespace")
                .or_else(|| elements[i].get("importedMembership"))
                .cloned()
            {
                // `importedMembership` references a Membership; the derived
                // importedElement is its member. Dereference in-document
                // memberships (library memberships stay as-is — dangling
                // derived refs are tolerated like every other library ref).
                let target = target
                    .get("@id")
                    .and_then(|v| v.as_str())
                    .and_then(|id| index.get(id).copied())
                    .filter(|&m| is_membership(ty(&elements[m])))
                    .and_then(|m| {
                        elements[m]
                            .get("memberElement")
                            .filter(|v| v.get("@id").is_some())
                            .cloned()
                            .or_else(|| {
                                related_elems[m].first().map(|&k| id_ref(eid(&elements[k])))
                            })
                    })
                    .unwrap_or(target);
                derived.insert("importedElement".into(), target);
            }
        }
        // Features: featureTarget = last chaining feature, else self
        // (projected from the layer; the fallback for an unprojected
        // element).
        let self_ref = id_ref(&this_id);
        if !projected {
            let chain_rels: Vec<usize> = owned_rels[i]
                .iter()
                .copied()
                .filter(|&r| ty(&elements[r]) == "FeatureChaining")
                .collect();
            let last_chain = chain_rels
                .last()
                .and_then(|&r| elements[r].get("chainingFeature").cloned());
            derived.insert(
                "chainingFeature".into(),
                Value::Array(
                    chain_rels
                        .iter()
                        .filter_map(|&r| elements[r].get("chainingFeature").cloned())
                        .collect(),
                ),
            );
            derived.insert(
                "ownedFeatureChaining".into(),
                Value::Array(
                    chain_rels
                        .iter()
                        .map(|&r| id_ref(eid(&elements[r])))
                        .collect(),
                ),
            );
            derived.insert(
                "featureTarget".into(),
                last_chain.unwrap_or_else(|| self_ref.clone()),
            );
        }
        // Expressions: `result` (projected: the return parameter) —
        // the self-reference placeholder for an unprojected element.
        if !projected {
            derived.insert("result".into(), self_ref.clone());
        }
        if !projected && t == "FeatureValue" {
            if let Some(o) = rel_owner[i] {
                derived.insert("featureWithValue".into(), id_ref(eid(&elements[o])));
            }
            if let Some(&k) = related_elems[i].first() {
                derived.insert("value".into(), id_ref(eid(&elements[k])));
            }
        }
        // Expression-family derived references.
        let membership_target = owned_rels[i]
            .iter()
            .find(|&&r| matches!(ty(&elements[r]), "Membership" | "OwningMembership"))
            .and_then(|&r| {
                elements[r]
                    .get("memberElement")
                    .cloned()
                    .filter(|v| !v.is_null())
                    .or_else(|| related_elems[r].first().map(|&k| id_ref(eid(&elements[k]))))
            });
        match t.as_str() {
            "FeatureReferenceExpression" if !projected => {
                if let Some(m) = &membership_target {
                    derived.insert("referent".into(), m.clone());
                }
            }
            "FeatureChainExpression" if !projected => {
                if let Some(m) = &membership_target {
                    derived.insert("targetFeature".into(), m.clone());
                }
            }
            "ReferenceSubsetting" if !projected => {
                if let Some(o) = rel_owner[i] {
                    derived.insert("referencingFeature".into(), id_ref(eid(&elements[o])));
                }
            }
            "CrossSubsetting" if !projected => {
                if let Some(o) = rel_owner[i] {
                    derived.insert("crossingFeature".into(), id_ref(eid(&elements[o])));
                }
            }
            "PortDefinition" if !projected => {
                if let Some(&c) = owned_kids
                    .iter()
                    .find(|&&k| ty(&elements[k]) == "ConjugatedPortDefinition")
                {
                    derived.insert("conjugatedPortDefinition".into(), id_ref(eid(&elements[c])));
                }
            }
            "ConjugatedPortDefinition" if !projected => {
                derived.insert("isConjugated".into(), Value::Bool(true));
                if let Some(o) = owner_idx {
                    derived.insert("originalPortDefinition".into(), id_ref(eid(&elements[o])));
                }
                if let Some(&pc) = owned_rels[i]
                    .iter()
                    .find(|&&r| ty(&elements[r]) == "PortConjugation")
                {
                    derived.insert("ownedPortConjugator".into(), id_ref(eid(&elements[pc])));
                }
            }
            // The conjugated definition: a PortConjugation's owner, a
            // State sub-actions: the entry/do/exit members by kind.
            "StateUsage" | "StateDefinition" if !projected => {
                for &r in &owned_rels[i] {
                    if ty(&elements[r]) != "StateSubactionMembership" {
                        continue;
                    }
                    let Some(prop) =
                        elements[r]
                            .get("kind")
                            .and_then(|v| v.as_str())
                            .and_then(|k| match k {
                                "entry" => Some("entryAction"),
                                "do" => Some("doAction"),
                                "exit" => Some("exitAction"),
                                _ => None,
                            })
                    else {
                        continue;
                    };
                    let target = elements[r]
                        .get("memberElement")
                        .cloned()
                        .filter(|v| v.get("@id").is_some())
                        .or_else(|| related_elems[r].first().map(|&k| id_ref(eid(&elements[k]))));
                    if let Some(v) = target {
                        derived.insert(prop.into(), v);
                    }
                }
            }
            // The verified requirement is the member's *referenced* target
            // — the chain's last link when the reference is a chain — not
            // the implicit member itself.
            "RequirementVerificationMembership" if !projected => {
                let target = related_elems[i].first().and_then(|&member| {
                    let refsub = owned_rels[member]
                        .iter()
                        .find(|&&rr| ty(&elements[rr]) == "ReferenceSubsetting")
                        .and_then(|&rr| {
                            elements[rr]
                                .get("referencedFeature")
                                .cloned()
                                .filter(|v| v.get("@id").is_some())
                        })?;
                    let chained = refsub
                        .get("@id")
                        .and_then(|v| v.as_str())
                        .and_then(|id| index.get(id))
                        .and_then(|&k| {
                            owned_rels[k]
                                .iter()
                                .filter(|&&rr| ty(&elements[rr]) == "FeatureChaining")
                                .filter_map(|&rr| elements[rr].get("chainingFeature").cloned())
                                .rfind(|v| v.get("@id").is_some())
                        });
                    Some(chained.unwrap_or(refsub))
                });
                if let Some(v) = target {
                    overrides.insert("verifiedRequirement".into(), v.clone());
                    overrides.insert("referencedConstraint".into(), v);
                }
            }
            // The requirements a verification case verifies: the
            // objective's RequirementVerificationMembership members.
            "VerificationCaseUsage" | "VerificationCaseDefinition" if !projected => {
                let mut verified = Vec::new();
                for &r in &owned_rels[i] {
                    if ty(&elements[r]) != "ObjectiveMembership" {
                        continue;
                    }
                    for &obj in &related_elems[r] {
                        for &rr in &owned_rels[obj] {
                            if ty(&elements[rr]) != "RequirementVerificationMembership" {
                                continue;
                            }
                            let target = elements[rr]
                                .get("memberElement")
                                .cloned()
                                .filter(|v| v.get("@id").is_some())
                                .or_else(|| {
                                    related_elems[rr]
                                        .first()
                                        .map(|&k| id_ref(eid(&elements[k])))
                                });
                            verified.extend(target);
                        }
                    }
                }
                if !verified.is_empty() {
                    derived.insert("verifiedRequirement".into(), Value::Array(verified));
                }
            }
            // The membership's referenced rendering: the member's
            // reference target, like ViewUsage::viewRendering below.
            "ViewRenderingMembership" if !projected => {
                let target = related_elems[i].first().and_then(|&member| {
                    owned_rels[member]
                        .iter()
                        .find(|&&rr| ty(&elements[rr]) == "ReferenceSubsetting")
                        .and_then(|&rr| {
                            elements[rr]
                                .get("referencedFeature")
                                .cloned()
                                .filter(|v| v.get("@id").is_some())
                        })
                });
                if let Some(v) = target {
                    overrides.insert("referencedRendering".into(), v);
                }
            }
            // The rendering a view uses: the ViewRenderingMembership
            // member's *referenced* rendering when the member is a
            // reference (`render asTreeDiagram;`), else the member itself.
            "ViewUsage" | "ViewDefinition" if !projected => {
                let member = owned_rels[i]
                    .iter()
                    .find(|&&r| ty(&elements[r]) == "ViewRenderingMembership")
                    .and_then(|&r| related_elems[r].first().copied());
                let target = member.and_then(|k| {
                    owned_rels[k]
                        .iter()
                        .find(|&&rr| ty(&elements[rr]) == "ReferenceSubsetting")
                        .and_then(|&rr| {
                            elements[rr]
                                .get("referencedFeature")
                                .cloned()
                                .filter(|v| v.get("@id").is_some())
                        })
                        .or_else(|| Some(id_ref(eid(&elements[k]))))
                });
                if let Some(v) = target {
                    derived.insert("viewRendering".into(), v);
                }
            }
            // The element whose metadata is accessed: the owned
            // Membership's member (the generic required-ref fill would
            // self-refer).
            "MetadataAccessExpression" if !projected => {
                let target = owned_rels[i]
                    .iter()
                    .find(|&&r| ty(&elements[r]) == "Membership")
                    .and_then(|&r| {
                        elements[r]
                            .get("memberElement")
                            .cloned()
                            .filter(|v| v.get("@id").is_some())
                            .or_else(|| {
                                related_elems[r].first().map(|&k| id_ref(eid(&elements[k])))
                            })
                    });
                if let Some(v) = target {
                    overrides.insert("referencedElement".into(), v);
                }
            }
            // ConjugatedPortTyping's type.
            "PortConjugation" => {
                if let Some(o) = rel_owner[i] {
                    let r = id_ref(eid(&elements[o]));
                    if !projected {
                        derived.insert("conjugatedPortDefinition".into(), r.clone());
                    }
                    derived.insert("conjugatedType".into(), r);
                }
            }
            "ConjugatedPortTyping" => {
                if let Some(t) = elements[i].get("type").cloned().filter(|v| !v.is_null()) {
                    derived.insert("conjugatedPortDefinition".into(), t);
                }
            }
            "TransitionUsage" if !projected => {
                if let Some(succ) = owned_kids
                    .iter()
                    .find(|&&k| ty(&elements[k]) == "SuccessionAsUsage")
                {
                    derived.insert("succession".into(), id_ref(eid(&elements[*succ])));
                }
            }
            // Association-family definitions: the end lists derive from the
            // owned end features, and associations are always sufficient at
            // the model level whatever the text spells (no `all` keyword) —
            // except flow definitions, which the pilot leaves insufficient.
            "InterfaceDefinition"
            | "ConnectionDefinition"
            | "AllocationDefinition"
            | "FlowDefinition"
            | "Association"
            | "AssociationStructure" => {
                let ends: Vec<Value> = owned_kids
                    .iter()
                    .filter(|&&k| elements[k].get("isEnd").and_then(|v| v.as_bool()) == Some(true))
                    .map(|&k| id_ref(eid(&elements[k])))
                    .collect();
                if !ends.is_empty() && !projected {
                    derived.insert("associationEnd".into(), Value::Array(ends.clone()));
                    derived.insert("connectionEnd".into(), Value::Array(ends.clone()));
                    if t == "InterfaceDefinition" {
                        derived.insert("interfaceEnd".into(), Value::Array(ends));
                    }
                }
                if t != "FlowDefinition" {
                    overrides.insert("isSufficient".into(), Value::Bool(true));
                }
            }
            "FlowUsage" | "SuccessionFlowUsage" | "Flow" | "SuccessionFlow" => {
                let flow_ends: Vec<usize> = owned_kids
                    .iter()
                    .copied()
                    .filter(|&k| ty(&elements[k]) == "FlowEnd")
                    .collect();
                if !flow_ends.is_empty() && !projected {
                    derived.insert(
                        "flowEnd".into(),
                        Value::Array(
                            flow_ends
                                .iter()
                                .map(|&k| id_ref(eid(&elements[k])))
                                .collect(),
                        ),
                    );
                    // The flow features: the source's output, the target's
                    // input (each FlowEnd's owned redefining feature).
                    let feature_of = |k: usize| -> Option<Value> {
                        owned_rels[k]
                            .iter()
                            .find(|&&r| ty(&elements[r]) == "FeatureMembership")
                            .and_then(|&r| related_elems[r].first())
                            .map(|&f| id_ref(eid(&elements[f])))
                    };
                    if let Some(v) = flow_ends.first().copied().and_then(feature_of) {
                        derived.insert("sourceOutputFeature".into(), v);
                    }
                    if let Some(v) = flow_ends.get(1).copied().and_then(feature_of) {
                        derived.insert("targetInputFeature".into(), v);
                    }
                }
                if let (Some(&p), false) = (
                    owned_kids
                        .iter()
                        .find(|&&k| ty(&elements[k]) == "PayloadFeature"),
                    projected,
                ) {
                    derived.insert("payloadFeature".into(), id_ref(eid(&elements[p])));
                }
            }
            "AcceptActionUsage" if !projected => {
                // payloadParameter = the first reference parameter (the
                // payload); receiverArgument = the receiver parameter's
                // bound value expression.
                let ref_params: Vec<usize> = owned_rels[i]
                    .iter()
                    .filter(|&&r| ty(&elements[r]) == "ParameterMembership")
                    .flat_map(|&r| related_elems[r].iter().copied())
                    .filter(|&k| matches!(ty(&elements[k]), "ReferenceUsage" | "Feature"))
                    .collect();
                if let Some(&p) = ref_params.first() {
                    derived.insert("payloadParameter".into(), id_ref(eid(&elements[p])));
                }
                if let Some(&r) = ref_params.get(1) {
                    if let Some(&a) = owned_rels[r]
                        .iter()
                        .find(|&&fv| ty(&elements[fv]) == "FeatureValue")
                        .and_then(|&fv| related_elems[fv].first())
                    {
                        derived.insert("receiverArgument".into(), id_ref(eid(&elements[a])));
                    }
                }
            }
            "PerformActionUsage"
            | "EventOccurrenceUsage"
            | "ExhibitStateUsage"
            | "IncludeUseCaseUsage"
                if !projected =>
            {
                // The referenced action/occurrence — dereferenced through
                // an owned feature chain to its target (the pilot resolves
                // `perform a.b` to `b`, not to the chain feature), else
                // the usage itself.
                let referenced = owned_rels[i]
                    .iter()
                    .find(|&&r| ty(&elements[r]) == "ReferenceSubsetting")
                    .and_then(|&r| elements[r].get("referencedFeature").cloned())
                    .filter(|v| !v.is_null())
                    .map(|v| {
                        ref_of(&v)
                            .and_then(|id| index.get(&id).copied())
                            .and_then(|k| {
                                owned_rels[k]
                                    .iter()
                                    .rev()
                                    .find(|&&r| ty(&elements[r]) == "FeatureChaining")
                                    .and_then(|&r| elements[r].get("chainingFeature").cloned())
                            })
                            .unwrap_or(v)
                    })
                    .unwrap_or_else(|| self_ref.clone());
                derived.insert("performedAction".into(), referenced.clone());
                derived.insert("eventOccurrence".into(), referenced.clone());
                derived.insert("exhibitedState".into(), referenced.clone());
                derived.insert("useCaseIncluded".into(), referenced);
            }
            _ => {}
        }

        // Annotating elements. `annotation` is the owning Annotation (the
        // prefix-annotation shape) followed by the owned ones (`about`
        // clauses); `ownedAnnotatingRelationship` is the owned ones that
        // annotate another element, the complement of `ownedAnnotation`.
        // `annotatedElement` follows those Annotations; an annotating
        // element with none annotates its owner implicitly.
        // All of them are projected from the layer (a target outside the
        // model is a `Reference` there); this is the fallback.
        if !projected && conforms(&t, "AnnotatingElement") {
            let owning = owner_rel[i].filter(|&r| ty(&elements[r]) == "Annotation");
            let owned_relating: Vec<usize> = owned_annotations
                .iter()
                .copied()
                .filter(|&r| !annotates_self(r))
                .collect();
            let mut annotation: Vec<usize> = owning.into_iter().collect();
            annotation.extend(owned_relating.iter().copied());
            let mut annotated: Vec<Value> = annotation
                .iter()
                .filter_map(|&r| {
                    elements[r]
                        .get("annotatedElement")
                        .cloned()
                        .filter(|v| !v.is_null())
                        // The owning Annotation may be completed from its
                        // owner (the Annotation ends above); apply the same
                        // rule here, whatever the element order.
                        .or_else(|| {
                            (Some(r) == owning)
                                .then(|| rel_owner[r].map(|o| id_ref(eid(&elements[o]))))
                                .flatten()
                        })
                })
                .collect();
            if annotated.is_empty() {
                annotated.extend(owner_idx.map(|o| id_ref(eid(&elements[o]))));
            }
            if matches!(
                t.as_str(),
                "Comment" | "Documentation" | "TextualRepresentation"
            ) {
                if let Some(first) = annotated.first() {
                    derived.insert("documentedElement".into(), first.clone());
                    derived.insert("representedElement".into(), first.clone());
                }
            }
            derived.insert("annotatedElement".into(), Value::Array(annotated));
            let refs = |rels: &[usize]| -> Value {
                Value::Array(rels.iter().map(|&r| id_ref(eid(&elements[r]))).collect())
            };
            derived.insert("ownedAnnotatingRelationship".into(), refs(&owned_relating));
            derived.insert("annotation".into(), refs(&annotation));
        }
        if !projected && t == "MultiplicityRange" {
            let bounds: Vec<Value> = owned_rels[i]
                .iter()
                .filter(|&&r| ty(&elements[r]) == "OwningMembership")
                .flat_map(|&r| related_elems[r].iter().map(|&k| id_ref(eid(&elements[k]))))
                .collect();
            if !bounds.is_empty() {
                derived.insert(
                    "lowerBound".into(),
                    if bounds.len() == 2 {
                        bounds[0].clone()
                    } else {
                        Value::Null
                    },
                );
                derived.insert("upperBound".into(), bounds.last().unwrap().clone());
                derived.insert("bound".into(), Value::Array(bounds));
            }
        }

        // Membership extras.
        if is_membership(&t) {
            if let Some(target) = elements[i]
                .get("memberElement")
                .cloned()
                .or_else(|| related_elems[i].first().map(|&k| id_ref(eid(&elements[k]))))
            {
                if let Some(id) = ref_of(&target) {
                    if !projected {
                        derived.insert("memberElementId".into(), Value::String(id.clone()));
                    }
                    if elements[i].get("memberName").is_none() {
                        let name = index
                            .get(&id)
                            .and_then(|&k| {
                                elements[k]
                                    .get("declaredName")
                                    .filter(|v| !v.is_null())
                                    .cloned()
                                    .or_else(|| eff_names[k].clone().map(Value::String))
                            })
                            .unwrap_or(Value::Null);
                        derived.insert("memberName".into(), name);
                    }
                    if elements[i].get("memberShortName").is_none() {
                        let name = index
                            .get(&id)
                            .and_then(|&k| elements[k].get("declaredShortName").cloned())
                            .unwrap_or(Value::Null);
                        derived.insert("memberShortName".into(), name);
                    }
                }
                derived.insert("memberElement".into(), target);
            }
            if !projected {
                derived.insert(
                    "membershipOwningNamespace".into(),
                    rel_owner[i]
                        .map(|o| id_ref(eid(&elements[o])))
                        .unwrap_or(Value::Null),
                );
            }
        }

        // Overlay: computed derived values (only those the metaclass
        // declares — `additionalProperties: false`), then catalog defaults
        // for anything still missing.
        let el = &mut elements[i];
        el.insert("isImpliedIncluded".into(), json!(implied_included));
        if let Some(props) = metaclass_props(&t) {
            // The property list is sorted by name (asserted in this
            // module's tests), so membership is a search over the static
            // table rather than a set built afresh for every element.
            let declared = |name: &str| props.binary_search_by_key(&name, |(n, _)| n).is_ok();
            for (k, v) in derived {
                if declared(&k) {
                    el.entry(k).or_insert(v);
                }
            }
            for (k, v) in std::mem::take(&mut overrides) {
                if declared(&k) {
                    el.insert(k, v);
                }
            }
            let member_alias = el
                .get("memberElement")
                .cloned()
                .filter(|v| !v.is_null())
                .or_else(|| {
                    el.get("ownedRelatedElement")
                        .and_then(|v| v.as_array())
                        .and_then(|a| a.first())
                        .cloned()
                });
            for (name, shape) in props.iter() {
                if el.get(*name).map(|v| !v.is_null()).unwrap_or(false) {
                    continue;
                }
                let default = match shape {
                    b'A' => Value::Array(Vec::new()),
                    b'B' => Value::Bool(false),
                    // Required references: membership redefinitions alias
                    // the member element; anything else self-references —
                    // the "passthrough" approximation, documented.
                    b'R' => {
                        if is_membership(&t) && member_alias.is_some() {
                            member_alias.clone().unwrap()
                        } else {
                            id_ref(&this_id)
                        }
                    }
                    _ => Value::Null,
                };
                el.insert((*name).to_string(), default);
            }
            // Drop compact-form properties the metaclass doesn't declare
            // (dialect mismatches would trip additionalProperties).
            let keys: Vec<String> = el
                .keys()
                .filter(|k| !k.starts_with('@') && !declared(k) && *k != "elementId")
                .cloned()
                .collect();
            for k in keys {
                el.remove(&k);
            }
        } else {
            for (k, v) in derived {
                el.entry(k).or_insert(v);
            }
            for (k, v) in std::mem::take(&mut overrides) {
                el.insert(k, v);
            }
        }
    }

    Value::Array(elements.into_iter().map(Value::Object).collect())
}

/// Unresolved-reference recovery (compact-space pre-pass): for every
/// `{"@ref": name}` about to become a dangling `@id`, attach one
/// `TextualRepresentation` (language [`UNRESOLVED_REP_LANGUAGE`], body =
/// `name`) to the referencing element's document root, deduplicated per
/// (root, name). Injected in compact shape so the ordinary full-form
/// derivation completes ownership lists, defaults, and derived properties
/// exactly as for hand-written `rep` members.
fn inject_unresolved_reps(elements: &mut Vec<Map<String, Value>>) {
    let by_id: HashMap<String, usize> = elements
        .iter()
        .enumerate()
        .map(|(i, e)| (eid(e).to_string(), i))
        .collect();
    fn collect_refs(v: &Value, out: &mut Vec<String>) {
        match v {
            Value::Object(m) => {
                if let Some(Value::String(s)) = m.get("@ref") {
                    // Id-shaped spellings are ids, not names to recover.
                    if Uuid::parse_str(s.trim_matches('\'')).is_ok() {
                        return;
                    }
                    out.push(s.clone());
                    return;
                }
                m.values().for_each(|x| collect_refs(x, out));
            }
            Value::Array(a) => a.iter().for_each(|x| collect_refs(x, out)),
            _ => {}
        }
    }
    // Document root of element `i`: follow owningRelationship →
    // owningRelatedElement to the top.
    let root_of = |mut i: usize| -> usize {
        for _ in 0..elements.len() {
            let Some(rel) = elements[i]
                .get("owningRelationship")
                .and_then(|v| v.get("@id"))
                .and_then(|v| v.as_str())
                .and_then(|id| by_id.get(id))
            else {
                return i;
            };
            let Some(owner) = elements[*rel]
                .get("owningRelatedElement")
                .and_then(|v| v.get("@id"))
                .and_then(|v| v.as_str())
                .and_then(|id| by_id.get(id))
            else {
                return *rel;
            };
            i = *owner;
        }
        i
    };

    // Collect (document root, name) pairs in an immutable phase; the
    // mutation loop below must not overlap the `root_of` borrow.
    let mut sites: Vec<(usize, String)> = Vec::new();
    for (i, el) in elements.iter().enumerate() {
        let mut refs = Vec::new();
        el.values().for_each(|v| collect_refs(v, &mut refs));
        if !refs.is_empty() {
            let root = root_of(i);
            sites.extend(refs.into_iter().map(|s| (root, s)));
        }
    }

    let mut seen: std::collections::HashSet<(usize, String)> = Default::default();
    for (root, name) in sites {
        if !seen.insert((root, name.clone())) {
            continue;
        }
        let root_id = eid(&elements[root]).to_string();
        let mem_id = Uuid::new_v5(
            &Uuid::NAMESPACE_OID,
            format!("unresolved-rep-m:{root_id}:{name}").as_bytes(),
        )
        .to_string();
        let rep_id = Uuid::new_v5(
            &Uuid::NAMESPACE_OID,
            format!("unresolved-rep:{root_id}:{name}").as_bytes(),
        )
        .to_string();
        let mut mem = Map::new();
        mem.insert("@id".into(), json!(mem_id));
        mem.insert("@type".into(), json!("OwningMembership"));
        mem.insert("elementId".into(), json!(mem_id));
        mem.insert("isImplied".into(), json!(false));
        mem.insert("visibility".into(), json!("public"));
        mem.insert("ownedRelatedElement".into(), json!([{ "@id": rep_id }]));
        mem.insert("owningRelatedElement".into(), json!({ "@id": root_id }));
        let mut rep = Map::new();
        rep.insert("@id".into(), json!(rep_id));
        rep.insert("@type".into(), json!("TextualRepresentation"));
        rep.insert("elementId".into(), json!(rep_id));
        rep.insert("language".into(), json!(UNRESOLVED_REP_LANGUAGE));
        rep.insert("body".into(), json!(name));
        rep.insert("owningRelationship".into(), json!({ "@id": mem_id }));
        if let Some(Value::Array(owned)) = elements[root].get_mut("ownedRelationship") {
            owned.push(json!({ "@id": mem_id }));
        } else {
            elements[root].insert("ownedRelationship".into(), json!([{ "@id": mem_id }]));
        }
        elements.push(mem);
        elements.push(rep);
    }
}

fn patch_refs(v: &mut Value) {
    match v {
        Value::Object(m) => {
            if let Some(Value::String(s)) = m.get("@ref") {
                // An id-shaped spelling is a reference by id (the lift
                // spells a target it cannot name — an unnamed element, or
                // a library element with no library loaded — as its quoted
                // id): keep the id. Anything else gets a deterministic
                // dangling id.
                let id = match Uuid::parse_str(s.trim_matches('\'')) {
                    Ok(id) => id.to_string(),
                    Err(_) => dangling_id(s),
                };
                m.clear();
                m.insert("@id".into(), Value::String(id));
                return;
            }
            for x in m.values_mut() {
                patch_refs(x);
            }
        }
        Value::Array(a) => {
            for x in a {
                patch_refs(x);
            }
        }
        _ => {}
    }
}

/// Effective name of an element (pilot `Element::effectiveName`): the
/// declared name, else the name of the first feature this one explicitly
/// redefines (`Feature::namingFeature`) or references (SysML reference
/// forms), else — for chain features — the last chaining target's name.
///
/// One naming rule, four representations. The implementations are this
/// one (over the full form's element maps, the only one that also
/// derives the positional implied names),
/// `json::Builder::graph_effective_name` (over the lowered element
/// graph, where `Builder::effective_name` is the declaration-only half),
/// `lift::Lifter::effective_name` (over payload JSON), and the fixpoint
/// inside `ids::walk` (over a compact payload, for id segments). They
/// agree by construction and by the differential test in the round-trip
/// gate; a change to one belongs in all of them.
fn effective_name_of(
    i: usize,
    elements: &[Map<String, Value>],
    owned_rels: &[Vec<usize>],
    index: &HashMap<String, usize>,
    lib_id_names: &HashMap<&str, &str>,
    depth: usize,
) -> Option<String> {
    if depth > 32 {
        return None;
    }
    if let Some(n) = elements[i].get("declaredName").and_then(|v| v.as_str()) {
        return Some(n.to_string());
    }
    let resolve = |tid: String| -> Option<String> {
        if let Some(&k) = index.get(&tid) {
            return effective_name_of(k, elements, owned_rels, index, lib_id_names, depth + 1);
        }
        lib_id_names.get(tid.as_str()).map(|n| n.to_string())
    };
    // Naming precedence mirrors the pilot: explicitly redefined feature,
    // then the computed (implied positional) redefinition, then the
    // referenced feature, then a chain's last link.
    let mut reference: Option<String> = None;
    let mut last_chain: Option<String> = None;
    for &r in &owned_rels[i] {
        if elements[r].get("isImplied").and_then(|v| v.as_bool()) == Some(true) {
            continue;
        }
        match ty(&elements[r]) {
            "Redefinition" => {
                if let Some(n) = elements[r]
                    .get("redefinedFeature")
                    .and_then(ref_of)
                    .and_then(&resolve)
                {
                    return Some(n);
                }
            }
            "ReferenceSubsetting" => {
                if reference.is_none() {
                    reference = elements[r].get("referencedFeature").and_then(ref_of);
                }
            }
            "FeatureChaining" => {
                last_chain = elements[r].get("chainingFeature").and_then(ref_of);
            }
            _ => {}
        }
    }
    if let Some(n) = implied_member_name(i, elements, index) {
        return Some(n);
    }
    // Actor/stakeholder parameters implicitly *subset* the library
    // `actors`/`stakeholders` collections — subsetting carries no name, so
    // a reference-spelled `actor ::> x;` stays anonymous (pilot naming).
    let owning_ty = elements[i]
        .get("owningRelationship")
        .and_then(ref_of)
        .and_then(|id| index.get(&id).copied())
        .map(|r| ty(&elements[r]));
    if matches!(owning_ty, Some("ActorMembership" | "StakeholderMembership")) {
        return None;
    }
    if let Some(n) = reference.and_then(&resolve) {
        return Some(n);
    }
    last_chain.and_then(resolve)
}

/// Positional names of implicitly-redefining members (the pilot's computed
/// redefinitions are its `namingFeature`s): the two bare ends of a binary
/// connector-family usage redefine the library binary ends (`source` /
/// `target`; successions `earlierOccurrence` / `laterOccurrence`), a flow's
/// payload feature redefines `payload`, and a transition trigger the
/// `accepter` action. This toolkit does not materialize those implied
/// Redefinition elements yet, but the names are what the pilot serializes
/// as `memberName`/`name`.
fn implied_member_name(
    i: usize,
    elements: &[Map<String, Value>],
    index: &HashMap<String, usize>,
) -> Option<String> {
    let t = ty(&elements[i]);
    let rel_id = elements[i].get("owningRelationship").and_then(ref_of)?;
    let rel = *index.get(&rel_id)?;
    let rel_ty = ty(&elements[rel]);
    if t == "PayloadFeature" {
        return Some("payload".to_string());
    }
    if t == "AcceptActionUsage" && rel_ty == "TransitionFeatureMembership" {
        return Some("accepter".to_string());
    }
    // Return parameters implicitly redefine the function's result.
    if rel_ty == "ReturnParameterMembership" {
        return Some("result".to_string());
    }
    // Subject parameters implicitly redefine the library Case/Requirement
    // `subj` parameter (SysML 7.19), including a satisfy's `by` subject.
    if rel_ty == "SubjectMembership" {
        return Some("subj".to_string());
    }
    // Objective requirements redefine the library Case `obj` parameter;
    // view renderings the `viewRendering` feature.
    if rel_ty == "ObjectiveMembership" {
        return Some("obj".to_string());
    }
    if rel_ty == "ViewRenderingMembership" {
        return Some("viewRendering".to_string());
    }
    // Positional invocation/constructor arguments implicitly redefine the
    // callee's `in` parameters in order, which names them (named arguments
    // carry an explicit ParameterRedefinition and never reach here).
    if rel_ty == "ParameterMembership" {
        return invocation_arg_name(i, rel, elements, index);
    }
    if rel_ty != "EndFeatureMembership" {
        return None;
    }
    // Owner and its end-membership positions.
    let owner_id = elements[rel].get("owningRelatedElement").and_then(ref_of)?;
    let owner = *index.get(&owner_id)?;
    let owner_ty = ty(&elements[owner]);
    let names: [&str; 2] = match owner_ty {
        "SuccessionAsUsage" | "Succession" | "TransitionUsage" => {
            ["earlierOccurrence", "laterOccurrence"]
        }
        // Binding ends redefine the library `Links::SelfLink` ends.
        "BindingConnectorAsUsage" | "BindingConnector" => ["thisThing", "sameThing"],
        "ConnectionUsage"
        | "AllocationUsage"
        | "InterfaceUsage"
        | "Connector"
        | "FlowUsage"
        | "SuccessionFlowUsage"
        | "Flow"
        | "SuccessionFlow" => ["source", "target"],
        _ => return None,
    };
    let ends: Vec<&str> = elements[owner]
        .get("ownedRelationship")
        .and_then(|v| v.as_array())?
        .iter()
        .filter_map(|r| r.get("@id").and_then(|x| x.as_str()))
        .filter(|id| {
            index
                .get(*id)
                .is_some_and(|&k| ty(&elements[k]) == "EndFeatureMembership")
        })
        .collect();
    if ends.len() != 2 {
        return None;
    }
    let pos = ends.iter().position(|&id| id == rel_id)?;
    Some(names[pos].to_string())
}

/// The positional name of an invocation/constructor argument: the pilot
/// implicitly redefines the callee's input parameters (`in`, `inout`) in
/// declaration order, an unnamed one holding its position. Only derivable
/// when the callee is in-document; a feature owning any Redefinition is a
/// named argument and keeps that name (even unresolved).
fn invocation_arg_name(
    i: usize,
    rel: usize,
    elements: &[Map<String, Value>],
    index: &HashMap<String, usize>,
) -> Option<String> {
    let has_redefinition = elements[i]
        .get("ownedRelationship")
        .and_then(|v| v.as_array())
        .is_some_and(|a| {
            a.iter()
                .filter_map(ref_of)
                .filter_map(|id| index.get(&id).copied())
                .any(|r| ty(&elements[r]) == "Redefinition")
        });
    if has_redefinition {
        return None;
    }
    let owner_id = elements[rel].get("owningRelatedElement").and_then(ref_of)?;
    let owner = *index.get(&owner_id)?;
    let owner_rels: Vec<usize> = elements[owner]
        .get("ownedRelationship")
        .and_then(|v| v.as_array())?
        .iter()
        .filter_map(ref_of)
        .filter_map(|id| index.get(&id).copied())
        .collect();
    // An accept action's reference parameters are its payload and receiver
    // (pilot AcceptParameterPart; trigger invocations are expressions and
    // don't count positions).
    if ty(&elements[owner]) == "AcceptActionUsage" {
        let ref_params: Vec<usize> = owner_rels
            .iter()
            .copied()
            .filter(|&r| {
                ty(&elements[r]) == "ParameterMembership"
                    && elements[r]
                        .get("ownedRelatedElement")
                        .and_then(|v| v.as_array())
                        .and_then(|a| a.first())
                        .and_then(ref_of)
                        .and_then(|id| index.get(&id).copied())
                        .is_some_and(|k| matches!(ty(&elements[k]), "ReferenceUsage" | "Feature"))
            })
            .collect();
        let pos = ref_params.iter().position(|&r| r == rel)?;
        return ["payload", "receiver"].get(pos).map(|n| n.to_string());
    }
    if !matches!(
        ty(&elements[owner]),
        "InvocationExpression" | "ConstructorExpression"
    ) {
        return None;
    }
    // The callee: the invocation's fn/type Membership target (an
    // OwningMembership when the callee is a feature chain).
    let callee_id = owner_rels
        .iter()
        .find(|&&r| matches!(ty(&elements[r]), "Membership" | "OwningMembership"))
        .and_then(|&r| elements[r].get("memberElement"))
        .and_then(ref_of)?;
    let callee = *index.get(&callee_id)?;
    let params: Vec<Option<&str>> = elements[callee]
        .get("ownedRelationship")
        .and_then(|v| v.as_array())?
        .iter()
        .filter_map(ref_of)
        .filter_map(|id| index.get(&id).copied())
        .filter_map(|r| {
            elements[r]
                .get("ownedRelatedElement")
                .and_then(|v| v.as_array())
                .and_then(|a| a.first())
                .and_then(ref_of)
                .and_then(|id| index.get(&id).copied())
        })
        .filter(|&k| {
            matches!(
                elements[k].get("direction").and_then(|v| v.as_str()),
                Some("in" | "inout")
            )
        })
        .map(|k| elements[k].get("declaredName").and_then(|v| v.as_str()))
        .collect();
    let pos = owner_rels
        .iter()
        .filter(|&&r| ty(&elements[r]) == "ParameterMembership")
        .position(|&r| r == rel)?;
    params.get(pos).copied().flatten().map(|n| n.to_string())
}

fn qname_of(
    i: usize,
    elements: &[Map<String, Value>],
    owner_rel: &[Option<usize>],
    rel_owner: &[Option<usize>],
    eff_names: &[Option<String>],
    qnames: &mut Vec<Option<String>>,
) -> Option<String> {
    if let Some(q) = &qnames[i] {
        return Some(q.clone());
    }
    let name = elements[i]
        .get("declaredName")
        .and_then(|v| v.as_str())
        .or_else(|| {
            elements[i]
                .get("declaredShortName")
                .and_then(|v| v.as_str())
        })
        .map(|s| s.to_string())
        .or_else(|| eff_names[i].clone())?;
    let escaped = sysmlv2_syntax::ast::escape_name(&name);
    let owner = owner_rel[i].and_then(|r| rel_owner[r]);
    let q = match owner {
        None => escaped,
        Some(o) if ty(&elements[o]) == "Namespace" && owner_rel[o].is_none() => escaped,
        Some(o) => {
            let oq = qname_of(o, elements, owner_rel, rel_owner, eff_names, qnames)?;
            format!("{oq}::{escaped}")
        }
    };
    qnames[i] = Some(q.clone());
    Some(q)
}

/// Fill `source` / `target` / `relatedElement` and redefined-name aliases.
fn fill_relationship_endpoints(
    derived: &mut Map<String, Value>,
    elements: &[Map<String, Value>],
    i: usize,
    rel_owner: &[Option<usize>],
    related_elems: &[Vec<usize>],
    projected: bool,
) {
    let el = &elements[i];
    let t = ty(el);
    let owner = rel_owner[i].map(|o| id_ref(eid(&elements[o])));
    let owned: Vec<Value> = related_elems[i]
        .iter()
        .map(|&k| id_ref(eid(&elements[k])))
        .collect();
    let get = |k: &str| el.get(k).cloned().filter(|v| !v.is_null());

    let (source, target): (Vec<Value>, Vec<Value>) = if is_membership(t) {
        let target = get("memberElement")
            .or_else(|| owned.first().cloned())
            .into_iter()
            .collect();
        (owner.into_iter().collect(), target)
    } else if is_import(t) {
        let target = get("importedNamespace")
            .or_else(|| get("importedMembership"))
            .into_iter()
            .collect();
        (owner.into_iter().collect(), target)
    } else {
        match t {
            "Subclassification" | "Specialization" => {
                let source = get("subclassifier").or_else(|| get("specific"));
                let target = get("superclassifier").or_else(|| get("general"));
                if let Some(s) = &source {
                    derived.insert("specific".into(), s.clone());
                    derived.insert("subclassifier".into(), s.clone());
                }
                if let Some(tt) = &target {
                    derived.insert("general".into(), tt.clone());
                    derived.insert("superclassifier".into(), tt.clone());
                }
                (source.into_iter().collect(), target.into_iter().collect())
            }
            "FeatureTyping" | "ConjugatedPortTyping" => {
                let source = get("typedFeature");
                let target = get("type");
                if let Some(s) = &source {
                    derived.insert("specific".into(), s.clone());
                }
                if let Some(tt) = &target {
                    derived.insert("general".into(), tt.clone());
                }
                (source.into_iter().collect(), target.into_iter().collect())
            }
            "Subsetting" | "Redefinition" | "ReferenceSubsetting" | "CrossSubsetting" => {
                let source = get("subsettingFeature")
                    .or_else(|| get("redefiningFeature"))
                    .or_else(|| get("referencingFeature"))
                    .or_else(|| get("crossingFeature"))
                    .or_else(|| owner.clone());
                let target = get("subsettedFeature")
                    .or_else(|| get("redefinedFeature"))
                    .or_else(|| get("referencedFeature"))
                    .or_else(|| get("crossedFeature"));
                if let Some(s) = &source {
                    derived.insert("specific".into(), s.clone());
                    derived.insert("subsettingFeature".into(), s.clone());
                }
                if let Some(tt) = &target {
                    derived.insert("general".into(), tt.clone());
                    derived.insert("subsettedFeature".into(), tt.clone());
                }
                (source.into_iter().collect(), target.into_iter().collect())
            }
            "Dependency" => {
                let client = el
                    .get("client")
                    .and_then(|v| v.as_array())
                    .cloned()
                    .unwrap_or_default();
                let supplier = el
                    .get("supplier")
                    .and_then(|v| v.as_array())
                    .cloned()
                    .unwrap_or_default();
                (client, supplier)
            }
            "Annotation" => {
                // The annotating element: the owner in the `about` shape,
                // the owned annotating element otherwise (derived above, or
                // spelled by a foreign payload); the annotated element may
                // likewise have been completed from the owner.
                let source = derived
                    .get("annotatingElement")
                    .cloned()
                    .or_else(|| get("annotatingElement"))
                    .or_else(|| owner.clone());
                let target = get("annotatedElement")
                    .or_else(|| derived.get("annotatedElement").cloned())
                    .into_iter()
                    .collect();
                (source.into_iter().collect(), target)
            }
            "Conjugation" | "PortConjugation" => {
                let source = get("conjugatedType").or_else(|| owner.clone());
                let target = get("originalType").into_iter().collect();
                (source.into_iter().collect(), target)
            }
            "Disjoining" => {
                let source = get("typeDisjoined").or_else(|| owner.clone());
                let target = get("disjoiningType");
                (source.into_iter().collect(), target.into_iter().collect())
            }
            "FeatureInverting" => {
                let source = get("featureInverted").or_else(|| owner.clone());
                let target = get("invertingFeature");
                (source.into_iter().collect(), target.into_iter().collect())
            }
            "TypeFeaturing" => {
                let source = get("featureOfType").or_else(|| owner.clone());
                let target = get("featuringType");
                (source.into_iter().collect(), target.into_iter().collect())
            }
            "Unioning"
            | "Intersecting"
            | "Differencing"
            | "FeatureChaining"
            | "FeatureValue"
            | "ElementFilterMembership" => {
                let target = get("unioningType")
                    .or_else(|| get("intersectingType"))
                    .or_else(|| get("differencingType"))
                    .or_else(|| get("chainingFeature"))
                    .or_else(|| owned.first().cloned())
                    .into_iter()
                    .collect();
                (owner.into_iter().collect(), target)
            }
            _ => return, // not a relationship
        }
    };
    if !projected {
        let mut related: Vec<Value> = source.clone();
        related.extend(target.clone());
        derived.insert("relatedElement".into(), Value::Array(related));
    }
    derived.insert("source".into(), Value::Array(source));
    derived.insert("target".into(), Value::Array(target));
}

/// Append the implied relationships the derivation layer holds for every
/// projected element (SysML 8.4.2 Tables 31/32 library specializations and
/// the variant specializations): one array element each, listed under
/// the owner's `ownedRelationship`, with the owned properties the layer
/// spells (`isImplied`, the two ends) and the structure the full form
/// expects of a relationship owned directly by its specific side.
fn add_implied_relationships(
    elements: &mut Vec<Map<String, Value>>,
    resolved: &mut crate::json::ResolvedModel,
) {
    let mut additions: Vec<(usize, Map<String, Value>)> = Vec::new();
    for (i, el) in elements.iter().enumerate() {
        let own_id = eid(el);
        let t = ty(el);
        // Same id *and* same metaclass, as the projection requires.
        let Some(e) = resolved
            .element_by_id(own_id)
            .filter(|&e| resolved.element_type(e) == t)
        else {
            continue;
        };
        for r in resolved.implied_relationships(e) {
            let rel_id = resolved.element_id(r).to_string();
            let mut rel = Map::new();
            rel.insert("@type".into(), json!(resolved.element_type(r)));
            rel.insert("@id".into(), json!(rel_id));
            rel.insert("elementId".into(), json!(rel_id));
            rel.insert("isImpliedIncluded".into(), json!(true));
            rel.insert("ownedRelationship".into(), json!([]));
            rel.insert("ownedRelatedElement".into(), json!([]));
            rel.insert("owningRelatedElement".into(), id_ref(own_id));
            rel.insert("owningRelationship".into(), Value::Null);
            rel.extend(resolved.element_properties(r));
            rel.insert("aliasIds".into(), json!([]));
            rel.insert("declaredName".into(), Value::Null);
            rel.insert("declaredShortName".into(), Value::Null);
            additions.push((i, rel));
        }
    }
    for (owner_idx, rel) in additions {
        let rel_ref = id_ref(eid(&rel));
        if let Some(Value::Array(rels)) = elements[owner_idx].get_mut("ownedRelationship") {
            rels.push(rel_ref);
        }
        elements.push(rel);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The generated property catalog is looked up by binary search, in
    /// the metaclass table and in every property list. Regenerating the
    /// tables in another order would make those searches miss silently —
    /// properties would go missing from the exported form — so the order
    /// is asserted here rather than assumed.
    #[test]
    fn the_property_catalog_is_sorted_for_lookup() {
        assert!(
            METACLASS_PROPS.windows(2).all(|w| w[0].0 < w[1].0),
            "the metaclass table must be sorted by name"
        );
        for (metaclass, props) in METACLASS_PROPS {
            assert!(
                props.windows(2).all(|w| w[0].0 < w[1].0),
                "{metaclass}'s property list must be sorted by name"
            );
            for (name, _) in *props {
                assert_eq!(
                    metaclass_props(metaclass).and_then(|p| p
                        .binary_search_by_key(name, |(n, _)| n)
                        .ok()
                        .map(|i| p[i].0)),
                    Some(*name)
                );
            }
        }
    }
}
