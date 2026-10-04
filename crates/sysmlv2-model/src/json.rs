//! Compact JSON serialization of a parsed model.
//!
//! Implements the KerML clause 10.4 "JSON Serialization" mapping in its
//! *compact* form: only what the textual notation states — owned (non-derived)
//! properties, no implied relationships (`isImpliedIncluded: false` on every
//! element), one flat JSON array per root namespace, every cross-reference an
//! `{"@id": ...}` object (clause 10.4.4).
//!
//! Element IDs are deterministic UUIDv5 values derived from each element's
//! ownership path, so serializing the same source always yields the same
//! output (good for diffing and snapshot tests). Tools that require random
//! IDs can post-process.
//!
//! References that cannot be resolved within the parsed source (typically
//! standard-library names such as `ScalarValues::Real`) are emitted as
//! `{"@ref": "<qualified name as written>"}` — a documented interim deviation
//! until multi-file/library resolution lands (which replaces these with the
//! normative UUIDv5 library IDs).

mod behavior;
mod callable_bodies;
mod cases;
mod closures;
mod derived;
mod derived_compositions;
mod direction_proof;
mod exposure;
mod feature_type_projection;
mod literal_inheritance;
mod membership_context;
mod metadata_associations;
mod model_level_evaluability;
use membership_context::{ImportProjection, MembershipContext, MembershipProjection};
mod dynamic_graph;
mod dynamic_invocations;
mod generated_defaults;
mod implied;
mod import_memberships;
mod library_plans;
pub(crate) use library_plans::{LibraryEnumTypes, LibraryPlans};
mod local_featuring;
mod membership_evidence;
mod membership_projection;
#[cfg(test)]
mod named_argument_index_tests;
pub(crate) mod naming;
mod operations;
mod owned_results;
mod parameter_context;
mod parameters;
mod positional;
mod positional_delta;
pub(crate) mod provider_completeness;
mod publication;
mod recorded_lookup;
mod redefinition_provenance;
mod result_redefinition;
mod runtime_frames;
mod scope_table;
mod semantic;
mod semantic_batch;
mod semantic_ownership;
pub mod settled;
mod structural_index;
mod succession_endpoints;
mod type_features;
mod type_inputs;
mod type_relations;
pub use type_features::{TypeFeatureReport, TypeFeatures};
pub use type_inputs::{FunctionResultReport, TypeInputIssue, TypeInputReport};
mod invocation_bindings;
pub use invocation_bindings::{
    InvocationBinding, InvocationBindingIssue, InvocationBindingReport, InvocationBindings,
};
mod constructor_bindings;
pub use constructor_bindings::{
    ConstructorBinding, ConstructorBindingIssue, ConstructorBindingReport, ConstructorBindings,
    ConstructorDefaultBinding, ConstructorDefaultReport, ConstructorResult,
    ConstructorResultReport, ConstructorSelection, ConstructorSelectionReport,
};
mod cardinality;
pub use cardinality::{CardinalityBounds, CardinalityIssue, CardinalityReport};
mod end_constancy;
mod typeops;
pub use end_constancy::{EndConstancyIssue, EndConstancyReport};
mod usage_variability;
pub use usage_variability::{UsageVariabilityIssue, UsageVariabilityReport};
pub(crate) mod value_context;
pub(crate) use callable_bodies::calculation_like;
pub use callable_bodies::{CallableBody, CallableResult};
pub use closures::{CLOSURE_NAMES, ClosurePolicy};
pub use derived::dangling_id;
pub use derived::{
    CatalogEntry, Derived, DerivedValue, Derives, PropertyShape, Reference, computed_names,
    derives, derives_under, is_owned_property, metaclass_conforms, property_catalog,
};
pub(crate) use direction_proof::{DirectionFact, DirectionProof, authored_direction};
pub use feature_type_projection::{FeatureTypeIssue, FeatureTypeReport};
pub use model_level_evaluability::{
    ModelLevelEvaluability, ModelLevelEvaluabilityReport, ModelLevelEvaluabilityUnknown,
};
pub use operations::{
    OperationArgumentIssue, OperationError, OperationExecutionSignature, OperationResult,
    operation_execution_signature,
};
pub use parameter_context::RuntimeParameterSelection;
pub use parameters::{ParameterBinding, ReferenceIdentity};
pub use runtime_frames::{RuntimeFrame, RuntimeFrameProof};
pub use semantic::{ConditionalPropertyCapability, conditional_property_capability};
pub use semantic::{PropertyError, PropertyIssue, SemanticExportError};
pub use value_context::{ValueScopeDecision, ValueScopeResolver};

use serde_json::{Map, Value, json};
use std::collections::{HashMap, HashSet};
use std::sync::Arc;

/// Recursion budget shared by name lookup and the import, heritage and
/// semantic-metadata walks: a chain deeper than this is treated as a
/// cycle and cut. Inherited-member enumeration reports reaching it
/// through [`InheritedBindings::truncated`]; lookup stays silent, as a
/// missing name is already a diagnostic.
pub(crate) const MAX_RESOLUTION_DEPTH: usize = 24;
use sysmlv2_syntax::ast::*;
use sysmlv2_syntax::span::Span;
use uuid::Uuid;

/// Serialize a parsed source unit to the compact JSON element array.
pub fn to_compact_json(unit: &SourceUnit) -> Value {
    let mut b = Builder {
        dialect: unit.dialect,
        ..Default::default()
    };
    b.build(unit);
    b.finish(0)
}

/// Compute the `elementId → qualified-name segments` table for a model's
/// library units (normative KerML 9.1 IDs). Feed this to
/// [`crate::lift::from_compact_json_with_names`] to convert library-resolved
/// JSON back to textual notation.
pub fn library_name_map(model: &crate::model::Model) -> HashMap<String, Vec<String>> {
    let mut b = Builder::default();
    b.build_model(model);
    b.lib_qnames
        .iter()
        .chain(b.lib_mem_qnames.iter())
        .map(|(id, segments)| (id.to_string(), segments.clone()))
        .collect()
}

/// Canonical library names and the referenced identities whose canonical name
/// cannot be used from an external source. The full name table retains its
/// identity-derivation contract; remove the second set only from the table fed
/// to the textual lifter, so those references use its existing UUID fallback.
/// No alternate name is invented and source-language visibility is unchanged.
pub fn library_reference_names(
    model: &crate::model::Model,
    referenced: &HashSet<Uuid>,
) -> (HashMap<String, Vec<String>>, HashSet<String>) {
    let mut b = Builder::default();
    b.build_model(model);
    let names: HashMap<_, _> = b
        .lib_qnames
        .iter()
        .chain(b.lib_mem_qnames.iter())
        .map(|(id, segments)| (id.to_string(), segments.clone()))
        .collect();
    let mut fallback = HashSet::new();
    for id in referenced {
        let text = id.to_string();
        let Some(segments) = names.get(&text) else {
            continue;
        };
        let qn = QualifiedName {
            is_global: true,
            segments: segments
                .iter()
                .map(|value| Name {
                    value: value.clone(),
                    span: Span::default(),
                })
                .collect(),
            span: Span::default(),
        };
        // Membership imports serialize the selected alias/owning Membership,
        // while ordinary reference expressions serialize the selected member.
        let usable = match b.resolve_result(0, &qn, 0, false) {
            LookupResult::Found(element, _, membership) => {
                b.elem_id(element) == *id
                    || membership
                        .or(b.elements[element].owning_relationship)
                        .is_some_and(|m| b.elem_id(m) == *id)
            }
            LookupResult::Missing | LookupResult::Ambiguous => false,
        };
        if !usable {
            fallback.insert(text);
        }
    }
    (names, fallback)
}

/// [`library_name_map`] restricted to library *elements* (memberships and
/// aliases excluded) — the safe basis for name→id inversions, where a
/// membership entry would collide with its member's qualified name.
pub fn library_element_name_map(model: &crate::model::Model) -> HashMap<String, Vec<String>> {
    let mut b = Builder::default();
    b.build_model(model);
    b.lib_qnames
        .iter()
        .map(|(id, segments)| (id.to_string(), segments.clone()))
        .collect()
}

/// Serialize a multi-file [`Model`](crate::model::Model) to the compact JSON
/// element array.
///
/// All units share the global root namespace, so references across files —
/// including into library units — resolve to `{"@id": …}` references.
/// Library units contribute resolution targets and IDs only; the returned
/// array contains just the non-library units' elements.
pub fn model_to_compact_json(model: &crate::model::Model) -> Value {
    model_to_compact_json_with_units(model).0
}

/// [`model_to_compact_json`] plus the model's unit structure: for each
/// user unit, the element-array index of its root namespace paired
/// with the unit's name (its source path). Binary interchange uses
/// this to preserve the original file structure of the encoded model.
pub fn model_to_compact_json_with_units(
    model: &crate::model::Model,
) -> (Value, Vec<(usize, String)>) {
    let mut b = Builder::default();
    let boundary = b.build_model(model);
    // Each unit's first element is its root namespace; user units are
    // the ones at or past the library boundary.
    let units: Vec<(usize, String)> = b
        .unit_starts
        .iter()
        .filter(|&&(start, _)| start >= boundary)
        .map(|&(start, orig)| (start - boundary, model.unit_meta(orig).0.to_owned()))
        .collect();
    if model.graph_format() == crate::model::GraphFormat::CanonicalV3 {
        let mut resolved = ResolvedModel::from_builder(b, model);
        let compact = resolved.completed_compact_range(boundary, resolved.b.explicit_len());
        (compact, units)
    } else {
        (b.finish(boundary), units)
    }
}

/// The resolved standard library itself as a compact element array:
/// every element of the model's **library** units, each under its
/// normative KerML 9.1 id (name-derived; truly unnamed elements keep
/// this toolkit's deterministic path-based ids — the norm's positional
/// ids count an implementation's implied-relationship closure and are
/// not portable). The complement of [`model_to_compact_json`], which
/// emits just the user units: together they partition the built graph,
/// and a user payload's library references land exactly on this
/// array's `@id`s.
pub fn library_to_compact_json(model: &crate::model::Model) -> Value {
    library_to_compact_json_with_units(model).0
}

/// [`library_to_compact_json`] plus the library's unit structure: for
/// each library unit, the element-array index of its root namespace
/// paired with the unit's name (its source path).
pub fn library_to_compact_json_with_units(
    model: &crate::model::Model,
) -> (Value, Vec<(usize, String)>) {
    let mut b = Builder::default();
    let boundary = b.build_model(model);
    let units: Vec<(usize, String)> = b
        .unit_starts
        .iter()
        .filter(|&&(start, _)| start < boundary)
        .map(|&(start, orig)| (start, model.unit_meta(orig).0.to_owned()))
        .collect();
    if model.graph_format() == crate::model::GraphFormat::CanonicalV3 {
        let mut resolved = ResolvedModel::from_builder(b, model);
        (resolved.completed_compact_range(0, boundary), units)
    } else {
        (b.finish_range(0, boundary), units)
    }
}

/// The standard-library **resolver artifact**: everything a
/// payload consumer needs to resolve library references without a
/// loaded `Model` or any library-cache internals — `forward` maps
/// every name-resolvable library id (elements *and*
/// memberships/aliases) to its effective qualified-name segments,
/// `inverse` maps element qualified names back to ids (memberships
/// excluded — they would collide with their member's name), and
/// `collisions` lists element names excluded from the inverse because
/// two distinct elements claim them (explicit policy: a colliding
/// lookup fails loudly rather than resolving nondeterministically).
/// The caller supplies pinning metadata: the library compact export's
/// state digest plus the codec table/scheme versions it was built
/// under — consumers refuse artifacts whose pins do not match.
pub fn library_resolver_artifact(
    model: &crate::model::Model,
    library_state_digest: &str,
    tables_version: u16,
    scheme_version: u8,
    toolkit: &str,
) -> Value {
    let forward_map = library_name_map(model);
    let element_map = library_element_name_map(model);
    let mut inverse: std::collections::BTreeMap<String, String> = Default::default();
    let mut collisions: std::collections::BTreeSet<String> = Default::default();
    for (id, segments) in &element_map {
        let qname = segments.join("::");
        if collisions.contains(&qname) {
            continue;
        }
        if let Some(prev) = inverse.get(&qname) {
            if prev != id {
                inverse.remove(&qname);
                collisions.insert(qname);
            }
        } else {
            inverse.insert(qname, id.clone());
        }
    }
    let forward: std::collections::BTreeMap<String, Value> = forward_map
        .into_iter()
        .map(|(id, segments)| {
            (
                id,
                Value::Array(segments.into_iter().map(Value::from).collect()),
            )
        })
        .collect();
    let units = (0..model.unit_count())
        .filter(|&i| model.is_library_unit(i))
        .count();
    serde_json::json!({
        "format": "sysmlv2-stdlib-resolver",
        "formatVersion": 1,
        "toolkit": toolkit,
        "tablesVersion": tables_version,
        "schemeVersion": scheme_version,
        "libraryStateDigest": library_state_digest,
        "units": units,
        "forward": forward,
        "inverse": inverse,
        "collisions": collisions.into_iter().collect::<Vec<_>>(),
    })
}

/// Convenience: pretty-printed JSON text.
///
/// # Panics
///
/// Never in practice: the compact form is built from owned values that
/// always serialize.
pub fn to_compact_json_string(unit: &SourceUnit) -> String {
    serde_json::to_string_pretty(&to_compact_json(unit)).expect("JSON serialization cannot fail")
}

/// Referential findings from resolving a model, for `sysmlv2 check`-style
/// diagnostics. Each entry carries the index of the unit (into
/// [`crate::model::Model::units`]) the reference was written in, and the
/// name as written (with its source span).
pub struct ResolutionReport {
    /// References that did not resolve to any element.
    pub unresolved: Vec<(usize, QualifiedName)>,
    /// References for which name lookup found more than one distinct
    /// candidate at the same precedence. No declaration/import-order
    /// tiebreak is applied.
    pub ambiguous: Vec<(usize, QualifiedName)>,
    /// `alias … for X;` members whose target `X` does not resolve.
    pub unresolved_aliases: Vec<(usize, QualifiedName)>,
    /// Namespace imports whose target transitively imports the importing
    /// namespace back (including direct self-imports).
    pub import_cycles: Vec<(usize, QualifiedName)>,
    /// User root memberships whose name is also a standard-library root
    /// name — see [`RootShadowing`].
    pub shadowed_roots: Vec<RootShadowing>,
    /// Unresolved references whose name does exist in the searched scope
    /// under a visibility the reference cannot see — see
    /// [`BlockedReference`].
    pub blocked: Vec<BlockedReference>,
}

/// An unresolved reference that names a member the resolver found only
/// by ignoring visibility: widening that member's visibility would let
/// the reference resolve. Produced for chain steps (`c.maxTime` where
/// `maxTime` is a private member of `c`'s type), qualified names
/// (`T::m`) and redefinitions of inherited private members.
#[derive(Clone, Debug)]
pub struct BlockedReference {
    /// Index into [`crate::model::Model::units`] of the reference.
    pub unit: usize,
    /// The reference as written — for a chain step, the member segment
    /// only (its span is the diagnostic's).
    pub name: QualifiedName,
    /// The whole spelling as written, chain links included
    /// (`c.maxTime`), for messages.
    pub spelling: String,
    /// The member a wider visibility would expose.
    pub member: ElementRef,
    /// The member's declared visibility (`private` or `protected`).
    pub visibility: &'static str,
    /// Making the member `protected` would already let the reference
    /// resolve: it reaches the member through a specialization of the
    /// owning type. Always false for a `protected` member.
    pub protected_suffices: bool,
}

/// A root membership of a user unit whose name collides with a root
/// membership of a library unit (`package Requirements {}` next to the
/// standard `Requirements` library). Root lookups keep their existing
/// behavior — the library declaration wins (or, for same-kind
/// declarations, the name is ambiguous) — so every qualified reference
/// through the name silently bypasses the user declaration; this record
/// is the resolution-time evidence the referential check reports.
#[derive(Clone, Debug)]
pub struct RootShadowing {
    /// Index into [`crate::model::Model::units`] of the user declaration.
    pub unit: usize,
    /// Span of the user declaration's name (the member span when the
    /// declaration is unnamed on the colliding side).
    pub span: Span,
    /// The colliding name as it appears in the root namespace.
    pub name: String,
    /// Metaclass of the user declaration (`Package`, `PartDefinition`, …).
    pub metaclass: &'static str,
    /// Metaclass of the library declaration the name reaches at the root.
    pub library_metaclass: &'static str,
    /// `true` when a root lookup of the name lands on the library
    /// declaration; `false` when it is ambiguous between the two.
    pub resolves_to_library: bool,
}

/// Resolve a model and report referential findings instead of JSON.
/// True when any user unit declares a top-level name that also appears as
/// a top-level name of a library unit — the one situation where a library
/// reference's resolution could differ from the library-only world the
/// cache was recorded in. Conservative: any identification on a top-level
/// package, definition, usage, or alias counts.
fn top_level_shadowing(model: &crate::model::Model) -> bool {
    let user = top_level_names(model.user_units().map(|(_, u)| u));
    if let Some(library) = &model.prepared {
        !user.is_disjoint(&library.root_names)
    } else {
        !user.is_disjoint(&top_level_names(
            model.units().iter().filter(|u| u.is_library),
        ))
    }
}

/// The owning element of each relationship row of `b` (the rows' own
/// ownership; a materialized suffix's view is not read).
pub(crate) fn relationship_owners(b: &Builder) -> Vec<Option<usize>> {
    let mut owners = vec![None; b.elements.len()];
    for (i, element) in b.elements.iter().enumerate() {
        for &r in &element.owned_relationships {
            owners[r] = Some(i);
        }
    }
    owners
}

pub(crate) fn top_level_names<'a>(
    units: impl Iterator<Item = &'a crate::model::ModelUnit>,
) -> HashSet<String> {
    let mut names = HashSet::new();
    for mu in units {
        for m in &mu.unit.members {
            let id = match &m.kind {
                MemberKind::Package(p) => &p.id,
                MemberKind::Definition(d) => &d.id,
                MemberKind::Usage(u) => &u.declaration.id,
                MemberKind::Alias(a) => &a.id,
                _ => continue,
            };
            for n in [&id.name, &id.short_name].into_iter().flatten() {
                names.insert(n.value.clone());
            }
        }
    }
    names
}

pub fn model_resolution_report(model: &crate::model::Model) -> ResolutionReport {
    let mut b = Builder::default();
    b.build_model(model);
    resolution_report_from(&mut b)
}

/// [`model_resolution_report`] over an already-built graph (the
/// builder's lists stay in place).
pub(crate) fn resolution_report_from(b: &mut Builder) -> ResolutionReport {
    // Reported, not drained: `unresolved_references` and the lint rules
    // read the same lists after the report has been taken.
    let unresolved = b
        .unresolved
        .iter()
        .map(|(elem, qn)| (b.unit_of_elem(*elem), qn.clone()))
        .collect();
    let ambiguous = b
        .ambiguous
        .iter()
        .map(|(elem, qn)| (b.unit_of_elem(*elem), qn.clone()))
        .collect();
    let blocked = b
        .blocked
        .iter()
        .map(|site| BlockedReference {
            unit: b.unit_of_elem(site.owner),
            name: site.name.clone(),
            spelling: site.spelling.clone(),
            member: ElementRef(site.member),
            visibility: site.visibility,
            protected_suffices: site.protected_suffices,
        })
        .collect();
    ResolutionReport {
        unresolved,
        ambiguous,
        unresolved_aliases: b.check_aliases(),
        import_cycles: b.check_import_cycles(),
        shadowed_roots: b.check_root_shadowing(),
        blocked,
    }
}

/// Statements and control-flow edges require execution, even when their
/// enclosing calculation also has an ordinary return-value expression.
pub(crate) fn member_requires_execution(member: &Member) -> bool {
    member.leading_then
        || matches!(member.kind, MemberKind::InitialNode(_))
        || matches!(&member.kind, MemberKind::Usage(u) if matches!(u.kind,
            UsageKind::Action | UsageKind::Perform | UsageKind::Succession
            | UsageKind::SuccessionFlow | UsageKind::Accept | UsageKind::Send
            | UsageKind::Assign | UsageKind::Terminate | UsageKind::IfNode
            | UsageKind::WhileLoop | UsageKind::ForLoop | UsageKind::Merge
            | UsageKind::Decide | UsageKind::Join | UsageKind::Fork | UsageKind::Step))
}

/// Fixed UUIDv5 namespace for this library's deterministic element IDs.
/// Derived once: every created element and relationship hashes its path
/// against it, and the derivation is a SHA-1 in its own right.
static ID_NAMESPACE: std::sync::LazyLock<Uuid> = std::sync::LazyLock::new(|| {
    Uuid::new_v5(
        &Uuid::NAMESPACE_URL,
        b"https://crates.io/crates/sysmlv2-parser",
    )
});

#[cfg(test)]
mod id_namespace_test {
    /// Element identities are derived from this namespace, so it is part
    /// of the interchange contract and may not drift.
    #[test]
    fn the_identity_namespace_is_pinned() {
        assert_eq!(
            super::ID_NAMESPACE.to_string(),
            "6e8a6e90-78ac-5309-8f3b-3151fa7a09e1"
        );
    }
}

/// One import declared in a user unit: its relationship element, the
/// member's span (where a visibility keyword goes), the importing scope
/// and the visibility as written.
#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub(crate) struct UserImport {
    pub(crate) rel: usize,
    pub(crate) span: Span,
    pub(crate) scope: usize,
    pub(crate) visibility: Option<Visibility>,
}

/// The access a lookup walked an import under — what the resolver
/// checked against the import's visibility at that moment. Ordered from
/// most to least restrictive.
#[derive(
    Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, serde::Serialize, serde::Deserialize,
)]
pub enum AccessMode {
    /// Reached from outside the importing namespace: only a public
    /// import serves.
    Public,
    /// Reached through a specialization of the importing type: a
    /// protected import serves.
    Protected,
    /// Walked with full access — lexically from inside the importing
    /// namespace, through an `import all`, or as the last segment of an
    /// alias or import target: any visibility serves.
    Any,
}

/// The visibility an import's dependents require — see
/// [`ResolvedModel::import_visibility_advice`].
#[derive(Clone, Debug)]
pub struct ImportVisibilityAdvice {
    /// The import relationship.
    pub import: ElementRef,
    /// Unit and member span of the import declaration (a visibility
    /// keyword goes at the span's start).
    pub unit: usize,
    pub span: Span,
    /// The keyword as written, if any.
    pub declared: Option<&'static str>,
    /// `private`, `protected` or `public`.
    pub recommended: &'static str,
    /// Reference sites that walked the import under a restricted access
    /// (from outside the importing namespace, or through a
    /// specialization of it) — the ones a `private` keyword would break
    /// — as (unit, span).
    pub outside_sites: Vec<(usize, Span)>,
    /// Qualified name of the importing namespace, for messages.
    pub namespace: Option<String>,
}

/// Import relationships a resolution walked through, each with the
/// access the walk ran under.
pub(crate) type ImportWalks = Vec<(usize, LookupAccess)>;

/// A recorded visibility-blocked miss — see [`BlockedReference`].
#[derive(Clone, Debug)]
pub(crate) struct BlockedSite {
    pub(crate) owner: usize,
    pub(crate) name: QualifiedName,
    pub(crate) spelling: String,
    pub(crate) member: usize,
    pub(crate) visibility: &'static str,
    pub(crate) protected_suffices: bool,
}

/// One enumeration outcome ([`Builder::inherited_bindings`]): the
/// `(member element, contributing scope)` pairs, the inherited alias
/// Membership relationships, and whether a depth guard cut the walk short.
#[derive(Clone, Default)]
pub(crate) struct InheritedBindings {
    pub(crate) members: Vec<(usize, usize)>,
    pub(crate) alias_rels: Vec<usize>,
    /// Contributing Membership identities in normative per-base order.
    pub(crate) membership_order: Vec<usize>,
    /// A heritage or import chain reached [`MAX_RESOLUTION_DEPTH`], so
    /// members beyond it are missing from `members`.
    pub(crate) truncated: bool,
    /// Known cyclic or unsupported semantic dependency. This is distinct
    /// from an actual depth-budget cut and does not certify completeness.
    pub(crate) incomplete: bool,
    /// `(dropped, shadowing)` pairs removed by the SysML implicit
    /// same-name usage redefinition (condition (c) of the removal pass):
    /// `dropped` is the inherited member a same-named usage-family member
    /// `shadowing` (owned by the enumerated scope, or inherited from a
    /// nearer base) hides without a spelled `:>>`. Lookup treats the pair
    /// as a redefinition; the namespace-distinguishability check reads it
    /// as the collision the normative rule reports. A parameter of a
    /// behavior or step, a result or an end shadows nothing this way, in
    /// lookup or here: it redefines by position.
    pub(crate) implicit_redefinitions: Vec<(usize, usize)>,
}

/// Replace an id-spelled `@ref` placeholder atom (or any nested in an
/// array) with a reference to that id.
fn bind_atom(atom: &mut crate::properties::Atom, bound: &mut HashSet<Uuid>) {
    use crate::properties::Atom;
    match atom {
        Atom::Array(items) => items.iter_mut().for_each(|a| bind_atom(a, bound)),
        Atom::Object(_) => {
            let spelled = atom
                .get("@ref")
                .and_then(|v| v.as_str())
                .map(str::to_string);
            let Some(spelled) = spelled else {
                return;
            };
            // The lift quotes the id; the spelling may carry the quotes.
            let Ok(id) = Uuid::parse_str(spelled.trim_matches('\'')) else {
                return;
            };
            *atom = Atom::from_json(json!({ "@id": id.to_string() }));
            bound.insert(id);
        }
        _ => {}
    }
}

/// A visit of the import walk ([`Builder::collect_import_scope`]): the
/// scope, the access it was entered at, whether the visit descends
/// recursively (`::**`), and the filter chain that applied. Recursion is
/// part of the key because a plain `Q::*` visit must not stand in for a
/// later `::**` one that also descends into `Q`'s members.
type ImportVisit = (usize, u8, bool, Vec<(usize, usize)>);

/// Valued chain redefinitions by owning type: (redefining feature, resolved
/// chain links) — see [`Builder::chain_redefinitions`].
pub(crate) type ChainRedefinitions =
    Arc<crate::layered::LayeredMap<usize, Vec<(usize, Vec<usize>)>>>;

#[derive(Clone, Default, serde::Serialize, serde::Deserialize)]
pub(crate) struct Builder {
    pub(crate) graph_format: crate::model::GraphFormat,
    // Reconstructed from Model input metadata on every build; payload units
    // are user units and cannot be frozen into a prepared library prefix.
    #[serde(skip)]
    payload_source_units: HashSet<usize>,
    dialect: Dialect,
    pub(crate) semantic_memo: crate::semantic_memo::SemanticMemo,
    #[serde(skip)]
    pub(crate) semantic_ready: bool,
    /// Sole publication authority; skipped by prepared serialization.
    #[serde(skip)]
    implied: Option<implied::ImpliedTable>,
    #[serde(skip)]
    publication: publication::Control,
    #[serde(skip)]
    dynamic_graph: Option<Arc<dynamic_graph::Snapshot>>,
    #[serde(skip)]
    static_planning: bool,
    #[serde(skip)]
    recorded_lookup_ready: bool,
    #[serde(skip)]
    recorded_lookup_graph: Option<recorded_lookup::Graph>,
    #[serde(skip)]
    recorded_lookup_prefix: Option<Arc<recorded_lookup::Graph>>,
    /// Whether the structural shape can change under Membership selection.
    /// Persist this proof across prepared snapshots; user append recomputes it.
    recorded_lookup_candidate: bool,
    /// The outcomes this build starts from (see [`settled`]), taken by
    /// [`Self::resolve_pending`].
    #[serde(skip)]
    seed: Option<settled::Seed>,
    /// Whether this build keeps the outcomes it settles on.
    #[serde(skip)]
    keep_settled: bool,
    /// The outcomes this build settled on, when kept.
    #[serde(skip)]
    settled: Option<Arc<settled::SettledOutcomes>>,
    /// Selection did not stabilize within the pass budget. Restore contextual
    /// bootstrap outputs together and preserve qualification across snapshots.
    recorded_lookup_incomplete: bool,
    #[serde(skip)]
    redefinition_lookup_owner: Option<usize>,
    #[serde(skip)]
    redefinition_lookup_base: Option<usize>,
    #[serde(skip)]
    recorded_lookup_suppressed: bool,
    #[serde(skip)]
    library_refs_to_users: bool,
    /// Immutable library facts; never retain facts about user additions.
    #[serde(skip)]
    pub(crate) library_facts: Option<std::sync::Arc<crate::check::facts::Facts>>,
    /// Names that found no binding in the root scope while this library was
    /// prepared. Only these lookups can change when a model adds root
    /// declarations or root-level imports; root hits are owned members,
    /// which take precedence over anything a later import contributes.
    pub(crate) root_misses: HashSet<String>,
    /// Flat element list in ownership (depth-first) order.
    #[serde(with = "element_table")]
    pub(crate) elements: crate::layered::LayeredVec<Elem>,
    /// Ownership-path hash states, kept only while a build lowers.
    #[serde(skip)]
    path_hashes: Option<PathHashes>,
    #[serde(with = "scope_table")]
    scopes: crate::layered::LayeredVec<Scope>,
    /// Element index → its body scope (for namespace-owning elements).
    pub(crate) elem_scope: crate::layered::LayeredMap<usize, usize>,
    /// Per-scope cache of resolved namespace-import target scopes (with the
    /// recursive flag and the import's bracket-filter indices).
    #[serde(skip)]
    import_cache: crate::layered::ScopeTable<Option<Arc<Vec<ImportedScope>>>>,
    /// Per scope and access, the sub-scopes a recursive import walks: the
    /// scopes its admitted named members open, sorted. Lookups through a
    /// recursive import visit them for every name; the lists are the scope
    /// tables', fixed for a pass.
    #[serde(skip)]
    recursive_subs: crate::layered::IdMap<(usize, u8), Arc<[usize]>>,
    /// [`Self::chain_redefinitions`], with the element count it was built
    /// for.
    #[serde(skip)]
    chain_redefinitions: Option<(usize, ChainRedefinitions)>,
    /// Import relationships a lookup actually resolved a name through
    /// (admitted hits only) — the unused-import check's evidence.
    pub(crate) used_imports: crate::layered::IdSet<usize>,
    /// Import relationships the resolution in progress walked through,
    /// each with the access the walk ran under; cleared per user
    /// reference and recorded on its [`RefSite`].
    #[serde(skip)]
    pub(crate) query_imports: ImportWalks,
    /// Unresolved user references that name a member visible only
    /// under a wider visibility. Kept beside `unresolved`, which the
    /// report copies; this list is read by `blocked_references`.
    #[serde(skip)]
    pub(crate) blocked: Vec<BlockedSite>,
    /// A visibility-blind probe is running: every lookup admits every
    /// membership and no import use is recorded.
    #[serde(skip)]
    probing: bool,
    /// One member admitted as if it had the given visibility, for
    /// checking that widening it would let a reference resolve.
    #[serde(skip)]
    widen: Option<(usize, LookupAccess)>,
    /// Every textual `import` member lowered from a source unit:
    /// (relationship element, whole-member span, spelled `private`).
    pub(crate) user_imports: Vec<UserImport>,
    /// Per-scope cache of resolved specialization-base scopes.
    #[serde(skip)]
    base_cache: crate::layered::ScopeTable<Option<(Vec<usize>, usize)>>,
    /// Rule-required positional edges, keyed by stable element indices.
    #[serde(skip)]
    positional_redefinitions: Option<positional::PositionalRedefinitions>,
    /// Private recursion guard; never stands in for completed evidence.
    #[serde(skip)]
    positional_planning: bool,
    /// Whether [`Self::positional_redefinitions`] extends the prepared
    /// library's plan (see [`Self::plan_positional_on_library`]): the
    /// library's types then have the redefinitions the library gives them.
    #[serde(skip)]
    positional_from_library: bool,
    /// Library/variation requirements reused by positional planning and
    /// materialization. External name-table overrides bypass this cache.
    #[serde(skip)]
    supported_implied: Option<Arc<implied::SupportedImpliedSpecializations>>,
    /// The prepared library this build stands on: the planners extend its
    /// own rows' plans with this build's rows instead of planning every row
    /// (see [`library_plans`]). `None` for a library's own build and a
    /// joint one.
    #[serde(skip)]
    pub(crate) prepared_from: Option<Arc<crate::prepared::PreparedLibrary>>,
    /// Whether the planners extend [`Self::prepared_from`]'s plans, decided
    /// once per state of the rows (see [`Builder::library_plans`]).
    #[serde(skip)]
    library_plans_decided: Option<library_plans::LibraryPlansDecided>,
    /// Caller-supplied library-name overrides used by positional planning
    /// before the implied relationship view is materialized.
    #[serde(skip)]
    external_implied_names: HashMap<String, Uuid>,
    /// Per-(scope, include_implied) memo of the inherited-member
    /// enumeration ([`Self::inherited_bindings`]), cleared with the
    /// other lookup caches. Shared, so a hit costs a pointer copy.
    #[serde(skip)]
    inherited_cache: crate::layered::IdMap<(usize, bool), Arc<InheritedBindings>>,
    /// The same memo keyed by heritage for scopes that own nothing (a
    /// bodiless usage or definition): their enumeration is a function of
    /// their base scopes alone, and a large model has thousands of such
    /// scopes over a few hundred distinct heritages.
    #[serde(skip)]
    inherited_by_heritage: HashMap<(Vec<usize>, bool), Arc<InheritedBindings>>,
    /// Per-scope visit marks and outcomes for the current name query
    /// ([`Self::lookup`]). `None` under the active stamp means the scope is
    /// currently being evaluated (a cyclic re-entry is a miss); `Some`
    /// memoizes the completed result so multiple import paths can apply
    /// their own filters without re-walking the graph. The six slots separate
    /// three visibility levels for compatibility and semantic-name queries.
    #[serde(skip)]
    visit_stamp: crate::layered::ScopeTable<[u64; 6]>,
    #[serde(skip)]
    visit_result: crate::layered::ScopeTable<[Option<LookupResult>; 6]>,
    /// The active lookup query number (one per (start scope, name) chase).
    #[serde(skip)]
    query_stamp: u64,
    /// Per-import-entry resolution outcomes, keyed by (importing scope,
    /// target spelling): the element each namespace-import entry resolved
    /// to during [`Self::import_scopes`], consumed when the entry's own
    /// `importedNamespace` pending serializes so the reference and the
    /// resolution machinery can never disagree.
    #[serde(skip)]
    /// Resolved target of each namespace import per scope, with the
    /// import walks its own resolution took (attributed to the import's
    /// reference site, not to whichever lookup first filled the cache).
    import_targets: crate::layered::IdMap<(usize, String), (Option<usize>, ImportWalks)>,
    /// Library element IDs → qualified-name segments (collected while
    /// assigning normative IDs).
    lib_qnames: crate::layered::LayeredVec<(Uuid, Vec<String>)>,
    /// Library *membership* IDs (`…/owningMembership`, alias Memberships) →
    /// the member's qualified-name segments. Kept separate from
    /// [`Self::lib_qnames`] so name→id inversions (full-form implied
    /// relationships) never collide with the member element; merged into
    /// [`library_name_map`] for lift, which names import targets by id.
    lib_mem_qnames: crate::layered::LayeredVec<(Uuid, Vec<String>)>,
    /// Syntactic effective names of unnamed features (KerML 8.2.3.5 — the
    /// last segment of the first redefined/referenced feature's spelling),
    /// recorded at lowering time so `assign_library_ids` can give
    /// effective-named library members their normative qualified-name IDs
    /// (`ShapeItems::PlanarSurface::shape`) before resolution runs.
    effective_hint: crate::layered::LayeredMap<usize, String>,
    /// Unresolved references to patch after all scopes exist. A property key
    /// of the form `base#n` appends to the array property `base`.
    pending: Vec<PendingRef>,
    /// User references retained only for models containing UUID spellings.
    /// Interchange loading replays them after restoring explicit identities.
    #[serde(skip)]
    id_binding_pending: Vec<PendingRef>,
    /// Identity spellings, keyed by source unit and first-segment span.
    /// Distinct lexical names that happen to spell the same UUID retain
    /// their normal meaning, even in the same interchange document.
    #[serde(skip)]
    id_spelled_targets: HashMap<(usize, u32, u32), (Uuid, Uuid)>,
    /// Source provenance of a lifted expression/name while its resolution
    /// context may belong to another unit (inherited defaults, imports).
    #[serde(skip)]
    pub(crate) identity_origin_unit: Option<usize>,
    /// Source units for aliases; the global scope may contain aliases
    /// declared in several source units with identical target spans.
    #[serde(skip)]
    alias_origins: crate::layered::IdMap<(usize, usize), usize>,
    /// Library-cache replay: recorded outcomes for library-origin pending
    /// refs, consumed positionally by `resolve_pending` (see
    /// [`crate::libcache`]).
    #[serde(skip)]
    lib_hints: Option<std::vec::IntoIter<(Option<Uuid>, Vec<String>)>>,
    /// Whether `lib_hints` hold the library's own fixed point (see
    /// [`crate::libcache::LibraryCache`]) rather than a first pass's outcomes.
    #[serde(skip)]
    lib_hints_fixed_point: bool,
    /// Whether the last resolution pass took every library-origin pending
    /// ref from `lib_hints`, none resolved afresh.
    #[serde(skip)]
    lib_replayed_all: bool,
    /// Replay only the recorded targets from `lib_hints` in the next pass:
    /// a recorded miss is resolved afresh, which alone tells an ambiguous
    /// name from a missing one.
    #[serde(skip)]
    lib_replay_targets_only: bool,
    /// Root names the user units of the model being built introduce, from
    /// declarations, inferred names and root imports; `None` when a root
    /// construct's contribution needs the resolver. Replay skips every
    /// recorded outcome whose root misses intersect this set.
    #[serde(skip)]
    replay_completions: Option<HashSet<String>>,
    /// Root misses seen while resolving the current pending reference, or
    /// while computing the innermost lookup-cache entry in progress.
    #[serde(skip)]
    current_misses: Vec<String>,
    /// The misses of every resolution a lookup-cache fill in progress
    /// interrupted, outermost first: each fill notes its own misses in
    /// `current_misses` (see [`Self::begin_fill`]).
    #[serde(skip)]
    fill_frames: Vec<Vec<String>>,
    /// Root misses behind each scope's `base_cache` entry.
    #[serde(skip)]
    base_misses: crate::layered::ScopeTable<FillMisses>,
    /// Root misses behind each scope's `import_cache` entry — the
    /// resolution of every namespace import target of the scope, which
    /// also yields its `import_targets` entries.
    #[serde(skip)]
    import_misses: crate::layered::ScopeTable<FillMisses>,
    /// The scopes of the prepared library the build stands on: the
    /// per-scope lookup caches keep their rows sparse (see
    /// [`crate::layered::ScopeTable`]).
    #[serde(skip)]
    scope_floor: usize,
    /// Root misses behind the `semantic_metadata` memo.
    #[serde(skip)]
    semantic_metadata_misses: FillMisses,
    /// Sealed-snapshot replay: the cache whose final library element ids
    /// are consumed positionally at element creation — skipping
    /// ownership-path construction and UUIDv5 hashing for the whole
    /// library prefix — with the count already taken. The ids are read
    /// where they lie rather than copied out of the cache.
    #[serde(skip)]
    lib_ids_in: Option<(Arc<crate::libcache::LibraryCache>, usize)>,
    /// Library-cache recording: outcomes of library-origin pending refs,
    /// collected during `resolve_pending`.
    #[serde(skip)]
    lib_record: Option<Vec<(Option<Uuid>, Vec<String>)>>,
    /// Element that must not be a resolution result right now: while a
    /// scope's specialization-base names resolve, its own element is
    /// excluded so an unnamed feature's effective name (taken from its
    /// referenced/redefined feature) cannot shadow that very target.
    exclude: Option<usize>,
    /// Default exclusion recorded on pending refs currently being created
    /// (set while a feature's value expression builds).
    pending_exclude: Option<usize>,
    /// When set, lookups skip effective names — feature-chain steps resolve
    /// members of their target, not the lexical scope, so an unnamed
    /// sibling's effective name must not capture them.
    declared_only: bool,
    /// Default `declared_only` recorded on pending refs currently being
    /// created (set while a feature-chain step builds).
    pending_declared_only: bool,
    /// Feature-value expressions for the evaluator: element → (scope the
    /// expression resolves from, the syntax expression).
    pub(crate) values: crate::layered::LayeredMap<usize, (usize, Expr)>,
    /// Elements whose feature value is a `default` (KerML FeatureValue
    /// isDefault): a redefining feature with no value of its own inherits
    /// such an expression, re-evaluated in the redefining context.
    pub(crate) default_values: HashSet<usize>,
    /// Static contracts for synthesized action parameters and trigger arguments.
    /// Separate from feature values: these do not provide runtime bindings.
    pub(crate) owned_cross_features: crate::layered::LayeredMap<usize, usize>,
    pub(crate) payload_flows: HashSet<usize>,
    pub(crate) contract_exprs: crate::layered::LayeredMap<usize, (usize, Expr)>,
    /// Authored ranges for semantic checks: (source element, lexical scope,
    /// clause). Header rows name the constrained element; body/named domain
    /// rows name the MultiplicityRange itself and do not specify its cardinality.
    pub(crate) multiplicities: crate::layered::LayeredVec<(usize, usize, Multiplicity)>,
    /// Connector-family end features with reference targets, for the
    /// featuring-accessibility check: (connector, end feature, target span).
    pub(crate) connector_ends: crate::layered::LayeredVec<(usize, usize, Span)>,
    /// Chain-written subsetting targets (`part m :> a.b;`): (subsetting
    /// feature, scope the chain resolves from, chain links, span) — for
    /// the featuring-accessibility semantic check.
    pub(crate) chain_subsettings:
        crate::layered::LayeredVec<(usize, usize, Vec<QualifiedName>, Span)>,
    /// Satisfaction claims (`satisfy R by x;`): the SatisfyRequirementUsage
    /// element, the scope it was written in, and the `by` target — the
    /// satisfied requirement itself rides the element's
    /// ReferenceSubsetting. Consumed by [`ResolvedModel::satisfactions`].
    pub(crate) satisfy_by: crate::layered::LayeredVec<(usize, usize, TargetRef)>,
    /// Transition guard expressions, kept as syntax for diagram labels
    /// (the built element tree has no source text): transition element →
    /// (scope, expression).
    pub(crate) transition_guards: crate::layered::LayeredMap<usize, (usize, Expr)>,
    /// Resolved reference sites: every qualified name written in a
    /// *user* unit that resolved to an element, recorded as the pendings
    /// resolve. Library-internal sites are not recorded — the sealed
    /// snapshot replays those without resolving, so recording them would
    /// make cold and warm builds disagree. The target is the element the
    /// *name denotes* (before the importedMembership / `~P` conjugation
    /// serialization substitutions).
    pub(crate) ref_sites: Vec<RefSite>,
    /// Declared-name span per element (the primary name; the short name
    /// only when it is the sole identifier) — declaration sites for
    /// find-usages/rename.
    pub(crate) decl_spans: crate::layered::LayeredMap<usize, Span>,
    /// Full member source extent (keyword through body or terminator) per
    /// member element — the transformation SDK's remove/insert anchor.
    pub(crate) member_spans: crate::layered::LayeredMap<usize, Span>,
    /// Explicit specialization targets for semantic checks:
    /// (owning element, relationship metaclass, scope, target as written).
    #[serde(deserialize_with = "crate::prepared::specializations")]
    pub(crate) spec_targets:
        crate::layered::LayeredVec<(usize, &'static str, usize, QualifiedName)>,
    /// Resolution outcome per `spec_targets` index, recorded as the pending
    /// refs resolve — consumers (redefinition conformance) read the target
    /// here instead of re-resolving (`:>>` names self-hit and fall through
    /// to full import scans, ~0.2 ms each on import-heavy scopes).
    pub(crate) spec_resolved: crate::layered::LayeredVec<Option<usize>>,
    /// Root misses behind each `spec_resolved` outcome, by the same index:
    /// a resolution that reads another reference's recorded outcome
    /// depends on the root names that reference missed.
    #[serde(skip)]
    spec_misses: MissTable,
    /// Root misses behind the recorded single-valued outcome of each
    /// relationship, by the relationship element — what the recorded
    /// lookup graph built from those outcomes depends on.
    #[serde(skip)]
    ref_misses: MissTable,
    /// `spec_targets` index the next created pending ref reports into.
    pending_spec_idx: Option<usize>,
    /// Trailing result expressions for constraint verdicts and calculation
    /// invocation: (owning element, scope the expression resolves from,
    /// expression).
    pub(crate) result_exprs: crate::layered::LayeredVec<(usize, usize, Expr)>,
    /// Calculation/function bodies containing executable statements. The
    /// expression evaluator must not mistake their return expressions for
    /// the result of executing the body. This is derived from source on
    /// every build, including builds that replay a library cache.
    pub(crate) executable_calculations: HashSet<usize>,
    /// Derived source-site parameter identities, rebuilt when elements are appended.
    #[serde(skip)]
    parameter_sites: Option<parameters::ParameterSites>,
    #[serde(skip)]
    parameter_signatures: Option<parameters::ParameterSignatures>,
    /// Every named usage member per owning element, in declaration order
    /// with its element index — the binding targets for `new T(…)`
    /// constructor evaluation (filtered to data usages at use).
    pub(crate) ctor_fields: crate::layered::LayeredMap<usize, Vec<(String, usize)>>,
    /// Return-parameter element per owning element — a calculation written
    /// `return x = expr;` yields its return parameter's bound value (the
    /// evaluator's fallback when there is no trailing result expression).
    pub(crate) return_params: crate::layered::LayeredMap<usize, usize>,
    /// Direct usage members of enum-definition bodies (enum literals) —
    /// identity-comparable values for the evaluator. (Fidelity gap: these
    /// still lower as ReferenceUsage/FeatureMembership instead of
    /// EnumerationUsage/VariantMembership; tracked in the plan.)
    /// Lazily built element → `spec_targets` indices map (explicit
    /// typing/specialization edges, shared by [`ResolvedModel::
    /// explicit_supertypes`] and the evaluator's classification
    /// operators).
    #[serde(skip)]
    pub(crate) spec_index: Option<crate::layered::LayeredMap<usize, Vec<usize>>>,
    /// Lazily built interchange-id → element index map (the inverse of
    /// id assignment) — resolves id-valued relationship properties like
    /// `referencedFeature` without a [`ResolvedModel`] at hand. Rebuilt
    /// when the element count moves (edit sessions append).
    #[serde(skip)]
    id_index: Option<Arc<crate::layered::IdMap<Uuid, usize>>>,
    /// Element count `id_index` was built for (the map itself is shorter
    /// than the element list when ids collide, which must not force a
    /// rebuild per lookup).
    #[serde(skip)]
    id_index_built_for: usize,
    /// Immutable stored topology only; semantic proof facts stay query-local.
    #[serde(skip)]
    stored_structure: Option<Arc<structural_index::StoredStructure>>,
    /// The structural scan of the frozen library rows, made when the
    /// library is frozen and shared by every build on it: a build scans only
    /// its own rows again. Not serialized: a decoded library's freeze makes
    /// its own.
    #[serde(skip)]
    pub(crate) prefix_structure: Option<Arc<structural_index::PrefixStructure>>,
    /// The frozen rows by id, kept by the freeze for the identity
    /// assignment of every build on them (see [`Self::assign_user_ids`]):
    /// the kept lookup graph's own table where there is one, else made at
    /// the freeze. Not serialized: a decoded library's freeze makes its own.
    #[serde(skip)]
    pub(crate) prefix_ids: Option<Arc<crate::layered::IdMap<Uuid, usize>>>,
    /// The library name tables by id, the first entry of an id winning,
    /// made by the first build on the frozen rows whose identity
    /// assignment reads a library row's name from them, and shared by
    /// every build on them (see [`IdentityTables::table_name`]). Not
    /// serialized: a decoded library's freeze makes its own cell.
    #[serde(skip)]
    pub(crate) prefix_table_names: Arc<std::sync::OnceLock<Arc<HashMap<Uuid, String>>>>,
    /// Lazily built constrained element → first header [`Self::multiplicities`]
    /// row, excluding body/named domain rows,
    /// with the row count it was built from. The table is
    /// library-inclusive, so the scan it replaces was proportional to
    /// the library on every lookup.
    #[serde(skip)]
    mult_index: Option<(usize, crate::layered::LayeredMap<usize, usize>)>,
    /// First non-library element index (libraries build first) — the
    /// `boundary` of [`Self::build_model`], kept for library-ownership
    /// tests.
    pub(crate) lib_boundary: usize,
    /// Index of the first *implied* relationship the derivation layer
    /// materialized past the explicit elements (`json/implied.rs`);
    /// `None` until it did. Everything that iterates the element list as
    /// the model's content stops at [`Self::explicit_len`].
    #[serde(skip)]
    pub(crate) implied_from: Option<usize>,
    /// Immutable ownership/source projection for materialized semantic nodes.
    /// Source storage and prepared snapshots never serialize this view.
    #[serde(skip)]
    semantic_ownership: Option<Arc<semantic_ownership::SemanticOwnership>>,
    /// Set while building an enum definition's direct body members.
    in_enum_body: bool,
    /// Usage elements with an expected featuring type (owned by a Type via
    /// a FeatureMembership, or a variant of such a variation usage) — the
    /// pilot's `UsageUtil.hasFeaturingType`, which drives `isComposite`
    /// for SysML usages.
    usage_featuring: crate::layered::LayeredMap<usize, bool>,
    /// Featuring flag for the usage element about to be created (set by
    /// `build_usage_with`/`build_usage_element_scoped`, read by
    /// `build_usage_element` immediately after — never across recursion).
    pending_featuring: bool,
    /// Membership-implied parameter direction for the usage element about
    /// to be created (same lifetime discipline as `pending_featuring`).
    #[serde(skip)]
    pending_direction: Option<&'static str>,
    /// Metaclass of the owner of the usage element about to be created
    /// (same lifetime discipline) — drives the port-usage composite rule.
    #[serde(skip)]
    pending_owner_ty: Option<&'static str>,
    /// Per-owner count of `prefixmeta{n}` segments handed out — prefix
    /// metadata and canonicalized bare `@M;` members share one sequence.
    prefix_meta_next: crate::layered::LayeredMap<usize, usize>,
    /// (first element index, original unit index) per built unit, in build
    /// order — attributes elements back to their source unit.
    unit_starts: Vec<(usize, usize)>,
    /// (first scope index, original unit index) per built unit.
    scope_starts: Vec<(usize, usize)>,
    /// References that stayed unresolved: (element, name as written).
    pub(crate) unresolved: Vec<(usize, QualifiedName)>,
    /// References whose lookup found multiple same-precedence targets.
    ambiguous: Vec<(usize, QualifiedName)>,
    /// Import filter conditions — `filter expr;` members and bracketed
    /// `import P::*[expr]` filters: (source relationship, scope the expression's names resolve from, the syntax expression). Applied by [`Self::lookup`] to every
    /// hit that arrives through an import (see [`Self::filter_verdict`]).
    pub(crate) filter_exprs: crate::layered::LayeredVec<(usize, usize, Expr)>,
    /// Per-filter re-entrancy guard: resolving a filter's own metaclass
    /// names may walk back through the filtered import; a re-entered
    /// filter answers *undecided* (member stays visible).
    #[serde(skip)]
    filters_active: Vec<bool>,
    /// Direct metadata annotations per annotated element: `#M` prefix
    /// metadata, about-less body members and validated explicit Annotation
    /// targets. Explicit-about snapshots are refreshed between resolution passes.
    pub(crate) metadata_of: crate::layered::LayeredMap<usize, Vec<usize>>,
    /// Captured lazily only for models containing explicit metadata about sites.
    #[serde(default)]
    metadata_intrinsic: Option<crate::layered::LayeredMap<usize, Vec<usize>>>,
    /// Current explicit contributions; empty keys retain touched-target history
    /// so prepared library contexts can be refreshed after association removal.
    #[serde(default)]
    pub(crate) metadata_about: std::collections::BTreeMap<usize, Vec<usize>>,
    /// Semantic snapshot changes can invalidate query proofs without row edits.
    #[serde(skip)]
    metadata_association_generation: Option<std::sync::Arc<()>>,
    #[serde(default)]
    explicit_metadata_annotations: crate::layered::LayeredVec<usize>,
    #[serde(default)]
    pub(crate) metadata_associations_incomplete: bool,
    /// Port definition element → its implicit ConjugatedPortDefinition
    /// (`~P` typings resolve through the original and substitute this).
    conjugated_defs: crate::layered::LayeredMap<usize, usize>,
    /// Memoized `Metaobjects::SemanticMetadata` element (`Some(None)` =
    /// resolved once, library absent — semantic-metadata implied bases
    /// stay inert).
    #[serde(skip)]
    semantic_metadata: Option<Option<usize>>,
    /// Membership-import entries currently resolving their own target —
    /// `(scope, index into member_imports)`. A membership import must not
    /// resolve its target through itself (`import vehicle::**;` — the
    /// entry matches `vehicle` and would recurse to the depth guard,
    /// permanently caching an empty `import_scopes` for the scope on the
    /// way down).
    #[serde(skip)]
    member_import_active: crate::layered::IdSet<(usize, usize)>,
}

/// Three-valued verdict of a filter condition against one candidate
/// element. Undecided keeps the member visible (checker policy: hide only
/// what provably fails the filter).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum Tri {
    True,
    False,
    Unknown,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
struct Binding {
    elem: usize,
    sub_scope: Option<usize>,
    /// Visibility of the Membership that contributes this name. KerML's
    /// default membership visibility is public.
    visibility: LookupAccess,
}

/// Visibility admitted by a lookup. The ordering is intentional:
/// public-only < public-or-protected < all memberships.
#[derive(Clone, Copy, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub(crate) enum LookupAccess {
    Public = 0,
    Protected = 1,
    All = 2,
}

impl LookupAccess {
    fn admits(self, visibility: Self) -> bool {
        (self as usize) >= (visibility as usize)
    }

    fn inherited(self) -> Self {
        match self {
            Self::All => Self::Protected,
            other => other,
        }
    }
}

fn access_mode(access: LookupAccess) -> AccessMode {
    match access {
        LookupAccess::Public => AccessMode::Public,
        LookupAccess::Protected => AccessMode::Protected,
        LookupAccess::All => AccessMode::Any,
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
enum LookupResult {
    Missing,
    /// Element, member scope, and the named alias Membership (if any).
    /// Retaining the last component lets membership imports preserve identity
    /// while ordinary references continue to denote the member element.
    Found(usize, Option<usize>, Option<usize>),
    Ambiguous,
}

impl LookupResult {
    fn option(self) -> Option<(usize, Option<usize>)> {
        match self {
            Self::Found(elem, scope, _) => Some((elem, scope)),
            Self::Missing | Self::Ambiguous => None,
        }
    }
}

/// The root misses ([`Builder::note_root_miss`]) behind one entry of a
/// lookup cache. The caches outlive the reference whose resolution fills
/// them, so every read of an entry notes these names again: an outcome
/// read through a cache depends on each root name the cached computation
/// looked up and missed, whichever reference computed it.
#[derive(Clone, Default)]
enum FillMisses {
    /// Not computed yet, or computed without missing a root name.
    #[default]
    None,
    /// Being computed by the fill [`Builder::begin_fill`] numbered so. A
    /// read from inside it sees the partial entry, which depends on what
    /// the fill has missed so far.
    Filling(usize),
    /// Computed; its computation missed these root names.
    Missed(Arc<[String]>),
}

/// Root misses by a dense index (a scope, an element, a specialization
/// entry), grown on demand. Only builds that record library outcomes fill
/// one, and sparsely: an absent index costs a bounds check, not a hash.
#[derive(Clone, Default)]
struct MissTable(Vec<Option<Arc<[String]>>>);

impl MissTable {
    fn get(&self, index: usize) -> Option<&Arc<[String]>> {
        self.0.get(index)?.as_ref()
    }

    fn set(&mut self, index: usize, misses: &[String]) {
        if misses.is_empty() {
            if let Some(slot) = self.0.get_mut(index) {
                *slot = None;
            }
            return;
        }
        if self.0.len() <= index {
            self.0.resize(index + 1, None);
        }
        self.0[index] = Some(misses.into());
    }

    fn clear(&mut self) {
        self.0 = Vec::new();
    }
}

/// The lookup state one query sets for itself — see
/// [`Builder::enter_fill_mode`].
struct QueryMode {
    probing: bool,
    widen: Option<(usize, LookupAccess)>,
    exclude: Option<usize>,
    declared_only: bool,
    header_owner: Option<usize>,
    header_base: Option<usize>,
    member_imports: crate::layered::IdSet<(usize, usize)>,
    /// The filter flags, when some filter was being evaluated.
    filters: Option<Vec<bool>>,
    suppressed: bool,
}

/// The root miss that stands for the root namespace importing nothing.
/// The recorded lookup graph takes a scope's implied roots as absent only
/// while no root import could make them visible, so what it reads through
/// such a scope depends on this as on the roots themselves, and any root
/// import supplies it. A root member spelled this way through an
/// unrestricted name costs a needless re-resolution, never a wrong one.
pub(crate) const ROOT_IMPORTS: &str = "::*";

/// Note `names` among the misses of the resolution in progress, once each.
fn note_misses<'a>(noted: &mut Vec<String>, names: impl IntoIterator<Item = &'a String>) {
    for name in names {
        if !noted.contains(name) {
            noted.push(name.clone());
        }
    }
}

#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
struct NamespaceImport {
    target: QualifiedName,
    recursive: bool,
    is_import_all: bool,
    filters: Vec<usize>,
    relationship: usize,
    /// Effective visibility of the imported membership in this namespace.
    is_public: bool,
}

#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
struct MemberImport {
    target: QualifiedName,
    is_import_all: bool,
    filters: Vec<usize>,
    relationship: usize,
    is_public: bool,
}

/// A scope made visible by a namespace import. `is_import_all` controls
/// whether non-public memberships of the source namespace participate.
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
struct ImportedScope {
    scope: usize,
    recursive: bool,
    is_import_all: bool,
    filters: Vec<usize>,
    relationship: usize,
    is_public: bool,
}

/// A reference recorded for the post-pass, once all scopes exist.
#[derive(Clone, serde::Serialize, serde::Deserialize)]
struct PendingRef {
    /// Element the resolved value is set on.
    elem: usize,
    /// Property key (`base#n` appends to array property `base`).
    key: String,
    /// Scope to resolve from.
    scope: usize,
    qn: QualifiedName,
    /// Element that must not be the resolution result (a specialization's
    /// own feature) — see [`Builder::exclude`].
    exclude: Option<usize>,
    /// Resolve against declared names only — see [`Builder::declared_only`].
    declared_only: bool,
    /// For feature-chain steps whose left spine is statically a name chain
    /// (`pub.topic`, `subscribing.sub.topic`): the spine link names, in
    /// order. Resolution first resolves the spine, then looks `qn` up in
    /// the final link's scope (owned + inherited members). Falls back to
    /// lexical resolution when absent or when the spine does not resolve.
    chain: Option<Vec<QualifiedName>>,
    /// `spec_targets` index to report the resolution outcome into.
    spec_idx: Option<usize>,
}

/// The rows an identity assignment reads by id and by name (see
/// [`Builder::assign_user_ids`]): its own rows, from `start`, in tables of
/// its own; the frozen rows before them through the ids their freeze kept
/// and their names on demand.
struct IdentityTables {
    start: usize,
    /// Pre-reassignment id → index of the rows from `start`: the last row
    /// carrying an id.
    by_id: crate::layered::IdMap<Uuid, usize>,
    /// The identity names of the rows from `start`.
    names: Vec<Option<String>>,
    /// The frozen rows by id, when `start` is their end.
    frozen: Option<Arc<crate::layered::IdMap<Uuid, usize>>>,
    /// The library name tables by id, the first entry of an id winning,
    /// made when a row's identity name is first read from them: the cell
    /// every build on the frozen rows shares while the tables are the
    /// frozen rows' alone, else a table of this build's own.
    table_names: Option<Arc<HashMap<Uuid, String>>>,
}

impl IdentityTables {
    /// The row carrying `id`: the last of this build's rows to, else the
    /// frozen row.
    fn index_of(&self, id: &Uuid) -> Option<usize> {
        self.by_id
            .get(id)
            .or_else(|| self.frozen.as_ref()?.get(id))
            .copied()
    }

    /// Row `e`'s identity name: declared, else from the library name tables.
    fn name(&mut self, b: &Builder, e: usize) -> Option<String> {
        if e >= self.start {
            return self.names[e - self.start].clone();
        }
        b.effective_name(e)
            .or_else(|| self.table_name(b, b.elements[e].id))
    }

    fn table_name(&mut self, b: &Builder, id: Uuid) -> Option<String> {
        let tables = self.table_names.get_or_insert_with(|| {
            let frozen_only = self.frozen.is_some()
                && b.lib_qnames.len() == b.lib_qnames.base_len()
                && b.lib_qnames.base_untouched()
                && b.lib_mem_qnames.len() == b.lib_mem_qnames.base_len()
                && b.lib_mem_qnames.base_untouched();
            if frozen_only {
                let shared = &b.prefix_table_names;
                if shared.get().is_none() {
                    note_library_names_built();
                }
                Arc::clone(shared.get_or_init(|| Arc::new(b.library_table_names())))
            } else {
                note_library_names_built();
                Arc::new(b.library_table_names())
            }
        });
        tables.get(&id).cloned()
    }
}

#[cfg(test)]
thread_local! {
    static PREFIX_IDS_SERVED: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
    static ID_INDEX_TABLED: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
    static LIBRARY_NAMES_BUILT: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}
/// How many rows the id index tabled itself, over every build.
#[cfg(test)]
pub(crate) fn id_index_tabled() -> usize {
    ID_INDEX_TABLED.with(|c| c.get())
}
#[cfg(test)]
fn note_id_index_tabled(rows: usize) {
    ID_INDEX_TABLED.with(|c| c.set(c.get() + rows));
}
#[cfg(not(test))]
fn note_id_index_tabled(_rows: usize) {}
/// How many times the library name tables were made by id.
#[cfg(test)]
pub(crate) fn library_names_built() -> usize {
    LIBRARY_NAMES_BUILT.with(|c| c.get())
}
#[cfg(test)]
fn note_library_names_built() {
    LIBRARY_NAMES_BUILT.with(|c| c.set(c.get() + 1));
}
#[cfg(not(test))]
fn note_library_names_built() {}
/// How many identity assignments read the frozen rows through a kept table.
#[cfg(test)]
pub(crate) fn prefix_ids_served() -> usize {
    PREFIX_IDS_SERVED.with(|c| c.get())
}
#[cfg(test)]
fn note_prefix_ids_served() {
    PREFIX_IDS_SERVED.with(|c| c.set(c.get() + 1));
}
#[cfg(not(test))]
fn note_prefix_ids_served() {}

/// The passes the redo loop takes against the graph of the previous
/// pass's outcomes before concluding that they oscillate.
const REDO_PASSES: usize = 4;

/// What a pass records beside its outcomes, as lowering left it: restored
/// before every pass, so that each pass records its own.
struct SideState {
    unresolved: Vec<(usize, QualifiedName)>,
    ambiguous: Vec<(usize, QualifiedName)>,
    blocked: Vec<BlockedSite>,
    sites: Vec<RefSite>,
    used: crate::layered::IdSet<usize>,
}

impl SideState {
    fn capture(b: &Builder) -> Self {
        Self {
            unresolved: b.unresolved.clone(),
            ambiguous: b.ambiguous.clone(),
            blocked: b.blocked.clone(),
            sites: b.ref_sites.clone(),
            used: b.used_imports.clone(),
        }
    }

    fn restore(&self, b: &mut Builder) {
        b.unresolved = self.unresolved.clone();
        b.ambiguous = self.ambiguous.clone();
        b.blocked = self.blocked.clone();
        b.ref_sites = self.sites.clone();
        b.used_imports = self.used.clone();
    }
}

/// A pass's outcomes: the pending references' values and the
/// specialization outcomes.
type PassOutcomes = (Vec<Option<crate::properties::Atom>>, Vec<Option<usize>>);

/// A library's recorded fixed point, for a redo pass to replay again.
type LibraryReplay = (Vec<(Option<Uuid>, Vec<String>)>, HashSet<String>);

#[cfg(test)]
thread_local! {
    static PASSES: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}
/// How many resolution passes ran.
#[cfg(test)]
pub(crate) fn passes() -> usize {
    PASSES.with(|c| c.get())
}
#[cfg(test)]
fn note_pass() {
    PASSES.with(|c| c.set(c.get() + 1));
}
#[cfg(not(test))]
fn note_pass() {}

/// One pending reference paired with cache bookkeeping before resolution is
/// reordered to put specialization outcomes first.
struct PendingWork {
    source_order: usize,
    pending: PendingRef,
    /// A replayed outcome and the root misses recorded with it.
    lib_hint: Option<(Option<Uuid>, Vec<String>)>,
    record_pos: Option<usize>,
}

#[derive(Clone)]
pub(crate) struct Elem {
    pub(crate) ty: &'static str,
    id: Uuid,
    /// Ownership path used to derive `id` and children's ids: the whole
    /// path, or under a `path_parent` only the segment this element adds
    /// to that element's path (see [`whole_path`]).
    path: String,
    /// The element whose ownership path this one's extends. Holding the
    /// segment alone keeps a path's cost its own length rather than its
    /// depth, which grows by one segment per ownership level.
    path_parent: Option<usize>,
    pub(crate) props: crate::properties::Properties,
    pub(crate) owned_relationships: crate::flat::Row<usize>,
    pub(crate) children: crate::flat::Row<usize>,
    pub(crate) owning_relationship: Option<usize>,
}

impl<'de> serde::Deserialize<'de> for Elem {
    fn deserialize<D: serde::Deserializer<'de>>(d: D) -> Result<Self, D::Error> {
        #[derive(serde::Deserialize)]
        struct Wire {
            ty: String,
            id: Uuid,
            path: String,
            props: crate::properties::Properties,
            owned_relationships: crate::flat::Row<usize>,
            children: crate::flat::Row<usize>,
            owning_relationship: Option<usize>,
        }
        let w = Wire::deserialize(d)?;
        Ok(Self {
            ty: crate::metaclass::canonical_name(&w.ty)
                .ok_or_else(|| serde::de::Error::custom("unknown metaclass"))?,
            id: w.id,
            path: w.path,
            path_parent: None,
            props: w.props,
            owned_relationships: w.owned_relationships,
            children: w.children,
            owning_relationship: w.owning_relationship,
        })
    }
}

/// The whole ownership path of element `i`: the segments of its path
/// parents and its own, joined by `/`. Each parent precedes its children
/// in the table, so the walk ends.
fn whole_path(elements: &crate::layered::LayeredVec<Elem>, i: usize) -> String {
    let mut segments = vec![elements[i].path.as_str()];
    let mut at = i;
    while let Some(parent) = elements[at].path_parent {
        segments.push(elements[parent].path.as_str());
        at = parent;
    }
    segments.reverse();
    segments.join("/")
}

/// The version-5 identity of the name `hash` has read after the identity
/// namespace — what [`Uuid::new_v5`] computes in one pass.
fn path_id(hash: &sha1_smol::Sha1) -> Uuid {
    let mut bytes = [0; 16];
    bytes.copy_from_slice(&hash.digest().bytes()[..16]);
    uuid::Builder::from_sha1_bytes(bytes).into_uuid()
}

#[cfg(test)]
thread_local! {
    static PATH_BYTES_HASHED: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

/// Bytes the current thread has hashed deriving element identities from
/// ownership paths.
#[cfg(test)]
pub(crate) fn path_bytes_hashed() -> usize {
    PATH_BYTES_HASHED.with(|c| c.get())
}

/// Hash `bytes` into an identity's path state.
fn hash_path(hash: &mut sha1_smol::Sha1, bytes: &[u8]) {
    #[cfg(test)]
    PATH_BYTES_HASHED.with(|c| c.set(c.get() + bytes.len()));
    hash.update(bytes);
}

/// The hash states that ownership paths leave, kept while a build lowers
/// sources: a child's identity then hashes its own segment onto its
/// parent's state instead of its whole path again.
#[derive(Clone, Default)]
struct PathHashes {
    /// The first element with a slot.
    base: usize,
    /// The state after the identity namespace and the element's whole
    /// path, by element index from `base`.
    states: Vec<Option<sha1_smol::Sha1>>,
}

#[derive(Clone, Default, serde::Serialize, serde::Deserialize)]
struct Scope {
    parent: Option<usize>,
    /// The element whose body this scope is (for base-resolution
    /// self-exclusion).
    owner: Option<usize>,
    /// name → all memberships contributing that name. Keeping every
    /// candidate is required both for ambiguity detection and KerML
    /// namespace distinguishability; insertion order must never choose a
    /// semantic target.
    #[serde(skip)]
    names: scope_table::Names,
    /// Effective names of unnamed features (from their first referenced or
    /// redefined feature). Consulted after `names`, and skipped entirely for
    /// feature-chain steps (which do not resolve lexically).
    #[serde(skip)]
    effective_names: scope_table::Names,
    /// Simple redefinition targets of this scope's owner. When resolving
    /// one with that owner excluded, sibling inferred names in its parent
    /// cannot establish the target they themselves are derived from.
    redefinition_names: HashSet<String>,
    /// Every name-spelled redefinition target of this scope's owner. Keep
    /// qualification so positional slot reduction can distinguish same-named
    /// inherited features without consulting a partially built target index.
    redefinition_spellings: Vec<QualifiedName>,
    /// Namespace imports (`P::*` / `P::*::**`) visible in this scope, with
    /// the recursive flag and the indices (into [`Builder::filter_exprs`])
    /// of the import's own bracket filters (`import P::*[@Safety]`).
    imports: Vec<NamespaceImport>,
    /// Membership imports (`import P::name`), with bracket-filter indices.
    member_imports: Vec<MemberImport>,
    /// Filter conditions declared as `filter expr;` members of this
    /// namespace (indices into [`Builder::filter_exprs`]) — they apply to
    /// every membership imported into this scope (SysML 7.2.5:
    /// ElementFilterMembership).
    filters: Vec<usize>,
    /// `alias a for X` members.
    aliases: Vec<(String, QualifiedName, usize)>,
    /// Implied end-feature names of a binary connector-family usage: its two
    /// ends implicitly redefine `source`/`target` (SysML 8.4.2, the ends of
    /// `Connections::BinaryConnection`), so those names resolve — in the
    /// usage's body — to the usage's own end features. Each entry is
    /// (name, end element, end scope); the end scope bases on the end's
    /// connected feature, so chain members (`source.x`) resolve through it.
    /// Lift names these ends positionally (`implied_end_name`) — the two
    /// must stay in sync or the round-trip gate trips.
    #[serde(deserialize_with = "crate::prepared::implied_ends")]
    implied_ends: Vec<(&'static str, usize, usize)>,
    /// Specialization/typing targets of the element owning this scope —
    /// members of these resolve as inherited members.
    bases: Vec<QualifiedName>,
    /// *Implied* heritage (resolution only, never emitted to JSON): the SysML
    /// Tables 31/32 library bases of the owner's kind and the binary
    /// connector/interface library base (the scopes of what a parameter,
    /// end or result redefines by position join them when the bases are
    /// read, [`Builder::base_scopes_split`]). Split from [`Self::bases`] so
    /// inherited-member enumeration can distinguish explicit heritage
    /// from implied; lookup treats both alike.
    implied_bases: Vec<QualifiedName>,
    /// Specialization/typing targets written as feature chains — the
    /// chain's last link contributes inherited members exactly like a
    /// plain-name base (`part m :> a.b { attribute :>> x; }` finds `x`
    /// among `b`'s members).
    chain_bases: Vec<Vec<QualifiedName>>,
}

impl Builder {
    fn build(&mut self, unit: &SourceUnit) {
        self.keep_path_hashes();
        let root_scope = self.push_scope(None);
        let root = self.new_element("Namespace", None, "$root".to_string());
        for (i, member) in unit.members.iter().enumerate() {
            self.build_member(member, root, root_scope, i);
        }
        self.resolve_pending();
        self.assign_user_ids(0, &[root]);
        self.path_hashes = None;
    }

    /// Build all units of a model into one graph (library units first) and
    /// return the element index where non-library output starts.
    pub(crate) fn build_model(&mut self, model: &crate::model::Model) -> usize {
        self.graph_format = model.graph_format();
        if let Some(library) = &model.prepared {
            if library.graph_format() == self.graph_format
                && !top_level_shadowing(model)
                && !library.builder.user_completes_library(model)
            {
                let boundary = self.build_on_library(model, &library.builder);
                self.prepared_from = Some(Arc::clone(library));
                return boundary;
            }
            // A prepared library's own recording stands in for the prepared
            // graph this build cannot reuse.
            model.arm_prepared_recording();
        }
        match self.build_model_inner(model, false) {
            Ok(boundary) => boundary,
            // Sealed-snapshot validation failed (a lowering change at the
            // same crate version — possible during development). Rebuild
            // cold, recording: the model's slot flips to Record, so the
            // rebuild makes the cache the next save overwrites the stale
            // file with, and a library prepared from this model keeps it.
            Err(()) => {
                *self = Builder::default();
                self.graph_format = model.graph_format();
                model.rerecord_library_cache();
                self.build_model_inner(model, false)
                    .expect("a build without a snapshot cannot fail snapshot validation")
            }
        }
    }

    fn user_completes_library(&self, model: &crate::model::Model) -> bool {
        // An unresolved library reference may become resolvable when a model
        // introduces its root name. In that case resolve everything together.
        // Owned root members shadow imported ones, so a root import or an
        // inferred root name matters only through recorded root misses.
        self.root_completions(model)
            .is_none_or(|names| names.iter().any(|n| self.completes_root_name(n)))
    }

    /// The names a model's user units make visible in the root namespace.
    /// `None` when a root construct's contribution needs the resolver, so
    /// callers must assume any recorded outcome could change.
    fn root_completions(&self, model: &crate::model::Model) -> Option<HashSet<String>> {
        let mut names = HashSet::new();
        for (_, unit) in model.user_units() {
            for member in &unit.unit.members {
                // Only root identifications matter. Avoid lowering user bodies.
                let id = match &member.kind {
                    MemberKind::Import(import) | MemberKind::Expose(import) => {
                        names.extend(self.imported_root_names(model, import)?);
                        names.insert(ROOT_IMPORTS.to_owned());
                        None
                    }
                    // A root filter also constrains the library's own root
                    // imports, so it always requires joint resolution.
                    MemberKind::Filter(_) => return None,
                    MemberKind::Package(p) => Some(&p.id),
                    MemberKind::Definition(d) => Some(&d.id),
                    // An anonymous root feature can introduce an inferred
                    // binding from its redefinition/reference target.
                    MemberKind::Usage(u) => {
                        if u.declaration.id.name.is_none() {
                            names.extend(effective_ref_name(
                                &u.declaration,
                                matches!(
                                    u.kind,
                                    UsageKind::Perform | UsageKind::Exhibit | UsageKind::Include
                                ),
                                u.prefix.is_variant,
                            ));
                        }
                        Some(&u.declaration.id)
                    }
                    MemberKind::Alias(a) => Some(&a.id),
                    MemberKind::Dependency(d) => Some(&d.id),
                    MemberKind::Relationship(r) => Some(&r.id),
                    MemberKind::MultiplicityDecl(m) => Some(&m.id),
                    MemberKind::Comment(c) => Some(&c.id),
                    MemberKind::Doc(d) => Some(&d.id),
                    MemberKind::TextualRep(r) => Some(&r.id),
                    // Other root constructs may also add named memberships;
                    // use joint resolution instead of guessing their effects.
                    _ => return None,
                };
                if let Some(id) = id {
                    names.extend(
                        [&id.name, &id.short_name]
                            .into_iter()
                            .flatten()
                            .map(|n| n.value.clone()),
                    );
                }
            }
        }
        Some(names)
    }

    /// Whether a name newly visible in the root namespace can change an
    /// outcome recorded while this library was prepared.
    fn completes_root_name(&self, name: &str) -> bool {
        self.root_misses.contains(name)
            || self
                .unresolved
                .iter()
                .chain(&self.ambiguous)
                .any(|(_, q)| q.segments.first().is_some_and(|s| s.value == name))
    }

    /// The names a root-level import of a model makes visible in the root
    /// namespace, located through user syntax or this library's scope tables
    /// alone: no resolver, no aliases, no user-side re-exports. `None` when
    /// the target cannot be located that way; the caller then resolves
    /// jointly instead of guessing.
    fn imported_root_names(
        &self,
        model: &crate::model::Model,
        import: &Import,
    ) -> Option<HashSet<String>> {
        let mut names = HashSet::new();
        let first = import.target.segments.first()?.value.as_str();
        let mut roots = model.user_units().flat_map(|(_, u)| u.unit.members.iter());
        if let Some(root) = roots.find(|m| member_id(m).is_some_and(|id| id_matches(id, first))) {
            let mut member = root;
            for segment in &import.target.segments[1..] {
                member = member_body(member)?
                    .iter()
                    .find(|m| member_id(m).is_some_and(|id| id_matches(id, &segment.value)))?;
            }
            if matches!(member.kind, MemberKind::Alias(_)) {
                return None;
            }
            if import.is_namespace {
                user_member_names(
                    member_body(member).unwrap_or(&[]),
                    import.is_recursive,
                    import.is_import_all,
                    &mut names,
                )?;
            } else {
                member_names(member, &mut names)?;
                if import.is_recursive {
                    user_member_names(
                        member_body(member).unwrap_or(&[]),
                        true,
                        import.is_import_all,
                        &mut names,
                    )?;
                }
            }
            return Some(names);
        }
        let mut seen = HashSet::new();
        if import.is_namespace {
            let scope = self.library_path_scope(0, &import.target)?;
            self.library_scope_names(scope, import.is_recursive, &mut seen, &mut names)?;
        } else {
            let (owner, elem) = self.library_path_member(0, &import.target)?;
            self.library_elem_names(owner, elem, &mut names);
            if import.is_recursive {
                if let Some(&sub) = self.elem_scope.get(&elem) {
                    self.library_scope_names(sub, true, &mut seen, &mut names)?;
                }
            }
        }
        Some(names)
    }

    /// The single element a library path names, walking declared names only,
    /// with the scope it was found in.
    fn library_path_member(&self, from: usize, qn: &QualifiedName) -> Option<(usize, usize)> {
        let first = qn.segments.first()?;
        let mut scope = if qn.is_global {
            0
        } else {
            let mut s = from;
            loop {
                if self.scopes[s].names.get(&first.value).is_some() {
                    break s;
                }
                s = self.scopes[s].parent?;
            }
        };
        let mut found = None;
        for segment in &qn.segments {
            let bindings = self.scopes[scope].names.get(&segment.value)?;
            let elem = bindings.first()?.elem;
            if bindings.iter().any(|b| b.elem != elem) {
                return None;
            }
            found = Some((scope, elem));
            scope = match bindings.iter().find_map(|b| b.sub_scope) {
                Some(sub) => sub,
                None if std::ptr::eq(segment, qn.segments.last()?) => break,
                None => return None,
            };
        }
        found
    }

    fn library_path_scope(&self, from: usize, qn: &QualifiedName) -> Option<usize> {
        let (_, elem) = self.library_path_member(from, qn)?;
        self.elem_scope.get(&elem).copied()
    }

    /// Every declared or inferred name of `elem` within `scope`.
    fn library_elem_names(&self, scope: usize, elem: usize, out: &mut HashSet<String>) {
        let scope = &self.scopes[scope];
        for (name, bindings) in scope.names.iter().chain(scope.effective_names.iter()) {
            if bindings.iter().any(|b| b.elem == elem) {
                out.insert(name.to_owned());
            }
        }
    }

    /// Names visible through a namespace import of library scope `s`,
    /// including re-exports through its public imports. `None` when a
    /// re-export target cannot be located without the resolver.
    fn library_scope_names(
        &self,
        s: usize,
        recursive: bool,
        seen: &mut HashSet<(usize, bool)>,
        out: &mut HashSet<String>,
    ) -> Option<()> {
        if !seen.insert((s, recursive)) {
            return Some(());
        }
        let scope = &self.scopes[s];
        for (name, bindings) in scope.names.iter().chain(scope.effective_names.iter()) {
            out.insert(name.to_owned());
            if recursive {
                for sub in bindings.iter().filter_map(|b| b.sub_scope) {
                    self.library_scope_names(sub, true, seen, out)?;
                }
            }
        }
        for (name, _, _) in &scope.aliases {
            out.insert(name.clone());
        }
        for &(name, _, _) in &scope.implied_ends {
            out.insert(name.to_owned());
        }
        for import in &scope.imports {
            if import.is_public {
                let target = self.library_path_scope(s, &import.target)?;
                self.library_scope_names(target, recursive || import.recursive, seen, out)?;
            }
        }
        for import in &scope.member_imports {
            if import.is_public {
                let (owner, elem) = self.library_path_member(s, &import.target)?;
                self.library_elem_names(owner, elem, out);
                if recursive {
                    if let Some(&sub) = self.elem_scope.get(&elem) {
                        self.library_scope_names(sub, true, seen, out)?;
                    }
                }
            }
        }
        Some(())
    }

    fn build_on_library(&mut self, model: &crate::model::Model, library: &Builder) -> usize {
        *self = library.clone();
        self.keep_path_hashes();
        self.semantic_ready = false;
        let boundary = self.elements.len();
        // Query outcomes are local to this model. In particular a root miss
        // in a library-only world must not hide a newly introduced user name.
        self.reset_lookup_caches();
        self.exclude = None;
        self.pending_exclude = None;
        self.declared_only = false;
        self.pending_declared_only = false;
        let mut roots = Vec::new();
        for (orig, unit) in model.user_units() {
            self.unit_starts.push((self.elements.len(), orig));
            self.scope_starts.push((self.scopes.len(), orig));
            self.dialect = unit.unit.dialect;
            let root = self.new_element("Namespace", None, format!("$root/{}", unit.name));
            roots.push(root);
            for (i, member) in unit.unit.members.iter().enumerate() {
                self.build_member(member, root, 0, i);
            }
            self.restore_payload_flags(model, orig, root);
        }
        // The outcomes the previous build settled on, where this build's
        // units resolve the references they did then (see `settled`).
        self.seed = model
            .take_settled()
            .and_then(|settled| self.seed_from(&self.pending, &settled));
        self.keep_settled = model.keeps_settled();
        self.resolve_pending();
        if let Some(settled) = self.settled.take() {
            model.deposit_settled(settled);
        }
        self.assign_user_ids(boundary, &roots);
        self.path_hashes = None;
        boundary
    }

    fn restore_payload_flags(&mut self, model: &crate::model::Model, unit: usize, start: usize) {
        let Some(records) = model.payload_source_flags(unit) else {
            return;
        };
        self.payload_source_units.insert(unit);
        if records.is_empty() {
            return;
        }
        for i in start..self.elements.len() {
            let Some(record) = records
                .get(&whole_path(&self.elements, i))
                .filter(|record| record.metaclass == self.elements[i].ty)
            else {
                continue;
            };
            for &key in crate::model::PAYLOAD_USAGE_FLAGS {
                if let Some(value) = record.flags.get(key) {
                    self.elements[i]
                        .props
                        .insert_payload_flag(key, value.to_json());
                }
            }
        }
    }

    pub(crate) fn prepare_facts(&mut self) -> crate::check::facts::Facts {
        let used = self.used_imports.clone();
        let facts = crate::check::facts::Facts::new(self);
        self.used_imports = used;
        facts
    }

    /// Empty per-scope lookup caches, one row per scope.
    fn reset_scope_tables(&mut self) {
        use crate::layered::ScopeTable;
        let (floor, n) = (self.scope_floor, self.scopes.len());
        self.import_cache = ScopeTable::new(floor, n);
        self.base_cache = ScopeTable::new(floor, n);
        self.import_misses = ScopeTable::new(floor, n);
        self.base_misses = ScopeTable::new(floor, n);
        self.visit_stamp = ScopeTable::new(floor, n);
        self.visit_result = ScopeTable::new(floor, n);
    }

    pub(crate) fn reset_lookup_caches(&mut self) {
        self.parameter_signatures = None;
        self.reset_scope_tables();
        self.recursive_subs.clear();
        self.semantic_metadata_misses = FillMisses::None;
        self.fill_frames.clear();
        self.query_stamp = 0;
        self.import_targets.clear();
        self.recorded_lookup_graph = None;
        self.semantic_metadata = None;
        // `id_index` stays: the ids it tables change only where identities
        // are assigned, which discards it itself.
        self.spec_index = None;
        self.mult_index = None;
        self.positional_redefinitions = None;
        self.supported_implied = None;
        self.inherited_cache.clear();
        self.inherited_by_heritage.clear();
        self.filters_active = vec![false; self.filter_exprs.len()];
        self.member_import_active.clear();
    }

    pub(crate) fn suppress_semantic_publication(&mut self) {
        self.publication.suppress();
    }

    pub(crate) fn freeze_library(&mut self) {
        assert!(
            self.implied.is_none() && self.implied_from.is_none(),
            "prepared libraries contain source rows only"
        );
        self.publication.suppress();
        if self.recorded_lookup_candidate
            && !self.recorded_lookup_incomplete
            && self.lib_boundary == self.elements.len()
            && !self.library_refs_to_users
        {
            let mut graph = self
                .recorded_lookup_graph
                .take()
                .unwrap_or_else(|| recorded_lookup::Graph::build(self));
            graph.freeze();
            self.recorded_lookup_prefix = Some(Arc::new(graph));
        } else {
            self.recorded_lookup_prefix = None;
        }
        for i in 0..self.elements.len() {
            let row = &self.elements[i];
            // A whole path under a parent holds a `/`, so it is neither empty
            // nor `first`; it ends as its own segment does.
            if row.path_parent.is_some() || (!row.path.is_empty() && row.path != "first") {
                let first = row.path.ends_with("first");
                let row = &mut self.elements[i];
                row.path = if first { "first".into() } else { String::new() };
                row.path_parent = None;
            }
        }
        self.recorded_lookup_graph = None;
        // Builds on a prepared library never record resolution outcomes, and
        // each one starts from a copy of this builder.
        self.spec_misses.clear();
        self.ref_misses.clear();
        // Every build on these rows reads few of their scopes: their
        // per-scope caches keep the rows of these sparse.
        self.scope_floor = self.scopes.len();
        self.reset_scope_tables();
        self.elements.freeze();
        // the frozen rows' structural scan, shared by every build on them
        self.prefix_structure = structural_index::StoredStructure::prefix_of(self);
        // the frozen rows by id, shared with the kept lookup graph
        self.prefix_ids = Some(
            self.recorded_lookup_prefix
                .as_ref()
                .and_then(|graph| graph.frozen_ids())
                .unwrap_or_else(|| {
                    Arc::new(
                        self.elements
                            .iter()
                            .enumerate()
                            .map(|(i, e)| (e.id, i))
                            .collect(),
                    )
                }),
        );
        self.prefix_table_names = Arc::new(std::sync::OnceLock::new());
        self.scopes.freeze();
        self.semantic_memo.freeze();
        self.id_index = None;
        self.spec_index = None;
        self.mult_index = None;
        self.positional_redefinitions = None;
        self.supported_implied = None;
        self.inherited_cache.clear();
        self.inherited_by_heritage.clear();
        self.elem_scope.freeze();
        self.effective_hint.freeze();
        self.values.freeze();
        self.owned_cross_features.freeze();
        self.contract_exprs.freeze();
        self.transition_guards.freeze();
        self.decl_spans.freeze();
        self.member_spans.freeze();
        self.ctor_fields.freeze();
        self.return_params.freeze();
        self.usage_featuring.freeze();
        self.prefix_meta_next.freeze();
        self.metadata_of.freeze();
        if let Some(intrinsic) = &mut self.metadata_intrinsic {
            intrinsic.freeze();
        }
        self.explicit_metadata_annotations.freeze();
        self.conjugated_defs.freeze();
        self.lib_qnames.freeze();
        self.lib_mem_qnames.freeze();
        self.multiplicities.freeze();
        self.connector_ends.freeze();
        self.chain_subsettings.freeze();
        self.satisfy_by.freeze();
        self.spec_targets.freeze();
        self.spec_resolved.freeze();
        self.result_exprs.freeze();
        self.filter_exprs.freeze();
    }

    pub(crate) fn valid_library(&self, units: usize) -> bool {
        let n = self.elements.len();
        let ns = self.scopes.len();
        self.lib_boundary == n
            && ns > 0
            && self.pending.is_empty()
            && self.ref_sites.is_empty()
            && self.unit_starts.len() == units
            && self.scope_starts.len() == units
            && self
                .unit_starts
                .iter()
                .enumerate()
                .all(|(u, &(e, orig))| e < n && u == orig)
            && self.scope_starts.iter().all(|&(s, u)| s <= ns && u < units)
            && self.import_cache.len() == ns
            && self.base_cache.len() == ns
            && self.visit_stamp.len() == ns
            && self.visit_result.len() == ns
            && self.spec_resolved.len() == self.spec_targets.len()
            && self.elements.iter().all(|e| {
                e.owning_relationship.is_none_or(|r| r < n)
                    && e.owned_relationships.iter().all(|&r| r < n)
                    && e.children.iter().all(|&r| r < n)
            })
            && self.elements.iter().enumerate().all(|(i, e)| {
                e.children
                    .iter()
                    .all(|&c| self.elements[c].owning_relationship == Some(i))
                    && e.owning_relationship
                        .is_none_or(|r| self.elements[r].children.contains(&i))
            })
            && self
                .metadata_of
                .iter()
                .all(|(&target, sources)| target < n && sources.iter().all(|&source| source < n))
            && self.metadata_intrinsic.as_ref().is_none_or(|map| {
                map.iter().all(|(&target, sources)| {
                    target < n && sources.iter().all(|&source| source < n)
                })
            })
            && self
                .metadata_about
                .iter()
                .all(|(&target, sources)| target < n && sources.iter().all(|&source| source < n))
            && (self.metadata_about.is_empty() || self.metadata_intrinsic.is_some())
            && self
                .explicit_metadata_annotations
                .iter()
                .all(|&annotation| {
                    annotation < n
                        && crate::metaclass::conforms(self.elements[annotation].ty, "Annotation")
                })
            && self.semantic_memo.valid(n, ns)
            && self.scopes.iter().enumerate().all(|(s, scope)| {
                scope.parent.is_none_or(|p| p < s)
                    && scope.owner.is_none_or(|e| e < n)
                    && scope.filters.iter().all(|&f| f < self.filter_exprs.len())
                    && scope.imports.iter().all(|i| {
                        i.relationship < n && i.filters.iter().all(|&f| f < self.filter_exprs.len())
                    })
                    && scope.member_imports.iter().all(|i| {
                        i.relationship < n && i.filters.iter().all(|&f| f < self.filter_exprs.len())
                    })
                    && scope
                        .names
                        .values()
                        .chain(scope.effective_names.values())
                        .flatten()
                        .all(|b| b.elem < n && b.sub_scope.is_none_or(|s| s < ns))
            })
            && self.elem_scope.iter().all(|(&e, &s)| e < n && s < ns)
            && self
                .spec_targets
                .iter()
                .all(|(e, _, s, _)| *e < n && *s < ns)
            && self.spec_resolved.iter().all(|t| t.is_none_or(|e| e < n))
            && self
                .values
                .iter()
                .chain(&self.contract_exprs)
                .chain(&self.transition_guards)
                .all(|(&e, (s, _))| e < n && *s < ns)
            && self
                .multiplicities
                .iter()
                .all(|(e, s, _)| *e < n && *s < ns)
            && self.filter_exprs.iter().all(|(e, s, _)| *e < n && *s < ns)
            && self.filters_active.len() == self.filter_exprs.len()
    }

    fn build_model_inner(
        &mut self,
        model: &crate::model::Model,
        no_cache: bool,
    ) -> Result<usize, ()> {
        self.keep_path_hashes();
        let root_scope = self.push_scope(None);
        let mut ordered: Vec<_> = model
            .units()
            .iter()
            .enumerate()
            .filter(|(_, u)| u.is_library)
            .collect();
        let boundary_units = ordered.len();
        ordered.extend(
            model
                .units()
                .iter()
                .enumerate()
                .filter(|(_, u)| !u.is_library),
        );

        // Sealed snapshot: the cache is consulted *before* lowering so the
        // library elements are created with their final ids (no ownership
        // paths, no UUIDv5 hashing, no normative re-assignment). It is
        // trusted only after two post-lowering validations — the element
        // count at the boundary and the pending-sequence fingerprint —
        // either mismatch aborts to a cold rebuild (`Err`).
        let slot = if no_cache {
            crate::model::LibCacheSlot::Off
        } else {
            model.take_lib_cache_for_build()
        };
        let mut snapshot: Option<Arc<crate::libcache::LibraryCache>> = None;
        match slot {
            crate::model::LibCacheSlot::Use(cache)
                if cache.graph_format == self.graph_format && !top_level_shadowing(model) =>
            {
                self.lib_ids_in = Some((Arc::clone(&cache), 0));
                snapshot = Some(cache);
            }
            crate::model::LibCacheSlot::Record => {
                self.lib_record = Some(Vec::new());
            }
            _ => {}
        }

        let mut boundary = 0;
        let mut lib_roots = Vec::new();
        for (i, (orig, mu)) in ordered.iter().enumerate() {
            if i == boundary_units {
                boundary = self.elements.len();
            }
            self.unit_starts.push((self.elements.len(), *orig));
            self.scope_starts.push((self.scopes.len(), *orig));
            self.dialect = mu.unit.dialect;
            let root = self.new_element("Namespace", None, format!("$root/{}", mu.name));
            if mu.is_library {
                // KerML-owned libraries use the KerML URL prefix; everything
                // else (Systems + Domain libraries) uses the SysML prefix.
                let prefix = match mu.unit.dialect {
                    Dialect::Kerml => "https://www.omg.org/spec/KerML/",
                    Dialect::Sysml => "https://www.omg.org/spec/SysML/",
                };
                lib_roots.push((root, prefix));
            }
            for (m, member) in mu.unit.members.iter().enumerate() {
                self.build_member(member, root, root_scope, m);
            }
            self.restore_payload_flags(model, *orig, root);
        }
        if boundary_units == ordered.len() {
            boundary = self.elements.len();
        }
        self.lib_boundary = boundary;

        let lib_names_pending = if let Some(cache) = snapshot {
            let exhausted = self
                .lib_ids_in
                .as_ref()
                .is_none_or(|(cache, taken)| *taken >= cache.lib_ids.len());
            self.lib_ids_in = None;
            if !exhausted
                || boundary != cache.lib_ids.len()
                || cache.fingerprint != self.lib_pending_fingerprint()
            {
                return Err(());
            }
            self.lib_qnames = cache.lib_qnames.iter().cloned().collect();
            self.lib_mem_qnames = cache.lib_mem_qnames.iter().cloned().collect();
            // The pairs outlive the borrow of the cache they are read
            // from, so they are owned here rather than iterated in place.
            #[allow(clippy::needless_collect)]
            let hints: Vec<_> = cache
                .outcomes
                .iter()
                .copied()
                .zip(cache.outcome_misses.iter().cloned())
                .collect();
            self.lib_hints = Some(hints.into_iter());
            self.lib_hints_fixed_point = cache.fixed_point;
            // Recorded outcomes are replayed only where the user units cannot
            // have changed them; an unlocatable root contribution disables
            // replay for this build.
            self.replay_completions = self.root_completions(model);
            false
        } else {
            self.assign_library_ids(&lib_roots);
            true
        };

        let mut lib_fingerprint = 0u64;
        if self.lib_record.is_some() {
            lib_fingerprint = self.lib_pending_fingerprint();
        }
        self.resolve_pending();
        if lib_names_pending {
            // Needs resolved redefinition targets, hence after
            // `resolve_pending`; warm builds get the extended table from
            // the cache.
            self.record_lib_effective_names();
        }
        // Graph-derived user ids (IDS.md) — after resolution
        // (graph-effective names need resolved redefinition targets) and
        // after the library name tables are in place (targets of `:>>`
        // chains reaching into the library).
        let user_roots: Vec<usize> = self
            .unit_starts
            .iter()
            .map(|&(start, _)| start)
            .filter(|&start| start >= boundary)
            .collect();
        self.assign_user_ids(boundary, &user_roots);
        if let Some(recorded) = self.lib_record.take() {
            let (outcomes, outcome_misses) = recorded.into_iter().unzip();
            model.deposit_recorded(crate::libcache::LibraryCache {
                graph_format: self.graph_format,
                fixed_point: boundary_units == ordered.len() && !self.recorded_lookup_incomplete,
                outcomes,
                outcome_misses,
                fingerprint: lib_fingerprint,
                lib_ids: self.elements.iter().take(boundary).map(|e| e.id).collect(),
                lib_qnames: self.lib_qnames.iter().cloned().collect(),
                lib_mem_qnames: self.lib_mem_qnames.iter().cloned().collect(),
            });
        }
        self.path_hashes = None;
        Ok(boundary)
    }

    /// Order-sensitive hash of the library-origin pending references —
    /// the sequence a [`crate::libcache::LibraryCache`]'s outcomes are
    /// positionally aligned with.
    fn lib_pending_fingerprint(&self) -> u64 {
        let mut h = crate::libcache::Fnv::new();
        // One buffer for every name: the references run to five figures
        // on a full library and nothing outlives the hash.
        let mut spelled = String::new();
        for p in &self.pending {
            if p.elem >= self.lib_boundary {
                continue;
            }
            h.update(&(p.elem as u64).to_le_bytes());
            h.update(p.key.as_bytes());
            spelled.clear();
            p.qn.write_ref_string(&mut spelled);
            h.update(spelled.as_bytes());
        }
        h.finish()
    }

    /// Reassign standard-library element IDs to the normative name-based
    /// UUIDs of KerML clause 9.1: top-level standard library packages get
    /// `uuid5(NameSpace_URL, prefix + escapedName)`, every named — including
    /// *effectively* named (KerML 8.2.3.5, e.g. `item :>> shape : …`) —
    /// element under fully-named ancestry gets
    /// `uuid5(topPackageUuid, qualifiedName)`, the owning membership of such
    /// an element (any Membership kind) gets `…qualifiedName +
    /// "/owningMembership"`, alias Memberships get the alias's qualified
    /// name, and the document root Namespace gets `uuid5(top, "")`.
    /// Everything else is positional in the norm (1-based
    /// `ownedRelationship` indices — which count the implementation's
    /// implied-relationship closure, so they are not portable) and can never
    /// be referenced from user text; those elements keep this library's
    /// deterministic path-based IDs.
    fn assign_library_ids(&mut self, lib_roots: &[(usize, &'static str)]) {
        // Owning relationship → owned element indices.
        let mut owned_by_rel: Vec<Vec<usize>> = vec![Vec::new(); self.elements.len()];
        for (i, e) in self.elements.iter().enumerate() {
            if let Some(r) = e.owning_relationship {
                owned_by_rel[r].push(i);
            }
        }
        let mut remap: HashMap<Uuid, Uuid> = HashMap::new();
        for &(root, prefix) in lib_roots {
            let rels = self.elements[root].owned_relationships.clone();
            let mut tops: Vec<(usize, Uuid, String)> = Vec::new();
            for rel in rels {
                for pkg in owned_by_rel[rel].clone() {
                    if self.elements[pkg].ty != "LibraryPackage" {
                        continue;
                    }
                    let Some(name) = self.effective_name(pkg) else {
                        continue;
                    };
                    let esc = escape_name(&name);
                    let top =
                        Uuid::new_v5(&Uuid::NAMESPACE_URL, format!("{prefix}{esc}").as_bytes());
                    self.reassign_id(pkg, top, &mut remap);
                    self.lib_qnames.push((top, vec![name.clone()]));
                    self.assign_descendant_ids(
                        pkg,
                        &esc,
                        std::slice::from_ref(&name),
                        top,
                        &owned_by_rel,
                        &mut remap,
                    );
                    tops.push((rel, top, esc));
                }
            }
            // The document root Namespace and the package's owning
            // membership are derivable only when the file holds exactly one
            // library package (always true for the standard library).
            if let [(rel, top, esc)] = tops.as_slice() {
                self.reassign_id(root, Uuid::new_v5(top, b""), &mut remap);
                if self.elements[*rel].ty.ends_with("Membership") && owned_by_rel[*rel].len() == 1 {
                    let mid = Uuid::new_v5(top, format!("{esc}/owningMembership").as_bytes());
                    self.reassign_id(*rel, mid, &mut remap);
                    let name = self
                        .effective_name(owned_by_rel[*rel][0])
                        .unwrap_or_else(|| esc.clone());
                    self.lib_mem_qnames.push((mid, vec![name]));
                }
            }
        }
        if !remap.is_empty() {
            // Patch `@id` references captured during the library build.
            for i in 0..self.elements.len() {
                let e = &mut self.elements[i];
                for v in e.props.values_mut() {
                    v.remap(&remap);
                }
            }
        }
        self.id_index = None;
    }

    /// Extend `lib_qnames` with redefinition-named library members
    /// (`attribute :>> length;` inside a library type): the normative-id
    /// walk skips unnamed elements, but their *effective* names (KerML
    /// 8.2.3.5 — the first redefined/referenced feature) are how the pilot
    /// names them, and the full form derives `memberName`/`name` for
    /// cross-document redefinition targets from this table. IDs are not
    /// touched — only the name table grows.
    fn record_lib_effective_names(&mut self) {
        let boundary = self.lib_boundary.min(self.elements.len());
        let mut by_id: HashMap<Uuid, usize> = HashMap::with_capacity(boundary);
        for (i, e) in self.elements.iter().enumerate().take(boundary) {
            by_id.insert(e.id, i);
        }
        // Relationship index → its owner element index.
        let mut owner_of_rel: Vec<Option<usize>> = vec![None; self.elements.len()];
        for (o, e) in self.elements.iter().enumerate() {
            for &r in &e.owned_relationships {
                owner_of_rel[r] = Some(o);
            }
        }
        let mut segments: HashMap<usize, Vec<String>> = HashMap::new();
        for (id, segs) in &self.lib_qnames {
            if let Some(&i) = by_id.get(id) {
                segments.insert(i, segs.clone());
            }
        }
        // First explicit redefinition / reference-subsetting target id.
        fn target_of(elements: &crate::layered::LayeredVec<Elem>, i: usize) -> Option<Uuid> {
            for &r in &elements[i].owned_relationships {
                let rel = &elements[r];
                let key = match rel.ty {
                    "Redefinition" => "redefinedFeature",
                    "ReferenceSubsetting" => "referencedFeature",
                    _ => continue,
                };
                return rel
                    .props
                    .get(key)
                    .and_then(|v| v.get("@id"))
                    .and_then(|v| v.as_str())
                    .and_then(|s| Uuid::parse_str(s).ok());
            }
            None
        }
        // Iterate: a member may take its name from another effectively
        // named member (chains of `:>>` through the library).
        loop {
            let mut added: Vec<(usize, Vec<String>)> = Vec::new();
            for i in 0..boundary {
                if segments.contains_key(&i) {
                    continue;
                }
                let e = &self.elements[i];
                if e.ty.ends_with("Membership")
                    || e.props.get("declaredName").is_some_and(|v| !v.is_null())
                {
                    continue;
                }
                let Some(rel) = e.owning_relationship else {
                    continue;
                };
                let Some(owner) = owner_of_rel[rel] else {
                    continue;
                };
                let Some(owner_segs) = segments.get(&owner) else {
                    continue;
                };
                let Some(tid) = target_of(&self.elements, i) else {
                    continue;
                };
                let Some(&t) = by_id.get(&tid) else { continue };
                let name = self.elements[t]
                    .props
                    .get("declaredName")
                    .and_then(|v| v.as_str())
                    .map(|s| s.to_string())
                    .or_else(|| segments.get(&t).and_then(|s| s.last().cloned()));
                let Some(name) = name else { continue };
                let mut segs = owner_segs.clone();
                segs.push(name);
                added.push((i, segs));
            }
            if added.is_empty() {
                break;
            }
            for (i, segs) in added {
                self.lib_qnames.push((self.elements[i].id, segs.clone()));
                segments.insert(i, segs);
            }
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn assign_descendant_ids(
        &mut self,
        e: usize,
        qname: &str,
        segments: &[String],
        top: Uuid,
        owned_by_rel: &[Vec<usize>],
        remap: &mut HashMap<Uuid, Uuid>,
    ) {
        let rels = self.elements[e].owned_relationships.clone();
        for rel in rels {
            let kids = owned_by_rel[rel].clone();
            if kids.is_empty() {
                // An alias member — a bare `Membership` that owns no
                // element — is a *named relationship* in the norm and gets
                // the alias's qualified name as its ID.
                if self.elements[rel].ty == "Membership" {
                    let props = &self.elements[rel].props;
                    let name = props
                        .get("memberName")
                        .and_then(|v| v.as_str())
                        .or_else(|| props.get("memberShortName").and_then(|v| v.as_str()))
                        .map(|s| s.to_string());
                    if let Some(name) = name {
                        let aq = format!("{qname}::{}", escape_name(&name));
                        let id = Uuid::new_v5(&top, aq.as_bytes());
                        self.reassign_id(rel, id, remap);
                        let mut segs = segments.to_vec();
                        segs.push(name);
                        self.lib_mem_qnames.push((id, segs));
                    }
                }
                continue;
            }
            // Only membership-owned elements have qualified names in the
            // norm; a named element under a non-membership relationship is
            // positional (and never referenced from user text).
            if !self.elements[rel].ty.ends_with("Membership") {
                continue;
            }
            for kid in kids.iter().copied() {
                let Some(name) = self.id_name(kid) else {
                    continue;
                };
                let kq = format!("{qname}::{}", escape_name(&name));
                let id = Uuid::new_v5(&top, kq.as_bytes());
                self.reassign_id(kid, id, remap);
                let mut kid_segments = segments.to_vec();
                kid_segments.push(name.clone());
                self.lib_qnames.push((id, kid_segments.clone()));
                if kids.len() == 1 {
                    let mid = Uuid::new_v5(&top, format!("{kq}/owningMembership").as_bytes());
                    self.reassign_id(rel, mid, remap);
                    // Membership ids are referenced by membership imports
                    // (`importedMembership`); name them like their member so
                    // lift can print the import target.
                    self.lib_mem_qnames.push((mid, kid_segments.clone()));
                }
                self.assign_descendant_ids(kid, &kq, &kid_segments, top, owned_by_rel, remap);
            }
        }
    }

    /// The declared half of the naming rule: an element's own declared
    /// (short) name, with no derivation. `Self::graph_identity_name`
    /// carries the derived half; see it for the rule and its other
    /// implementations.
    pub(crate) fn effective_name(&self, e: usize) -> Option<String> {
        let props = &self.elements[e].props;
        props
            .get("declaredName")
            .and_then(|v| v.as_str())
            .or_else(|| props.get("declaredShortName").and_then(|v| v.as_str()))
            .map(|s| s.to_string())
    }

    /// The name an element's normative library ID derives from: declared
    /// name, declared short name, or — for unnamed features — the syntactic
    /// effective name recorded at lowering time (KerML 8.2.3.5).
    pub(crate) fn id_name(&self, e: usize) -> Option<String> {
        self.effective_name(e)
            .or_else(|| self.effective_hint.get(&e).cloned())
    }

    fn reassign_id(&mut self, e: usize, id: Uuid, remap: &mut HashMap<Uuid, Uuid>) {
        let old = self.elements[e].id;
        if old != id {
            remap.insert(old, id);
            self.elements[e].id = id;
        }
    }

    /// Versioned identity label used only by ID scheme 2. Its historical
    /// generic ReferenceSubsetting fallback is retained for decoder parity;
    /// it does not confer a semantic name. Keep this algorithm synchronized
    /// with `ids::walk`, independently of the public naming projection.
    fn graph_identity_name(&self, e: usize, tables: &mut IdentityTables) -> Option<String> {
        let named_reference = naming::reference_names_feature(
            self.elements[e].ty,
            self.elements[e]
                .owning_relationship
                .map(|r| self.elements[r].ty),
        )
        .then(|| {
            self.elements[e]
                .owned_relationships
                .iter()
                .copied()
                .find(|&r| self.elements[r].ty == "ReferenceSubsetting")
        })
        .flatten();
        for &r in &self.elements[e].owned_relationships {
            if named_reference.is_some() && Some(r) != named_reference {
                continue;
            }
            let rel = &self.elements[r];
            let key = match rel.ty {
                "Redefinition" => "redefinedFeature",
                "ReferenceSubsetting" => "referencedFeature",
                _ => continue,
            };
            let target = rel.props.get(key)?;
            if let Some(s) = target.get("@ref").and_then(|v| v.as_str()) {
                return Some(s.rsplit("::").next().unwrap_or(s).to_string());
            }
            let mut t = tables.index_of(&target.as_reference()?)?;
            if key == "referencedFeature"
                && naming::reference_names_feature_target(
                    self.elements[e].ty,
                    self.elements[e]
                        .owning_relationship
                        .map(|r| self.elements[r].ty),
                )
            {
                if let Some(last) = self.elements[t]
                    .owned_relationships
                    .iter()
                    .rev()
                    .find(|&&r| self.elements[r].ty == "FeatureChaining")
                {
                    t = tables.index_of(
                        &self.elements[*last]
                            .props
                            .get("chainingFeature")?
                            .as_reference()?,
                    )?;
                }
            }
            return tables.name(self, t);
        }
        None
    }

    /// Reassign user-element ids to the graph-derived scheme (IDS.md;
    /// id scheme 2): `id(child) = uuid5(id(parent),
    /// segment)`, chained from each unit root (whose id stays assigned
    /// — the root names the source unit, which the interchange graph
    /// does not carry). Segments: a single-member membership with a
    /// named member chains **past the membership** (member `"::" +
    /// escaped id-name` under the owner, membership `"m"` under the
    /// member); alias memberships `"::" + escapedName`; positional
    /// `r{i}`/`e{j}` otherwise. Named segments claim owner scope
    /// first-come; a collision drops the pair back positional. Runs
    /// after `resolve_pending` so graph-effective names see resolved
    /// redefinition targets. Library ids are untouched.
    fn assign_user_ids(&mut self, boundary: usize, roots: &[usize]) {
        let n = self.elements.len();
        if boundary >= n || roots.is_empty() {
            return;
        }
        // The rows read by id and by name: a build on frozen rows reads
        // the frozen rows' ids through the table their freeze kept and
        // their names on demand, and tables only its own rows; any other
        // build tables every row.
        let frozen = self
            .prefix_ids
            .clone()
            .filter(|ids| ids.len() == boundary && self.elements.base_untouched());
        let start = if frozen.is_some() { boundary } else { 0 };
        if frozen.is_some() {
            note_prefix_ids_served();
        }
        let mut tables = IdentityTables {
            start,
            by_id: crate::layered::IdMap::with_capacity_and_hasher(n - start, Default::default()),
            names: Vec::with_capacity(n - start),
            frozen,
            table_names: None,
        };
        // Pre-reassignment id → index, for resolved reference targets.
        for (i, e) in self.elements.iter().enumerate().skip(start) {
            tables.by_id.insert(e.id, i);
        }
        // Names: declared everywhere; library elements additionally
        // through the effective-name tables; unnamed user elements by
        // the graph-effective fixpoint (`:>>` chains may pass through
        // other effectively named members).
        for i in start..n {
            let id = self.elements[i].id;
            let mut name = self.effective_name(i);
            // The tables name the last row carrying an id of theirs, and
            // theirs are the frozen rows' ids.
            if name.is_none()
                && tables.by_id.get(&id) == Some(&i)
                && tables
                    .frozen
                    .as_ref()
                    .is_none_or(|frozen| frozen.contains_key(&id))
            {
                name = tables.table_name(self, id);
            }
            tables.names.push(name);
        }
        loop {
            let mut changed = false;
            for e in boundary..n {
                if tables.names[e - start].is_some() || self.elements[e].ty.ends_with("Membership")
                {
                    continue;
                }
                if let Some(name) = self.graph_identity_name(e, &mut tables) {
                    tables.names[e - start] = Some(name);
                    changed = true;
                }
            }
            if !changed {
                break;
            }
        }
        // Relationship → owned elements, creation (= array) order, for the
        // relationships the walk reaches: those owned from `boundary`.
        let mut owned_by_rel: Vec<Vec<usize>> = vec![Vec::new(); n - boundary];
        for (i, e) in self.elements.iter().enumerate().skip(boundary) {
            if let Some(r) = e.owning_relationship.filter(|&r| r >= boundary) {
                owned_by_rel[r - boundary].push(i);
            }
        }
        // Top-down walk: parents carry their final ids before children
        // derive from them.
        let mut remap: HashMap<Uuid, Uuid> = HashMap::new();
        let mut stack: Vec<usize> = roots.to_vec();
        while let Some(owner) = stack.pop() {
            let owner_id = self.elements[owner].id;
            let rels = self.elements[owner].owned_relationships.clone();
            let mut used: HashSet<String> = HashSet::new();
            for (i, rel) in rels.into_iter().enumerate() {
                let kids = if rel >= boundary {
                    owned_by_rel[rel - boundary].clone()
                } else {
                    // A frozen relationship claimed by a row of this build,
                    // which no production writer makes: its owned rows, as
                    // a table over every row lists them.
                    (0..n)
                        .filter(|&i| self.elements[i].owning_relationship == Some(rel))
                        .collect()
                };
                let membership = self.elements[rel].ty.ends_with("Membership");
                // The constructor result is a structural role, independent of
                // effective names and argument ordinals. In particular it must
                // not capture a legacy first argument's positional identity.
                if self.elements[owner].ty == "ConstructorExpression"
                    && self.elements[rel].ty == "ReturnParameterMembership"
                    && kids.len() == 1
                    && self.elements[kids[0]].ty == "Feature"
                {
                    let rel_id = Uuid::new_v5(&owner_id, b"result");
                    self.reassign_id(rel, rel_id, &mut remap);
                    self.reassign_id(kids[0], Uuid::new_v5(&rel_id, b"e0"), &mut remap);
                    stack.extend([rel, kids[0]]);
                    continue;
                }
                // A single-member membership whose member has an
                // id-name chains **past the membership**:
                // the member takes the owner-scope named segment, and
                // the membership is named by its member — neither
                // references the ordinal, so member insertion cannot
                // disturb named siblings. Owner-scope collisions
                // (duplicate member names, aliases) drop the pair
                // back to the positional chain.
                if membership && kids.len() == 1 {
                    if let Some(name) = tables.name(self, kids[0]) {
                        let named = format!("::{}", escape_name(&name));
                        if used.insert(named.clone()) {
                            let kid = kids[0];
                            let kid_id = Uuid::new_v5(&owner_id, named.as_bytes());
                            self.reassign_id(kid, kid_id, &mut remap);
                            stack.push(kid);
                            self.reassign_id(rel, Uuid::new_v5(&kid_id, b"m"), &mut remap);
                            stack.push(rel);
                            continue;
                        }
                    }
                }
                let mut seg = format!("r{i}");
                if kids.is_empty() && self.elements[rel].ty == "Membership" {
                    let props = &self.elements[rel].props;
                    if let Some(name) = props
                        .get("memberName")
                        .and_then(|v| v.as_str())
                        .or_else(|| props.get("memberShortName").and_then(|v| v.as_str()))
                    {
                        let named = format!("::{}", escape_name(name));
                        if used.insert(named.clone()) {
                            seg = named;
                        }
                    }
                }
                let rel_id = Uuid::new_v5(&owner_id, seg.as_bytes());
                self.reassign_id(rel, rel_id, &mut remap);
                // A relationship can own relationships of its own
                // (annotations, filters) — it owns in its own right.
                stack.push(rel);
                let mut kid_used: HashSet<String> = HashSet::new();
                for (j, kid) in kids.into_iter().enumerate() {
                    let mut kseg = format!("e{j}");
                    if membership {
                        if let Some(name) = tables.name(self, kid) {
                            let named = format!("::{}", escape_name(&name));
                            if kid_used.insert(named.clone()) {
                                kseg = named;
                            }
                        }
                    }
                    self.reassign_id(kid, Uuid::new_v5(&rel_id, kseg.as_bytes()), &mut remap);
                    stack.push(kid);
                }
            }
        }
        if remap.is_empty() {
            return;
        }
        self.id_index = None;
        self.supported_implied = None;
        // A library reference can resolve a root supplied by user units.
        // Remap those captured endpoints as well as user-owned references.
        fn needs_remap(atom: &crate::properties::Atom, remap: &HashMap<Uuid, Uuid>) -> bool {
            use crate::properties::Atom;
            match atom {
                Atom::Reference(_) => atom
                    .as_reference()
                    .is_some_and(|id| remap.contains_key(&id)),
                Atom::Array(values) => values.iter().any(|v| needs_remap(v, remap)),
                Atom::Object(values) => values.values().any(|v| needs_remap(v, remap)),
                _ => false,
            }
        }
        let reference_start = if self.library_refs_to_users {
            0
        } else {
            boundary
        };
        for i in reference_start..self.elements.len() {
            if i < boundary
                && !self.elements[i]
                    .props
                    .entries
                    .iter()
                    .any(|(_, v)| needs_remap(v, &remap))
            {
                continue;
            }
            let e = &mut self.elements[i];
            for v in e.props.values_mut() {
                v.remap(&remap);
            }
        }
        if let Some(record) = self.lib_record.as_mut() {
            for (target, _) in record {
                if let Some(id) = target.as_mut() {
                    if let Some(&new) = remap.get(id) {
                        *id = new;
                    }
                }
            }
        }
        // Final user identity assignment can expose UUID collisions that were
        // absent in the provisional lowering graph. Revalidate associations
        // before publishing immutable metadata navigation.
        self.refresh_metadata_associations();
    }

    fn finish(self, boundary: usize) -> Value {
        let end = self.elements.len();
        self.finish_range(boundary, end)
    }

    fn finish_range(&self, start: usize, end: usize) -> Value {
        // Materialize relationship arrays as {"@id"} references.
        let ids: Vec<Uuid> = self.elements.iter().map(|e| e.id).collect();
        let mut out = Vec::with_capacity(end - start);
        for i in start..end {
            let elem = &self.elements[i];
            let mut obj = Map::new();
            obj.insert("@type".into(), json!(elem.ty));
            obj.insert("@id".into(), json!(elem.id.to_string()));
            obj.insert("elementId".into(), json!(elem.id.to_string()));
            obj.insert("isImpliedIncluded".into(), json!(false));
            obj.insert(
                "ownedRelationship".into(),
                Value::Array(
                    elem.owned_relationships
                        .iter()
                        .map(|&i| id_value(ids[i]))
                        .collect(),
                ),
            );
            obj.insert(
                "owningRelationship".into(),
                elem.owning_relationship
                    .map(|i| id_value(ids[i]))
                    .unwrap_or(Value::Null),
            );
            obj.extend(elem.props.to_json());
            if !elem.children.is_empty() {
                obj.insert(
                    "ownedRelatedElement".into(),
                    Value::Array(elem.children.iter().map(|&i| id_value(ids[i])).collect()),
                );
            }
            out.push(Value::Object(obj));
        }
        Value::Array(out)
    }

    // ---- graph primitives ----

    fn push_scope(&mut self, parent: Option<usize>) -> usize {
        self.scopes.push(Scope {
            parent,
            ..Default::default()
        });
        self.import_cache.push(None);
        self.base_cache.push(None);
        self.import_misses.push(FillMisses::None);
        self.base_misses.push(FillMisses::None);
        self.visit_stamp.push([0; 6]);
        self.visit_result.push([None; 6]);
        self.scopes.len() - 1
    }

    /// Register an element's declared name and short name in `scope`, with
    /// its body scope `sub_scope`.
    fn register(&mut self, scope: usize, id: &Identification, elem: usize, sub_scope: usize) {
        self.bind_names(scope, id, elem, Some(sub_scope));
        self.elem_scope.insert(elem, sub_scope);
        self.scopes[sub_scope].owner = Some(elem);
    }

    /// Register the declared name and short name of an element that owns
    /// no members of its own — a named comment, documentation, textual
    /// representation, or dependency. Its owning membership names it in
    /// `scope` like any other member, so `about` clauses and qualified
    /// names reach it, but nothing resolves *through* it.
    fn register_leaf(&mut self, scope: usize, id: &Identification, elem: usize) {
        self.bind_names(scope, id, elem, None);
    }

    fn bind_names(
        &mut self,
        scope: usize,
        id: &Identification,
        elem: usize,
        sub_scope: Option<usize>,
    ) {
        let visibility = match self.elements[elem]
            .owning_relationship
            .and_then(|r| self.elements[r].props.get("visibility"))
            .and_then(|v| v.as_str())
        {
            Some("private") => LookupAccess::All,
            Some("protected") => LookupAccess::Protected,
            _ => LookupAccess::Public,
        };
        let binding = Binding {
            elem,
            sub_scope,
            visibility,
        };
        for name in id.name.iter().chain(&id.short_name) {
            self.scopes[scope].names.push(name.value.clone(), binding);
        }
    }

    /// Next replayed library element id, when a sealed snapshot is active.
    fn next_lib_id(&mut self) -> Option<Uuid> {
        self.lib_ids_in.as_mut().and_then(|(cache, taken)| {
            let id = cache.lib_ids.get(*taken).copied();
            *taken += 1;
            id
        })
    }

    fn new_element(&mut self, ty: &'static str, owner_rel: Option<usize>, path: String) -> usize {
        let id = match self.next_lib_id() {
            Some(id) => id,
            None => {
                let mut hash = sha1_smol::Sha1::new();
                hash_path(&mut hash, ID_NAMESPACE.as_bytes());
                hash_path(&mut hash, path.as_bytes());
                self.keep_path_hash(hash)
            }
        };
        self.elements.push(Elem {
            ty,
            id,
            path,
            path_parent: None,
            props: crate::properties::Properties::new(),
            owned_relationships: Default::default(),
            children: Default::default(),
            owning_relationship: owner_rel,
        });
        let idx = self.elements.len() - 1;
        if let Some(rel) = owner_rel {
            self.elements[rel].children.push(idx);
        }
        idx
    }

    /// Create a relationship element owned by `owner` (appended to its
    /// `ownedRelationship` list).
    /// The element's `@id` (for check-time id → index maps).
    pub(crate) fn elem_id(&self, i: usize) -> Uuid {
        self.elements[i].id
    }

    /// The number of explicit elements — the element list without the
    /// implied relationships the derivation layer may have appended.
    pub(crate) fn explicit_len(&self) -> usize {
        self.implied_from.unwrap_or(self.elements.len())
    }

    /// Keep the ownership-path hash state of each element created from
    /// here on, until the build ends.
    fn keep_path_hashes(&mut self) {
        self.path_hashes = Some(PathHashes {
            base: self.elements.len(),
            states: Vec::new(),
        });
    }

    /// The identity of the element about to be created, whose whole path
    /// `hash` has read after the identity namespace. Its state is kept for
    /// the element's children while a build lowers.
    fn keep_path_hash(&mut self, hash: sha1_smol::Sha1) -> Uuid {
        let id = path_id(&hash);
        let i = self.elements.len();
        if let Some(kept) = &mut self.path_hashes {
            if let Some(slot) = i.checked_sub(kept.base) {
                if kept.states.len() <= slot {
                    kept.states.resize(slot + 1, None);
                }
                kept.states[slot] = Some(hash);
            }
        }
        id
    }

    /// The identity of the element about to be created with `segment`
    /// appended to `parent`'s ownership path: the version-5 identity of the
    /// whole path, hashing only `/` and the segment onto the parent's kept
    /// state. Without a kept state the parent's whole path is hashed first.
    fn child_path_id(&mut self, parent: usize, segment: &str) -> Uuid {
        let kept = self
            .path_hashes
            .as_ref()
            .and_then(|kept| kept.states.get(parent.checked_sub(kept.base)?)?.clone());
        let mut hash = kept.unwrap_or_else(|| {
            let mut hash = sha1_smol::Sha1::new();
            hash_path(&mut hash, ID_NAMESPACE.as_bytes());
            hash_path(&mut hash, whole_path(&self.elements, parent).as_bytes());
            hash
        });
        hash_path(&mut hash, b"/");
        hash_path(&mut hash, segment.as_bytes());
        self.keep_path_hash(hash)
    }

    fn new_relationship(&mut self, ty: &'static str, owner: usize, path_seg: &str) -> usize {
        let (path, path_parent, id) = match self.next_lib_id() {
            // Sealed snapshot: paths only feed id derivation, so skip both.
            Some(id) => (String::new(), None, id),
            None => {
                let id = self.child_path_id(owner, path_seg);
                (path_seg.to_owned(), Some(owner), id)
            }
        };
        self.elements.push(Elem {
            ty,
            id,
            path,
            path_parent,
            props: crate::properties::Properties::new(),
            owned_relationships: Default::default(),
            children: Default::default(),
            owning_relationship: None,
        });
        let idx = self.elements.len() - 1;
        self.elements[owner].owned_relationships.push(idx);
        // owningRelatedElement is the owned counterpart on the relationship.
        let owner_id = self.elements[owner].id;
        self.elements[idx]
            .props
            .insert("owningRelatedElement", id_ref(owner_id));
        idx
    }

    /// Create an element owned via `rel` (`ownedRelatedElement`).
    fn new_owned_element(&mut self, ty: &'static str, rel: usize, name_seg: &str) -> usize {
        let (path, path_parent, id) = match self.next_lib_id() {
            // Sealed snapshot: paths only feed id derivation, so skip both.
            Some(id) => (String::new(), None, id),
            None => {
                let id = self.child_path_id(rel, name_seg);
                (name_seg.to_owned(), Some(rel), id)
            }
        };
        self.elements.push(Elem {
            ty,
            id,
            path,
            path_parent,
            props: crate::properties::Properties::new(),
            owned_relationships: Default::default(),
            children: Default::default(),
            owning_relationship: Some(rel),
        });
        let idx = self.elements.len() - 1;
        self.elements[rel].children.push(idx);
        idx
    }

    fn set(&mut self, elem: usize, key: &str, value: impl Into<crate::properties::Atom>) {
        self.elements[elem].props.insert(key, value);
    }

    fn set_identification(&mut self, elem: usize, id: &Identification) {
        if let Some(n) = id.name.as_ref().or(id.short_name.as_ref()) {
            self.decl_spans.insert(elem, n.span);
        }
        self.set(
            elem,
            "declaredName",
            id.name
                .as_ref()
                .map(|n| json!(n.value))
                .unwrap_or(Value::Null),
        );
        self.set(
            elem,
            "declaredShortName",
            id.short_name
                .as_ref()
                .map(|n| json!(n.value))
                .unwrap_or(Value::Null),
        );
    }

    /// Reference another element by qualified name: resolve now if possible,
    /// otherwise record for the post-pass.
    fn set_ref(&mut self, elem: usize, key: &str, scope: usize, target: &TargetRef) {
        self.set_ref_excluding(elem, key, scope, target, None);
    }

    /// [`Self::set_ref`], excluding `exclude` as a resolution result — for a
    /// feature's own specialization targets, which must not resolve to the
    /// feature itself through its registered effective name.
    fn set_ref_excluding(
        &mut self,
        elem: usize,
        key: &str,
        scope: usize,
        target: &TargetRef,
        exclude: Option<usize>,
    ) {
        let exclude = exclude.or(self.pending_exclude);
        match target {
            TargetRef::Name(qn) => {
                self.pending.push(PendingRef {
                    elem,
                    key: key.to_string(),
                    scope,
                    qn: qn.clone(),
                    exclude,
                    declared_only: self.pending_declared_only,
                    chain: None,
                    spec_idx: self.pending_spec_idx.take(),
                });
            }
            TargetRef::Chain(links) => {
                // Normative feature-chain serialization (KerMLExpressions
                // `OwnedFeatureChain`): the referencing relationship owns a
                // `Feature` carrying one FeatureChaining per link; link 1
                // resolves lexically, link *k* as a member (owned or
                // inherited via typing) of link *k−1*.
                let base = key.split('#').next().unwrap_or(key);
                // A membership that owns the chain feature is an
                // OwningMembership (SysML.xtext `TransitionSourceMember`,
                // KerMLExpressions.xtext `FeatureChainMember` /
                // `InstantiatedTypeMember`), whatever the referencing
                // site created it as.
                if self.elements[elem].ty == "Membership" {
                    self.elements[elem].ty = "OwningMembership";
                }
                let feature = self.new_owned_element("Feature", elem, &format!("{base}.chain"));
                for (i, link) in links.iter().enumerate() {
                    let fc =
                        self.new_relationship("FeatureChaining", feature, &format!("chaining{i}"));
                    self.set(fc, "isImplied", json!(false));
                    self.pending.push(PendingRef {
                        elem: fc,
                        key: "chainingFeature".to_string(),
                        scope,
                        qn: link.clone(),
                        exclude,
                        declared_only: false,
                        spec_idx: None,
                        chain: if i == 0 {
                            None
                        } else {
                            Some(links[..i].to_vec())
                        },
                    });
                }
                let feature_id = self.elements[feature].id;
                self.set(elem, key, id_ref(feature_id));
            }
        }
    }

    // ---- members ----

    fn visibility_value(v: Option<Visibility>) -> Value {
        match v {
            Some(Visibility::Public) | None => json!("public"),
            Some(Visibility::Private) => json!("private"),
            Some(Visibility::Protected) => json!("protected"),
        }
    }

    /// Lower an `import`/`expose` relationship. A bracket-filtered import
    /// (`import P::*[@Safety]`) owns an implicit anonymous *FilterPackage*
    /// (SysML.xtext `FilterPackage`): the outer relationship is always the
    /// namespace kind, its `importedNamespace` is an owned anonymous
    /// Package holding the actual import (a plain Membership/Namespace
    /// *Import* even under an expose, per `FilterPackageImport`) plus one
    /// private ElementFilterMembership per bracket. The inner import must
    /// stay public — the outer import sees only the filter package's
    /// visible memberships.
    fn emit_import_rel(
        &mut self,
        imp: &Import,
        owner: usize,
        scope: usize,
        seg: &str,
        vis: Value,
        expose: bool,
    ) -> usize {
        let key = if imp.is_namespace {
            "importedNamespace"
        } else {
            "importedMembership"
        };
        if imp.filters.is_empty() {
            let ty = match (expose, imp.is_namespace) {
                (false, true) => "NamespaceImport",
                (false, false) => "MembershipImport",
                (true, true) => "NamespaceExpose",
                (true, false) => "MembershipExpose",
            };
            let rel = self.new_relationship(ty, owner, seg);
            self.set(rel, "visibility", vis);
            self.set(rel, "isImplied", json!(false));
            // Exposes are always import-all (pilot `*ExposeImpl`).
            self.set(rel, "isImportAll", json!(imp.is_import_all || expose));
            self.set(rel, "isRecursive", json!(imp.is_recursive));
            self.set_ref(rel, key, scope, &TargetRef::Name(imp.target.clone()));
            return rel;
        }
        let outer_ty = if expose {
            "NamespaceExpose"
        } else {
            "NamespaceImport"
        };
        let rel = self.new_relationship(outer_ty, owner, seg);
        self.set(rel, "visibility", vis);
        self.set(rel, "isImplied", json!(false));
        self.set(rel, "isImportAll", json!(imp.is_import_all || expose));
        self.set(rel, "isRecursive", json!(false));
        let pkg = self.new_owned_element("Package", rel, "filter");
        self.set(pkg, "declaredName", Value::Null);
        self.set(pkg, "declaredShortName", Value::Null);
        let pkg_id = self.elements[pkg].id;
        self.set(rel, "importedNamespace", id_ref(pkg_id));
        let inner_ty = if imp.is_namespace {
            "NamespaceImport"
        } else {
            "MembershipImport"
        };
        let inner = self.new_relationship(inner_ty, pkg, "import0");
        self.set(inner, "visibility", json!("public"));
        self.set(inner, "isImplied", json!(false));
        self.set(inner, "isImportAll", json!(false));
        self.set(inner, "isRecursive", json!(imp.is_recursive));
        self.set_ref(inner, key, scope, &TargetRef::Name(imp.target.clone()));
        for (i, f) in imp.filters.iter().enumerate() {
            let efm = self.new_relationship("ElementFilterMembership", pkg, &format!("filter{i}"));
            // `[` maps to private (`FilterPackageMemberVisibility`).
            self.set(efm, "visibility", json!("private"));
            self.set(efm, "isImplied", json!(false));
            self.build_expr(f, efm, scope, "condition");
        }
        rel
    }

    /// `#Meta` prefix metadata → owned MetadataUsage members. Bare
    /// about-less `@M;` body members canonicalize to the same shape (the
    /// pilot owns both spellings identically — `PrefixMetadataMember` /
    /// `AnnotatingMember` both return OwningMembership — so compact JSON
    /// cannot distinguish them; sharing segments makes the deterministic
    /// IDs agree and the round-trip converge on either spelling).
    fn emit_prefix_metadata(&mut self, owner: usize, metadata: &[QualifiedName], scope: usize) {
        for m in metadata {
            self.emit_prefix_metadata_one(owner, m, scope);
        }
    }

    fn emit_prefix_metadata_one(&mut self, owner: usize, m: &QualifiedName, scope: usize) {
        let n = self.prefix_meta_next.entry(owner).or_insert(0);
        let i = *n;
        *n += 1;
        let rel = self.new_relationship("OwningMembership", owner, &format!("prefixmeta{i}"));
        self.set(rel, "isImplied", json!(false));
        self.set(rel, "visibility", json!("public"));
        let e = self.new_owned_element("MetadataUsage", rel, &format!("meta{i}"));
        // Annotating metadata is unfeatured and referential. `isVariation`
        // has no metamodel default, so it is spelled even on synthesized
        // usages (XMI audit) — while `isAbstract` stays
        // absent, which is what `take_prefix_metadata` keys on.
        self.set(e, "isComposite", json!(false));
        self.set(e, "isVariation", json!(false));
        let ft = self.new_relationship("FeatureTyping", e, "typing");
        self.set(ft, "isImplied", json!(false));
        // Record before creating the pending reference so its outcome is
        // indexed just like an explicitly written metadata typing.
        self.spec_targets
            .push((e, "FeatureTyping", scope, m.clone()));
        self.pending_spec_idx = Some(self.spec_targets.len() - 1);
        self.set_ref(ft, "type", scope, &TargetRef::Name(m.clone()));
        let e_id = self.elements[e].id;
        self.set(ft, "typedFeature", id_ref(e_id));
        self.record_intrinsic_metadata(owner, e);
    }

    fn build_member(&mut self, member: &Member, owner: usize, scope: usize, index: usize) {
        let watermark = self.elements.len();
        self.build_member_inner(member, owner, scope, index);
        // Record the member's full source extent (keyword through body or
        // terminator) on the first element it owns — the transformation
        // SDK's remove/insert anchor. Nested members record their own
        // extents in their own frames; scaffolding relationships have no
        // owning relationship and are skipped.
        if let Some(i) = (watermark..self.elements.len()).find(|&i| {
            self.elements[i]
                .owning_relationship
                .is_some_and(|r| r >= watermark)
        }) {
            self.member_spans.entry(i).or_insert(member.span);
        }
        // A leading `then` synthesizes an EmptySuccession before building
        // the written usage, so the first element above is the succession,
        // not the declaration transformation callers address. Record the
        // same outer member extent on the earliest declared element too
        // (the usage's name precedes every named member in its body).
        if member.leading_then {
            let declared = self
                .decl_spans
                .iter()
                .filter(|(i, span)| {
                    **i >= watermark
                        && span.start >= member.span.start
                        && span.end <= member.span.end
                })
                .min_by_key(|(_, span)| span.start)
                .map(|(&i, _)| i);
            if let Some(i) = declared {
                self.member_spans.entry(i).or_insert(member.span);
            }
        }
    }

    fn build_member_inner(&mut self, member: &Member, owner: usize, scope: usize, index: usize) {
        if matches!(
            self.elements[owner].ty,
            "CalculationDefinition" | "CalculationUsage" | "Function" | "Expression"
        ) && member_requires_execution(member)
        {
            self.executable_calculations.insert(owner);
        }
        // Implied empty succession from a bare leading `then`. The pilot's
        // EmptySuccession rule owns two bare ends (MultiplicitySourceEndMember
        // + EmptyTargetEndMember).
        if member.leading_then {
            let rel = self.new_relationship("FeatureMembership", owner, &format!("m{index}then"));
            self.set(rel, "isImplied", json!(false));
            self.set(rel, "visibility", json!("public"));
            let succ = self.new_owned_element("SuccessionAsUsage", rel, "emptySuccession");
            self.set(succ, "isComposite", json!(false));
            self.set(succ, "isVariation", json!(false));
            let mut source = Self::empty_connector_end();
            source.multiplicity = member.leading_then_multiplicity.clone();
            self.emit_connector_end(succ, &source, scope, 0);
            let empty = Self::empty_connector_end();
            self.emit_connector_end(succ, &empty, scope, 1);
        }
        match &member.kind {
            MemberKind::Package(p) => {
                let seg =
                    p.id.name
                        .as_ref()
                        .map(|n| n.value.clone())
                        .unwrap_or_else(|| format!("#{index}"));
                let rel = self.new_relationship("OwningMembership", owner, &format!("m{index}"));
                self.set(rel, "visibility", Self::visibility_value(member.visibility));
                self.set(rel, "isImplied", json!(false));
                let ty = if p.is_namespace {
                    "Namespace"
                } else if p.is_library {
                    "LibraryPackage"
                } else {
                    "Package"
                };
                let pkg = self.new_owned_element(ty, rel, &seg);
                self.set_identification(pkg, &p.id);
                self.emit_prefix_metadata(pkg, &p.metadata, scope);
                if p.is_library {
                    self.set(pkg, "isStandard", json!(p.is_standard));
                }
                let pkg_scope = self.push_scope(Some(scope));
                self.register(scope, &p.id.clone(), pkg, pkg_scope);
                if let Some(body) = &p.body {
                    for (i, m) in body.iter().enumerate() {
                        self.build_member(m, pkg, pkg_scope, i);
                    }
                }
            }
            MemberKind::Import(imp) => {
                let rel = self.emit_import_rel(
                    imp,
                    owner,
                    scope,
                    &format!("import{index}"),
                    Self::visibility_value(member.visibility),
                    false,
                );
                self.user_imports.push(UserImport {
                    rel,
                    span: member.span,
                    scope,
                    visibility: member.visibility,
                });
                let fids = self.record_filters(&imp.filters, rel, scope);
                let is_public =
                    member.visibility.is_none() || member.visibility == Some(Visibility::Public);
                if imp.is_namespace {
                    self.scopes[scope].imports.push(NamespaceImport {
                        target: imp.target.clone(),
                        recursive: imp.is_recursive,
                        is_import_all: imp.is_import_all,
                        filters: fids,
                        relationship: rel,
                        is_public,
                    });
                } else {
                    self.scopes[scope].member_imports.push(MemberImport {
                        target: imp.target.clone(),
                        is_import_all: imp.is_import_all,
                        filters: fids.clone(),
                        relationship: rel,
                        is_public,
                    });
                    if imp.is_recursive {
                        // `import P::**` also brings the target's contents
                        // (recursively) into scope.
                        self.scopes[scope].imports.push(NamespaceImport {
                            target: imp.target.clone(),
                            recursive: true,
                            is_import_all: imp.is_import_all,
                            filters: fids,
                            relationship: rel,
                            is_public,
                        });
                    }
                }
            }
            MemberKind::Alias(a) => {
                let rel = self.new_relationship("Membership", owner, &format!("alias{index}"));
                self.set(rel, "visibility", Self::visibility_value(member.visibility));
                self.set(rel, "isImplied", json!(false));
                self.set(
                    rel,
                    "memberName",
                    a.id.name
                        .as_ref()
                        .map(|n| json!(n.value))
                        .unwrap_or(Value::Null),
                );
                self.set(
                    rel,
                    "memberShortName",
                    a.id.short_name
                        .as_ref()
                        .map(|n| json!(n.value))
                        .unwrap_or(Value::Null),
                );
                self.set_ref(
                    rel,
                    "memberElement",
                    scope,
                    &TargetRef::Name(a.target.clone()),
                );
                for name in a.id.name.iter().chain(a.id.short_name.iter()) {
                    if self.scopes[scope]
                        .aliases
                        .last()
                        .is_some_and(|entry| entry.2 == rel && entry.0 == name.value)
                    {
                        continue;
                    }
                    let index = self.scopes[scope].aliases.len();
                    self.alias_origins
                        .insert((scope, index), self.unit_of_elem(rel));
                    self.scopes[scope]
                        .aliases
                        .push((name.value.clone(), a.target.clone(), rel));
                }
            }
            MemberKind::Comment(c) => {
                let rel = self.new_relationship("OwningMembership", owner, &format!("m{index}"));
                self.set(rel, "visibility", Self::visibility_value(member.visibility));
                self.set(rel, "isImplied", json!(false));
                let e = self.new_owned_element("Comment", rel, &format!("comment{index}"));
                self.set_identification(e, &c.id);
                self.register_leaf(scope, &c.id, e);
                self.set(e, "body", json!(process_comment_body(&c.body)));
                self.set(
                    e,
                    "locale",
                    c.locale.as_ref().map(|l| json!(l)).unwrap_or(Value::Null),
                );
                for (i, about) in c.about.iter().enumerate() {
                    let ann = self.new_relationship("Annotation", e, &format!("about{i}"));
                    self.set(ann, "isImplied", json!(false));
                    self.set_ref(
                        ann,
                        "annotatedElement",
                        scope,
                        &TargetRef::Name(about.clone()),
                    );
                }
            }
            MemberKind::Doc(d) => {
                let rel = self.new_relationship("OwningMembership", owner, &format!("m{index}"));
                self.set(rel, "visibility", Self::visibility_value(member.visibility));
                self.set(rel, "isImplied", json!(false));
                let e = self.new_owned_element("Documentation", rel, &format!("doc{index}"));
                self.set_identification(e, &d.id);
                self.register_leaf(scope, &d.id, e);
                self.set(e, "body", json!(process_comment_body(&d.body)));
                self.set(
                    e,
                    "locale",
                    d.locale.as_ref().map(|l| json!(l)).unwrap_or(Value::Null),
                );
            }
            MemberKind::TextualRep(r) => {
                let rel = self.new_relationship("OwningMembership", owner, &format!("m{index}"));
                self.set(rel, "visibility", Self::visibility_value(member.visibility));
                self.set(rel, "isImplied", json!(false));
                let e =
                    self.new_owned_element("TextualRepresentation", rel, &format!("rep{index}"));
                self.set_identification(e, &r.id);
                self.register_leaf(scope, &r.id, e);
                self.set(e, "language", json!(r.language));
                self.set(e, "body", json!(r.body));
            }
            MemberKind::Filter(expr) => {
                let rel = self.new_relationship(
                    "ElementFilterMembership",
                    owner,
                    &format!("filter{index}"),
                );
                self.set(rel, "visibility", Self::visibility_value(member.visibility));
                self.set(rel, "isImplied", json!(false));
                self.build_expr(expr, rel, scope, "condition");
                // A namespace's filter conditions apply to every membership
                // it imports (resolution-side of ElementFilterMembership).
                let fids = self.record_filters(std::slice::from_ref(expr), rel, scope);
                self.scopes[scope].filters.extend(fids);
            }
            MemberKind::Definition(d) => self.build_definition(d, member, owner, scope, index),
            MemberKind::Usage(u) => self.build_usage(u, member, owner, scope, index),
            MemberKind::Dependency(d) => {
                let rel = self.new_relationship("OwningMembership", owner, &format!("m{index}"));
                self.set(rel, "visibility", Self::visibility_value(member.visibility));
                self.set(rel, "isImplied", json!(false));
                let e = self.new_owned_element("Dependency", rel, &format!("dependency{index}"));
                self.set_identification(e, &d.id);
                self.register_leaf(scope, &d.id, e);
                self.set(e, "isImplied", json!(false));
                self.emit_prefix_metadata(e, &d.metadata, scope);
                for (i, c) in d.clients.iter().enumerate() {
                    self.set_ref(
                        e,
                        &format!("client#{i}"),
                        scope,
                        &TargetRef::Name(c.clone()),
                    );
                }
                for (i, s) in d.suppliers.iter().enumerate() {
                    self.set_ref(
                        e,
                        &format!("supplier#{i}"),
                        scope,
                        &TargetRef::Name(s.clone()),
                    );
                }
            }
            MemberKind::InitialNode(qn) => {
                let rel = self.new_relationship("Membership", owner, &format!("m{index}first"));
                self.set(rel, "visibility", Self::visibility_value(member.visibility));
                self.set(rel, "isImplied", json!(false));
                self.set_ref(rel, "memberElement", scope, &TargetRef::Name(qn.clone()));
            }
            MemberKind::Subject(u) => {
                self.build_usage_with(
                    u,
                    member.visibility,
                    owner,
                    scope,
                    index,
                    "SubjectMembership",
                    Some("ReferenceUsage"),
                );
            }
            MemberKind::Actor(u) => {
                self.build_usage_with(
                    u,
                    member.visibility,
                    owner,
                    scope,
                    index,
                    "ActorMembership",
                    Some("PartUsage"),
                );
            }
            MemberKind::Stakeholder(u) => {
                self.build_usage_with(
                    u,
                    member.visibility,
                    owner,
                    scope,
                    index,
                    "StakeholderMembership",
                    Some("PartUsage"),
                );
            }
            MemberKind::Objective(u) => {
                self.build_usage_with(
                    u,
                    member.visibility,
                    owner,
                    scope,
                    index,
                    "ObjectiveMembership",
                    Some("RequirementUsage"),
                );
            }
            MemberKind::RequirementConstraint { kind, usage } => {
                let (rel, _) = self.build_usage_with(
                    usage,
                    member.visibility,
                    owner,
                    scope,
                    index,
                    "RequirementConstraintMembership",
                    Some("ConstraintUsage"),
                );
                let kind_str = match kind {
                    RequirementConstraintKind::Assumption => "assumption",
                    RequirementConstraintKind::Requirement => "requirement",
                };
                self.set(rel, "kind", json!(kind_str));
            }
            MemberKind::FramedConcern(u) => {
                let (rel, _) = self.build_usage_with(
                    u,
                    member.visibility,
                    owner,
                    scope,
                    index,
                    "FramedConcernMembership",
                    Some("ConcernUsage"),
                );
                self.set(rel, "kind", json!("requirement"));
            }
            MemberKind::RequirementVerification(u) => {
                let (rel, _) = self.build_usage_with(
                    u,
                    member.visibility,
                    owner,
                    scope,
                    index,
                    "RequirementVerificationMembership",
                    Some("RequirementUsage"),
                );
                self.set(rel, "kind", json!("requirement"));
            }
            MemberKind::StateSubaction { kind, action } => {
                let kind_str = match kind {
                    StateSubactionKind::Entry => "entry",
                    StateSubactionKind::Do => "do",
                    StateSubactionKind::Exit => "exit",
                };
                match action {
                    Some(u) => {
                        let (rel, _) = self.build_usage_with(
                            u,
                            member.visibility,
                            owner,
                            scope,
                            index,
                            "StateSubactionMembership",
                            None,
                        );
                        self.set(rel, "kind", json!(kind_str));
                    }
                    None => {
                        let rel = self.new_relationship(
                            "StateSubactionMembership",
                            owner,
                            &format!("m{index}"),
                        );
                        self.set(rel, "visibility", Self::visibility_value(member.visibility));
                        self.set(rel, "isImplied", json!(false));
                        self.set(rel, "kind", json!(kind_str));
                        let a = self.new_owned_element("ActionUsage", rel, kind_str);
                        self.set(a, "isVariation", json!(false));
                    }
                }
            }
            MemberKind::Expose(imp) => {
                // The `expose` keyword maps to protected visibility.
                let rel = self.emit_import_rel(
                    imp,
                    owner,
                    scope,
                    &format!("expose{index}"),
                    json!("protected"),
                    true,
                );
                // An expose is an import for name resolution: exposed
                // members are referencable within the view body.
                let fids = self.record_filters(&imp.filters, rel, scope);
                if imp.is_namespace {
                    self.scopes[scope].imports.push(NamespaceImport {
                        target: imp.target.clone(),
                        recursive: imp.is_recursive,
                        is_import_all: imp.is_import_all,
                        filters: fids,
                        relationship: rel,
                        is_public: false,
                    });
                } else {
                    self.scopes[scope].member_imports.push(MemberImport {
                        target: imp.target.clone(),
                        is_import_all: imp.is_import_all,
                        filters: fids.clone(),
                        relationship: rel,
                        is_public: false,
                    });
                    if imp.is_recursive {
                        // `expose P::**` also brings the target's
                        // contents (recursively) into scope — mirror of
                        // the import arm.
                        self.scopes[scope].imports.push(NamespaceImport {
                            target: imp.target.clone(),
                            recursive: true,
                            is_import_all: imp.is_import_all,
                            filters: fids,
                            relationship: rel,
                            is_public: false,
                        });
                    }
                }
            }
            MemberKind::Render(u) => {
                self.build_usage_with(
                    u,
                    member.visibility,
                    owner,
                    scope,
                    index,
                    "ViewRenderingMembership",
                    Some("RenderingUsage"),
                );
            }
            MemberKind::Return(u) => {
                let (_, e) = self.build_usage_with(
                    u,
                    member.visibility,
                    owner,
                    scope,
                    index,
                    "ReturnParameterMembership",
                    None,
                );
                self.return_params.insert(owner, e);
            }
            MemberKind::Result(expr) => {
                self.result_exprs.push((owner, scope, expr.clone()));
                let rel = self.new_relationship(
                    "ResultExpressionMembership",
                    owner,
                    &format!("m{index}result"),
                );
                self.set(rel, "visibility", Self::visibility_value(member.visibility));
                self.set(rel, "isImplied", json!(false));
                self.build_expr(expr, rel, scope, "expr");
            }
            MemberKind::Relationship(r) => {
                let rel = self.new_relationship("OwningMembership", owner, &format!("m{index}"));
                self.set(rel, "visibility", Self::visibility_value(member.visibility));
                self.set(rel, "isImplied", json!(false));
                let (ty, source_key, target_key) = relationship_decl_props(r.kind);
                let e = self.new_owned_element(ty, rel, &format!("rel{index}"));
                self.set_identification(e, &r.id);
                self.set(e, "isImplied", json!(false));
                self.set_ref(e, source_key, scope, &r.source);
                self.set_ref(e, target_key, scope, &r.target);
            }
            MemberKind::MultiplicityDecl(m) => {
                let rel = self.new_relationship("OwningMembership", owner, &format!("m{index}"));
                self.set(rel, "visibility", Self::visibility_value(member.visibility));
                self.set(rel, "isImplied", json!(false));
                let ty = if m.range.is_some() {
                    "MultiplicityRange"
                } else {
                    "Multiplicity"
                };
                let seg =
                    m.id.name
                        .as_ref()
                        .map(|n| n.value.clone())
                        .unwrap_or_else(|| format!("mult{index}"));
                let e = self.new_owned_element(ty, rel, &seg);
                self.set_identification(e, &m.id);
                if let Some(subsets) = &m.subsets {
                    let s = self.new_relationship("Subsetting", e, "subset");
                    self.set(s, "isImplied", json!(false));
                    self.set_ref(s, "subsettedFeature", scope, subsets);
                }
                if let Some(range) = &m.range {
                    self.multiplicities.push((e, scope, range.clone()));
                    // A multiplicity declaration owns its bound expressions
                    // directly (it *is* the MultiplicityRange).
                    if let Some(lower) = &range.lower {
                        let om = self.new_relationship("OwningMembership", e, "lower");
                        self.set(om, "isImplied", json!(false));
                        self.build_expr(lower, om, scope, "bound");
                    }
                    let om = self.new_relationship("OwningMembership", e, "upper");
                    self.set(om, "isImplied", json!(false));
                    self.build_expr(&range.upper, om, scope, "bound");
                }
                let body_scope = self.push_scope(Some(scope));
                self.register(scope, &m.id.clone(), e, body_scope);
                if let Some(body) = &m.body {
                    for (i, member) in body.iter().enumerate() {
                        self.build_member(member, e, body_scope, i);
                    }
                }
            }
        }
    }

    fn build_definition(
        &mut self,
        d: &Definition,
        member: &Member,
        owner: usize,
        scope: usize,
        index: usize,
    ) {
        let rel = self.new_relationship("OwningMembership", owner, &format!("m{index}"));
        self.set(rel, "visibility", Self::visibility_value(member.visibility));
        self.set(rel, "isImplied", json!(false));
        let seg =
            d.id.name
                .as_ref()
                .map(|n| n.value.clone())
                .unwrap_or_else(|| format!("#{index}"));
        let ty = def_metaclass(d.kind);
        let e = self.new_owned_element(ty, rel, &seg);
        self.set_identification(e, &d.id);
        self.emit_prefix_metadata(e, &d.prefix.metadata, scope);
        // Enumeration definitions are inherently variations (pilot
        // `EnumerationDefinitionImpl`), and a variation is implicitly
        // abstract (pilot `DefinitionAdapter.postProcess`).
        let is_variation = d.prefix.is_variation || d.kind == DefKind::Enum;
        self.set(e, "isAbstract", json!(d.prefix.is_abstract || is_variation));
        if declares_variation(ty) {
            self.set(e, "isVariation", json!(is_variation));
        }
        self.set(e, "isSufficient", json!(d.is_sufficient));
        if let Some(mult) = &d.multiplicity {
            self.emit_multiplicity(e, mult, scope);
        }
        for (i, t) in d.conjugates.iter().enumerate() {
            let c = self.new_relationship("Conjugation", e, &format!("conj{i}"));
            self.set(c, "isImplied", json!(false));
            self.set_ref(c, "originalType", scope, t);
        }
        for (kind, key, targets) in [
            ("Disjoining", "disjoiningType", &d.disjoint_from),
            ("Unioning", "unioningType", &d.unions),
            ("Intersecting", "intersectingType", &d.intersects),
            ("Differencing", "differencingType", &d.differences),
        ] {
            for (i, t) in targets.iter().enumerate() {
                let r = self.new_relationship(kind, e, &format!("{key}{i}"));
                self.set(r, "isImplied", json!(false));
                self.set_ref(r, key, scope, t);
            }
        }
        if d.prefix.is_individual || matches!(d.kind, DefKind::Occurrence | DefKind::Individual) {
            self.set(e, "isIndividual", json!(d.prefix.is_individual));
        }
        if d.kind == DefKind::State {
            self.set(e, "isParallel", json!(d.is_parallel));
        }
        let body_scope = self.push_scope(Some(scope));
        self.register(scope, &d.id.clone(), e, body_scope);
        // Specialization targets provide inherited-member resolution, plus
        // the kind's implied library base (resolution only, never emitted).
        for target in d.specializes.iter().chain(&d.conjugates) {
            if let TargetRef::Name(qn) = target {
                self.scopes[body_scope].bases.push(qn.clone());
            }
        }
        for base in implicit_def_bases(d.kind) {
            self.scopes[body_scope].implied_bases.push(lib_qn(base));
        }
        for (i, target) in d.specializes.iter().enumerate() {
            if let TargetRef::Name(qn) = target {
                self.spec_targets
                    .push((e, "Subclassification", scope, qn.clone()));
                // Record the pending outcome like usage specializations do
                // (`spec_resolved` via the superclassifier ref below) — the
                // recorded-only conformance walk behind implicit-redefinition
                // shadowing needs definition subclassifications too.
                self.pending_spec_idx = Some(self.spec_targets.len() - 1);
            }
            let sub = self.new_relationship("Subclassification", e, &format!("subcl{i}"));
            self.set(sub, "isImplied", json!(false));
            self.set_ref(sub, "superclassifier", scope, target);
            let e_id = self.elements[e].id;
            self.set(sub, "subclassifier", id_ref(e_id));
        }
        if let Some(body) = &d.body {
            for (i, m) in body.iter().enumerate() {
                self.in_enum_body = d.kind == DefKind::Enum;
                self.build_member(m, e, body_scope, i);
            }
            self.in_enum_body = false;
        }
        // SysML binary definition rules count owned ends. Their library
        // heritage must be available before resolving end redefinitions.
        if let Some((base, true)) = self.binary_owned_base(e) {
            self.scopes[body_scope].implied_bases.push(lib_qn(base));
        }
        // Every port definition owns its implicit conjugated definition
        // (pilot ConjugatedPortDefinitionMember, after the body): an
        // OwningMembership → ConjugatedPortDefinition `~P` whose
        // PortConjugation points back at the original. `~P` typings
        // resolve through the original and substitute this element.
        if d.kind == DefKind::Port && self.dialect == Dialect::Sysml {
            let om = self.new_relationship("OwningMembership", e, "conjugated");
            self.set(om, "isImplied", json!(false));
            self.set(om, "visibility", json!("public"));
            let name = d.id.name.as_ref().map(|n| format!("~{}", n.value));
            let cpd = self.new_owned_element(
                "ConjugatedPortDefinition",
                om,
                name.as_deref().unwrap_or("~"),
            );
            if let Some(name) = &name {
                self.set(cpd, "declaredName", json!(name));
            }
            // Definition-family usages spell defaultless `isVariation`
            // even when synthesized (XMI property audit).
            self.set(cpd, "isVariation", json!(false));
            let pc = self.new_relationship("PortConjugation", cpd, "conjugation");
            self.set(pc, "isImplied", json!(false));
            let e_id = self.elements[e].id;
            self.set(pc, "originalType", id_ref(e_id));
            self.set(pc, "originalPortDefinition", id_ref(e_id));
            let cpd_id = self.elements[cpd].id;
            self.set(pc, "conjugatedType", id_ref(cpd_id));
            self.conjugated_defs.insert(e, cpd);
        }
    }

    fn build_usage(
        &mut self,
        u: &Usage,
        member: &Member,
        owner: usize,
        scope: usize,
        index: usize,
    ) {
        // A bare about-less `@M;` member is indistinguishable from `#M`
        // prefix metadata in the pilot's abstract syntax — canonicalize to
        // the prefix shape (same segments, same bare element).
        if self.dialect != Dialect::Kerml
            && u.kind == UsageKind::Metadata
            && !self.in_enum_body
            && member.visibility.is_none()
            && u.prefix == UsagePrefix::default()
            && u.value.is_none()
            && u.body.as_ref().is_none_or(|b| b.is_empty())
            && matches!(&u.detail, UsageDetail::Metadata { about } if about.is_empty())
        {
            if let FeatureDeclaration {
                id,
                specializations,
                multiplicity: None,
                is_ordered: false,
                is_nonunique: false,
                ..
            } = &u.declaration
            {
                if id.name.is_none() && id.short_name.is_none() {
                    if let [FeatureSpecialization::TypedBy(types)] = &specializations[..] {
                        if let [
                            TypeRef {
                                target: TargetRef::Name(qn),
                                is_conjugated: false,
                            },
                        ] = &types[..]
                        {
                            let qn = qn.clone();
                            self.emit_prefix_metadata_one(owner, &qn, scope);
                            return;
                        }
                    }
                }
            }
        }
        let in_interface = matches!(
            self.elements[owner].ty,
            "InterfaceDefinition" | "InterfaceUsage"
        );
        let rel_ty = if self.in_enum_body || u.prefix.is_variant {
            // Direct enum-body members are enum literals: variant
            // memberships of the enumeration (SysML 8.3), like explicit
            // `variant` members of a variation.
            "VariantMembership"
        } else if u.prefix.is_end && in_interface {
            // Interface-body end members are plain occurrence members
            // (pilot InterfaceOccurrenceUsageMember); the keywordless
            // `end x : P;` is the DefaultInterfaceEnd PortUsage.
            "FeatureMembership"
        } else if u.prefix.is_end {
            "EndFeatureMembership"
        } else if u.kind == UsageKind::Metadata && self.dialect != Dialect::Kerml {
            // Metadata usages are AnnotatingElements: the pilot's
            // `AnnotatingMember`/`PrefixMetadataMember` own them via
            // OwningMembership even inside type bodies (so they are
            // unfeatured and referential).
            "OwningMembership"
        } else if u.prefix.is_type_member || is_namespace_metaclass(self.elements[owner].ty) {
            // FeatureMembership is for members of Types only; a usage owned
            // directly by a package/namespace lowers as OwningMembership
            // (SysML `PackageMember`, KerML `NamespaceFeatureMember`), like
            // a KerML `member`-prefixed type member.
            "OwningMembership"
        } else {
            "FeatureMembership"
        };
        let class_override = if u.prefix.is_end && in_interface && u.kind == UsageKind::Default {
            Some("PortUsage")
        } else {
            None
        };
        self.build_usage_with(
            u,
            member.visibility,
            owner,
            scope,
            index,
            rel_ty,
            class_override,
        );
    }

    /// Create the membership relationship and the usage element under it.
    /// `class_override` forces the element metaclass (e.g. `actor` members
    /// are PartUsages regardless of declared shape).
    #[allow(clippy::too_many_arguments)]
    fn build_usage_with(
        &mut self,
        u: &Usage,
        visibility: Option<Visibility>,
        owner: usize,
        scope: usize,
        index: usize,
        rel_ty: &'static str,
        class_override: Option<&'static str>,
    ) -> (usize, usize) {
        let rel = self.new_relationship(rel_ty, owner, &format!("m{index}"));
        self.set(rel, "visibility", Self::visibility_value(visibility));
        self.set(rel, "isImplied", json!(false));
        // Expected featuring type (pilot `UsageUtil.getExpectedFeaturingTypeOf`):
        // FeatureMembership-family ownership features the usage in the
        // owning Type; a variant is featured iff its variation usage is.
        self.pending_featuring = match rel_ty {
            "OwningMembership" | "Membership" => false,
            "VariantMembership" => self.usage_featuring.get(&owner).copied().unwrap_or(false),
            _ => true,
        };
        // ParameterMembership-family memberships force their parameter's
        // direction (pilot `ParameterMembershipAdapter.postProcess`):
        // subjects/actors/stakeholders are `in`, return parameters `out`.
        self.pending_direction = match rel_ty {
            "ReturnParameterMembership" => Some("out"),
            "SubjectMembership" | "ActorMembership" | "StakeholderMembership" => Some("in"),
            _ => None,
        };
        self.pending_owner_ty = Some(self.elements[owner].ty);
        let seg = u
            .declaration
            .id
            .name
            .as_ref()
            .map(|n| n.value.clone())
            .unwrap_or_else(|| format!("#{index}"));
        let e = self.build_usage_element(u, rel, scope, &seg, class_override);
        if let Some(n) = &u.declaration.id.name {
            self.ctor_fields
                .entry(owner)
                .or_default()
                .push((n.value.clone(), e));
        }
        // An about-less metadata member annotates its owner (import filters
        // test these annotations; `@M about x;` annotates `x` instead).
        if u.kind == UsageKind::Metadata
            && matches!(&u.detail, UsageDetail::Metadata { about } if about.is_empty())
        {
            self.record_intrinsic_metadata(owner, e);
        }
        (rel, e)
    }

    /// Build a usage element owned by an existing relationship.
    fn build_usage_element(
        &mut self,
        u: &Usage,
        rel: usize,
        scope: usize,
        seg: &str,
        class_override: Option<&'static str>,
    ) -> usize {
        // Direct enum-body members are enum literals (EnumerationUsage);
        // the flag is consumed here so nested members are not marked.
        let enum_literal = std::mem::take(&mut self.in_enum_body);
        let ty = if enum_literal {
            "EnumerationUsage"
        } else {
            class_override.unwrap_or_else(|| usage_metaclass(u.kind, self.dialect))
        };
        let e = self.new_owned_element(ty, rel, seg);
        // Captured before any nested member building can overwrite them.
        let featuring = self.pending_featuring;
        let forced_direction = self.pending_direction.take();
        let owner_ty = self.pending_owner_ty.take();
        self.set_identification(e, &u.declaration.id);
        self.emit_prefix_metadata(e, &u.prefix.metadata, scope);
        let body_scope = self.push_scope(Some(scope));
        if let Some(cross) = &u.prefix.end_cross {
            let om = self.new_relationship("OwningMembership", e, "crossFeature");
            self.set(om, "isImplied", json!(false));
            self.set(om, "visibility", json!("public"));
            let cf = self.new_owned_element("ReferenceUsage", om, "crossFeature");
            self.owned_cross_features.insert(e, cf);
            self.set(cf, "isVariation", json!(cross.is_variation));
            // The cross feature's own basic prefix; flags are emitted only
            // when set so cross-feature-free models are unchanged.
            if let Some(dir) = cross.direction {
                self.set(
                    cf,
                    "direction",
                    match dir {
                        FeatureDirection::In => json!("in"),
                        FeatureDirection::Out => json!("out"),
                        FeatureDirection::InOut => json!("inout"),
                    },
                );
            }
            if cross.is_derived {
                self.set(cf, "isDerived", json!(true));
            }
            if cross.is_abstract {
                self.set(cf, "isAbstract", json!(true));
            }
            if cross.is_constant {
                self.set(cf, "isConstant", json!(true));
            }
            if cross.is_composite {
                self.set(cf, "isComposite", json!(true));
            }
            if cross.is_portion {
                self.set(cf, "isPortion", json!(true));
            }
            if cross.is_variable {
                self.set(cf, "isVariable", json!(true));
            }
            self.set_identification(cf, &cross.decl.id);
            // The cross feature is an owned member of the end feature, so
            // its references see that end's members and inherited types.
            self.emit_specializations(cf, &cross.decl, body_scope);
            if let Some(mult) = &cross.decl.multiplicity {
                self.emit_multiplicity(cf, mult, body_scope);
            }
        }
        // A variation is implicitly abstract (pilot `UsageAdapter.postProcess`).
        self.set(
            e,
            "isAbstract",
            json!(u.prefix.is_abstract || u.prefix.is_variation),
        );
        if declares_variation(ty) {
            self.set(e, "isVariation", json!(u.prefix.is_variation));
        }
        self.set(e, "isDerived", json!(u.prefix.is_derived));
        self.set(e, "isConstant", json!(u.prefix.is_constant));
        self.set(e, "isEnd", json!(u.prefix.is_end));
        if self.dialect == Dialect::Kerml {
            self.set(e, "isComposite", json!(u.prefix.is_composite));
            self.set(e, "isPortion", json!(u.prefix.is_portion));
            self.set(
                e,
                "isVariable",
                json!(u.prefix.is_variable || u.prefix.is_constant),
            );
            self.set(e, "isSufficient", json!(u.declaration.is_sufficient));
        } else {
            // SysML usages are composite by default (pilot `UsageImpl`),
            // except the inherently referential metaclasses (pilot
            // constructors), `ref`/directed/end declarations, and usages
            // with no expected featuring type (`UsageAdapter.postProcess`).
            self.usage_featuring.insert(e, featuring);
            let composite = featuring
                && !matches!(
                    ty,
                    "AttributeUsage"
                        | "EnumerationUsage"
                        | "ReferenceUsage"
                        | "BindingConnectorAsUsage"
                        | "SuccessionAsUsage"
                        | "EventOccurrenceUsage"
                        | "ExhibitStateUsage"
                        | "IncludeUseCaseUsage"
                        | "PerformActionUsage"
                )
                && !u.prefix.is_ref
                && u.prefix.direction.is_none()
                && forced_direction.is_none()
                && !u.prefix.is_end
                // Ports are referential except as sub-ports (pilot
                // `PortUsageAdapter.postProcess`).
                && (ty != "PortUsage"
                    || matches!(owner_ty, Some("PortDefinition" | "PortUsage")));
            self.set(e, "isComposite", json!(composite));
        }
        self.set(e, "isOrdered", json!(u.declaration.is_ordered));
        self.set(e, "isUnique", json!(!u.declaration.is_nonunique));
        self.set(
            e,
            "direction",
            match u.prefix.direction {
                Some(FeatureDirection::In) => json!("in"),
                Some(FeatureDirection::Out) => json!("out"),
                Some(FeatureDirection::InOut) => json!("inout"),
                None => forced_direction.map(|d| json!(d)).unwrap_or(Value::Null),
            },
        );
        if u.prefix.is_individual || u.prefix.portion.is_some() || u.kind == UsageKind::Occurrence {
            self.set(e, "isIndividual", json!(u.prefix.is_individual));
            self.set(
                e,
                "portionKind",
                match u.prefix.portion {
                    Some(PortionKind::Snapshot) => json!("snapshot"),
                    Some(PortionKind::Timeslice) => json!("timeslice"),
                    None => Value::Null,
                },
            );
        }

        self.register(scope, &u.declaration.id.clone(), e, body_scope);
        // Unnamed features take an effective name from the first feature
        // they redefine (KerML 8.2.3.5) or reference (SysML variant/perform/
        // exhibit/… reference forms): `variant manualTransmission;` and
        // `:>> mass = 5;` are findable by those names. Resolution-only —
        // declaredName stays null.
        if u.declaration.id.name.is_none() && u.declaration.id.short_name.is_none() {
            if let Some(name) = effective_ref_name(
                &u.declaration,
                naming::reference_names_feature_target(ty, Some(self.elements[rel].ty)),
                self.elements[rel].ty == "VariantMembership",
            ) {
                self.effective_hint.insert(e, name.clone());
                self.scopes[scope].effective_names.push(
                    name,
                    Binding {
                        elem: e,
                        sub_scope: Some(body_scope),
                        visibility: match self.elements[rel]
                            .props
                            .get("visibility")
                            .and_then(|v| v.as_str())
                        {
                            Some("private") => LookupAccess::All,
                            Some("protected") => LookupAccess::Protected,
                            _ => LookupAccess::Public,
                        },
                    },
                );
            }
        }
        // Typing/subsetting/redefinition targets provide inherited-member
        // resolution within this usage's body.
        for spec in &u.declaration.specializations {
            let (targets, subsets): (Vec<&TargetRef>, bool) = match spec {
                FeatureSpecialization::TypedBy(types) => {
                    (types.iter().map(|t| &t.target).collect(), false)
                }
                FeatureSpecialization::Subsets(ts) => (ts.iter().collect(), true),
                FeatureSpecialization::Redefines(ts) => (ts.iter().collect(), false),
                FeatureSpecialization::References(t) | FeatureSpecialization::Crosses(t) => {
                    (vec![t], false)
                }
            };
            for t in targets {
                match t {
                    TargetRef::Name(qn) => {
                        if matches!(spec, FeatureSpecialization::Redefines(_)) {
                            self.scopes[body_scope]
                                .redefinition_spellings
                                .push(qn.clone());
                            if !qn.is_global && qn.segments.len() == 1 {
                                self.scopes[body_scope]
                                    .redefinition_names
                                    .insert(qn.segments[0].value.clone());
                            }
                        }
                        self.scopes[body_scope].bases.push(qn.clone());
                    }
                    TargetRef::Chain(links) if !links.is_empty() => {
                        self.scopes[body_scope].chain_bases.push(links.clone());
                        if subsets {
                            // Recorded for the featuring-accessibility
                            // check: a chain-written subsetting names a
                            // feature whose featuring context the
                            // subsetter must be able to reach.
                            self.chain_subsettings
                                .push((e, scope, links.clone(), links[0].span));
                        }
                    }
                    TargetRef::Chain(_) => {}
                }
            }
        }
        if self.dialect == Dialect::Sysml {
            let base_kind = if enum_literal {
                UsageKind::Enum
            } else {
                u.kind
            };
            for base in implicit_usage_bases(base_kind) {
                self.scopes[body_scope].implied_bases.push(lib_qn(base));
            }
        }
        // Every Step specializes the Kernel Semantic Library performance
        // feature, including untyped KerML steps.
        if crate::metaclass::conforms(ty, "Step") {
            self.scopes[body_scope]
                .implied_bases
                .push(lib_qn("Performances::performances"));
        }
        // Every Feature specializes Base::things, including ordinary KerML
        // features whose syntax kind has no SysML-specific implied base.
        // Its nested `that` feature must therefore participate in lookup.
        self.scopes[body_scope]
            .implied_bases
            .push(lib_qn("Base::things"));
        self.emit_specializations(e, &u.declaration, scope);

        if let Some(mult) = &u.declaration.multiplicity {
            self.emit_multiplicity(e, mult, scope);
        }
        self.finish_usage_element(u, e, scope, body_scope)
    }

    /// Specialization clauses of a feature declaration → relationship
    /// elements owned by `e`.
    fn emit_specializations(&mut self, e: usize, decl: &FeatureDeclaration, scope: usize) {
        // `spec_targets` (semantic-check side table) records alongside each
        // relationship; the pending ref reports its resolution outcome back
        // into `spec_resolved` via `pending_spec_idx`.
        let mut spec_counter = 0usize;
        for spec in &decl.specializations {
            match spec {
                FeatureSpecialization::TypedBy(types) => {
                    for t in types {
                        let ft = self.new_relationship(
                            "FeatureTyping",
                            e,
                            &format!("typing{spec_counter}"),
                        );
                        spec_counter += 1;
                        self.set(ft, "isImplied", json!(false));
                        // Conjugated port typing is its own metaclass in
                        // SysML; flagged here until modeled.
                        if t.is_conjugated {
                            self.elements[ft].ty = "ConjugatedPortTyping";
                        }
                        if let TargetRef::Name(qn) = &t.target {
                            self.spec_targets
                                .push((e, "FeatureTyping", scope, qn.clone()));
                            self.pending_spec_idx = Some(self.spec_targets.len() - 1);
                        }
                        self.set_ref(ft, "type", scope, &t.target);
                        let e_id = self.elements[e].id;
                        self.set(ft, "typedFeature", id_ref(e_id));
                    }
                }
                FeatureSpecialization::Subsets(targets) => {
                    for t in targets {
                        let s = self.new_relationship(
                            "Subsetting",
                            e,
                            &format!("subset{spec_counter}"),
                        );
                        spec_counter += 1;
                        self.set(s, "isImplied", json!(false));
                        if let TargetRef::Name(qn) = t {
                            self.spec_targets.push((e, "Subsetting", scope, qn.clone()));
                            self.pending_spec_idx = Some(self.spec_targets.len() - 1);
                        }
                        self.set_ref_excluding(s, "subsettedFeature", scope, t, Some(e));
                        let e_id = self.elements[e].id;
                        self.set(s, "subsettingFeature", id_ref(e_id));
                    }
                }
                FeatureSpecialization::Redefines(targets) => {
                    for t in targets {
                        let r = self.new_relationship(
                            "Redefinition",
                            e,
                            &format!("redef{spec_counter}"),
                        );
                        spec_counter += 1;
                        self.set(r, "isImplied", json!(false));
                        if let TargetRef::Name(qn) = t {
                            self.spec_targets
                                .push((e, "Redefinition", scope, qn.clone()));
                            self.pending_spec_idx = Some(self.spec_targets.len() - 1);
                        }
                        self.set_ref_excluding(r, "redefinedFeature", scope, t, Some(e));
                        let e_id = self.elements[e].id;
                        self.set(r, "redefiningFeature", id_ref(e_id));
                    }
                }
                FeatureSpecialization::References(t) => {
                    let r = self.new_relationship(
                        "ReferenceSubsetting",
                        e,
                        &format!("refsub{spec_counter}"),
                    );
                    spec_counter += 1;
                    self.set(r, "isImplied", json!(false));
                    self.set_ref_excluding(r, "referencedFeature", scope, t, Some(e));
                    let e_id = self.elements[e].id;
                    self.set(r, "subsettingFeature", id_ref(e_id));
                }
                FeatureSpecialization::Crosses(t) => {
                    let r = self.new_relationship(
                        "CrossSubsetting",
                        e,
                        &format!("cross{spec_counter}"),
                    );
                    spec_counter += 1;
                    self.set(r, "isImplied", json!(false));
                    self.set_ref_excluding(r, "crossedFeature", scope, t, Some(e));
                    let e_id = self.elements[e].id;
                    self.set(r, "subsettingFeature", id_ref(e_id));
                }
            }
        }
        // KerML feature-relationship parts.
        if let Some(t) = &decl.conjugates {
            let c = self.new_relationship("Conjugation", e, "conjugation");
            self.set(c, "isImplied", json!(false));
            self.set_ref(c, "originalType", scope, t);
        }
        if let Some(TargetRef::Chain(links)) = &decl.chains {
            for (i, link) in links.iter().enumerate() {
                let fc = self.new_relationship("FeatureChaining", e, &format!("chain{i}"));
                self.set(fc, "isImplied", json!(false));
                self.pending.push(PendingRef {
                    elem: fc,
                    key: "chainingFeature".to_string(),
                    scope,
                    qn: link.clone(),
                    exclude: self.pending_exclude,
                    declared_only: false,
                    chain: (i > 0 && !link.is_global).then(|| links[..i].to_vec()),
                    spec_idx: None,
                });
            }
        } else if let Some(t) = &decl.chains {
            let fc = self.new_relationship("FeatureChaining", e, "chain0");
            self.set(fc, "isImplied", json!(false));
            self.set_ref(fc, "chainingFeature", scope, t);
        }
        if let Some(t) = &decl.inverse_of {
            let fi = self.new_relationship("FeatureInverting", e, "inverting");
            self.set(fi, "isImplied", json!(false));
            self.set_ref(fi, "invertingFeature", scope, t);
        }
        for (i, t) in decl.featured_by.iter().enumerate() {
            let tf = self.new_relationship("TypeFeaturing", e, &format!("featuring{i}"));
            self.set(tf, "isImplied", json!(false));
            self.set_ref(tf, "featuringType", scope, t);
        }
        for (kind, key, targets) in [
            ("Disjoining", "disjoiningType", &decl.disjoint_from),
            ("Unioning", "unioningType", &decl.unions),
            ("Intersecting", "intersectingType", &decl.intersects),
            ("Differencing", "differencingType", &decl.differences),
        ] {
            for (i, t) in targets.iter().enumerate() {
                let r = self.new_relationship(kind, e, &format!("{key}{i}"));
                self.set(r, "isImplied", json!(false));
                self.set_ref(r, key, scope, t);
            }
        }
    }

    /// Value part, parallel flag, detail, and body of a usage element.
    fn finish_usage_element(
        &mut self,
        u: &Usage,
        e: usize,
        scope: usize,
        body_scope: usize,
    ) -> usize {
        if let Some(value) = &u.value {
            // Recorded for the evaluator: the expression and the scope it
            // resolves from.
            self.values.insert(e, (scope, value.expr.clone()));
            if matches!(value.kind, ValueKind::Default | ValueKind::DefaultInitial) {
                self.default_values.insert(e);
            }
            let fv = self.new_relationship("FeatureValue", e, "value");
            self.set(fv, "isImplied", json!(false));
            self.set(
                fv,
                "isInitial",
                json!(matches!(
                    value.kind,
                    ValueKind::Initial | ValueKind::DefaultInitial
                )),
            );
            self.set(
                fv,
                "isDefault",
                json!(matches!(
                    value.kind,
                    ValueKind::Default | ValueKind::DefaultInitial
                )),
            );
            // A feature's value expression must not resolve names to the
            // feature itself (its effective name — e.g. `:>> mass = …` —
            // would otherwise shadow the sibling/inherited feature the
            // expression means).
            let saved = self.pending_exclude;
            self.pending_exclude = Some(e);
            self.build_expr(&value.expr, fv, scope, "expr");
            self.pending_exclude = saved;
        }

        if matches!(u.kind, UsageKind::State | UsageKind::Exhibit) {
            self.set(e, "isParallel", json!(u.is_parallel));
        }

        // Canonicalization: bare end body-members of connection-family
        // usages (`connection : C { end r1 ::> req1; … }`) serialize exactly
        // like connect-part ends, so emit them through the detail path —
        // the two syntactic forms are indistinguishable in compact JSON and
        // must produce identical (deterministic) IDs.
        let mut detail = u.detail.clone();
        let mut body_members: Vec<&Member> = u.body.iter().flatten().collect();
        // (Interface bodies are excluded: their end members are the pilot's
        // DefaultInterfaceEnd PortUsages under plain FeatureMembership.)
        if matches!(
            u.kind,
            UsageKind::Connection | UsageKind::Allocation | UsageKind::Connector
        ) {
            let bare: Vec<usize> = body_members
                .iter()
                .enumerate()
                .filter_map(|(i, m)| bare_end_member(m).map(|_| i))
                .collect();
            let existing = match &detail {
                UsageDetail::Connector { ends } => ends.len(),
                UsageDetail::None => 0,
                _ => usize::MAX,
            };
            if existing != usize::MAX && existing + bare.len() >= 2 && !bare.is_empty() {
                let mut ends = match detail {
                    UsageDetail::Connector { ends } => ends,
                    _ => Vec::new(),
                };
                for &i in &bare {
                    if let Some(end) = bare_end_member(body_members[i]) {
                        ends.push(end);
                    }
                }
                for &i in bare.iter().rev() {
                    body_members.remove(i);
                }
                detail = UsageDetail::Connector { ends };
            }
        }

        if matches!(u.kind, UsageKind::Flow | UsageKind::SuccessionFlow) {
            self.payload_flows.insert(e);
        }
        let end_elems = self.build_usage_detail(e, &detail, scope);

        // Connector-part end declarations own the same lookup bindings as
        // ordinary end members. Their scopes inherit the connected feature,
        // with target names resolved outside the connector's body to avoid
        // capturing the end currently being declared.
        if matches!(
            u.kind,
            UsageKind::Connection
                | UsageKind::Interface
                | UsageKind::Allocation
                | UsageKind::Connector
        ) {
            if let UsageDetail::Connector { ends } = &detail {
                let binary = end_elems.len() == 2;
                if binary && self.dialect == Dialect::Sysml {
                    let base = match u.kind {
                        UsageKind::Connection => Some("Connections::binaryConnections"),
                        UsageKind::Interface => Some("Interfaces::binaryInterfaces"),
                        _ => None,
                    };
                    if let Some(base) = base {
                        self.scopes[body_scope].implied_bases.push(lib_qn(base));
                    }
                }
                for (i, (&end_elem, end)) in end_elems.iter().zip(ends).enumerate() {
                    let end_scope = self.push_scope(Some(scope));
                    if let Some(qn) = flat_target_qn(&end.target) {
                        self.scopes[end_scope].bases.push(qn);
                    }
                    self.register(
                        body_scope,
                        &Identification {
                            name: end.name.clone(),
                            short_name: None,
                        },
                        end_elem,
                        end_scope,
                    );
                    // The binary positional aliases remain a fallback after
                    // declared names, including a declared source or target.
                    if binary {
                        self.scopes[body_scope].implied_ends.push((
                            ["source", "target"][i],
                            end_elem,
                            end_scope,
                        ));
                    }
                }
            }
        }

        for (i, m) in body_members.into_iter().enumerate() {
            self.build_member(m, e, body_scope, i);
        }
        // Flow's narrower library base applies only when it owns ends.
        // Keep lookup heritage aligned with the materialized requirements.
        if crate::metaclass::conforms(self.elements[e].ty, "Flow")
            && self.owned_member_elems(e, true).into_iter().any(|feature| {
                self.elements[feature]
                    .props
                    .get("isEnd")
                    .and_then(|v| v.as_bool())
                    == Some(true)
            })
        {
            let base = if crate::metaclass::conforms(self.elements[e].ty, "FlowUsage") {
                "Flows::flows"
            } else {
                "Transfers::flowTransfers"
            };
            self.scopes[body_scope].implied_bases.push(lib_qn(base));
        }
        e
    }

    fn emit_multiplicity(&mut self, owner: usize, mult: &Multiplicity, scope: usize) {
        self.multiplicities.push((owner, scope, mult.clone()));
        let om = self.new_relationship("OwningMembership", owner, "multiplicity");
        self.set(om, "isImplied", json!(false));
        self.set(om, "visibility", json!("public"));
        let mr = self.new_owned_element("MultiplicityRange", om, "range");
        if let Some(lower) = &mult.lower {
            let m = self.new_relationship("OwningMembership", mr, "lower");
            self.set(m, "isImplied", json!(false));
            self.build_expr(lower, m, scope, "bound");
        }
        let m = self.new_relationship("OwningMembership", mr, "upper");
        self.set(m, "isImplied", json!(false));
        self.build_expr(&mult.upper, m, scope, "bound");
    }

    /// The metaclass of anonymous reference features (connector ends, node
    /// parameters): ReferenceUsage in SysML, plain Feature in KerML.
    /// SysML usages spell defaultless `isVariation` even when synthesized
    /// (XMI property audit; KerML `Feature` has no such property).
    fn set_synth_usage_flags(&mut self, e: usize) {
        if self.elements[e].ty != "Feature" {
            self.set(e, "isVariation", json!(false));
        }
    }

    fn ref_feature_metaclass(&self) -> &'static str {
        match self.dialect {
            Dialect::Sysml => "ReferenceUsage",
            Dialect::Kerml => "Feature",
        }
    }

    /// A succession end the text leaves unspelled: bare reference feature
    /// under an EndFeatureMembership, no subsetting (the pilot's
    /// MultiplicitySourceEnd / EmptySourceEnd / EmptyTargetEnd rules).
    fn empty_connector_end() -> ConnectorEnd {
        ConnectorEnd {
            multiplicity: None,
            name: None,
            target: TargetRef::unspelled(),
        }
    }

    /// One connector end: EndFeatureMembership → reference feature with a
    /// ReferenceSubsetting to the end target. Returns the end feature.
    fn emit_connector_end(
        &mut self,
        parent: usize,
        end: &ConnectorEnd,
        scope: usize,
        i: usize,
    ) -> usize {
        let rel = self.new_relationship("EndFeatureMembership", parent, &format!("end{i}"));
        self.set(rel, "isImplied", json!(false));
        self.set(rel, "visibility", json!("public"));
        // Interface ends are PortUsages (pilot InterfaceEnd rule).
        let end_ty = if matches!(
            self.elements[parent].ty,
            "InterfaceUsage" | "InterfaceDefinition"
        ) {
            "PortUsage"
        } else {
            self.ref_feature_metaclass()
        };
        let ru = self.new_owned_element(end_ty, rel, &format!("end{i}"));
        self.set(ru, "isEnd", json!(true));
        // Connector ends are referential (the pilot's ReferenceUsage
        // constructor); the full form derives isReference from this.
        self.set(ru, "isComposite", json!(false));
        // SysML usages spell defaultless `isVariation` even when
        // synthesized (XMI audit); KerML `Feature` has no such property.
        if end_ty != "Feature" {
            self.set(ru, "isVariation", json!(false));
        }
        if let Some(name) = &end.name {
            self.set(ru, "declaredName", json!(name.value));
        }
        if let Some(mult) = &end.multiplicity {
            // The bound expression is owned inside the connector and can
            // reference members declared in its body. End target lookup
            // keeps the outer scope so it cannot capture the end itself.
            let bound_scope = self.elem_scope.get(&parent).copied().unwrap_or(scope);
            self.emit_multiplicity(ru, mult, bound_scope);
        }
        // Empty targets occur for implicit source ends of successions.
        let is_empty = end.target.is_unspelled();
        if !is_empty {
            let span = match &end.target {
                TargetRef::Name(qn) => qn_span(qn),
                TargetRef::Chain(links) => Span {
                    start: links.first().map_or(0, |l| qn_span(l).start),
                    end: links.last().map_or(0, |l| qn_span(l).end),
                },
            };
            self.connector_ends.push((parent, ru, span));
            let rs = self.new_relationship("ReferenceSubsetting", ru, "refsub");
            self.set(rs, "isImplied", json!(false));
            self.set_ref(rs, "referencedFeature", scope, &end.target);
            let ru_id = self.elements[ru].id;
            self.set(rs, "subsettingFeature", id_ref(ru_id));
        }
        ru
    }

    /// Payload feature of flows/messages/accept actions. Flow payloads own
    /// via FeatureMembership (pilot PayloadFeatureMember); accept payloads
    /// are `inout` parameters (pilot PayloadParameterMember).
    fn emit_payload(
        &mut self,
        parent: usize,
        payload: &PayloadPart,
        scope: usize,
        ty: &'static str,
    ) {
        let (rel_ty, direction) = if ty == "PayloadFeature" {
            ("FeatureMembership", None)
        } else {
            ("ParameterMembership", Some("inout"))
        };
        let rel = self.new_relationship(rel_ty, parent, "payload");
        self.set(rel, "isImplied", json!(false));
        self.set(rel, "visibility", json!("public"));
        let seg = payload
            .id
            .name
            .as_ref()
            .map(|n| n.value.clone())
            .unwrap_or_else(|| "payload".to_string());
        let e = self.new_owned_element(ty, rel, &seg);
        if ty == "ReferenceUsage" {
            self.set(e, "isVariation", json!(false));
        }
        self.set_identification(e, &payload.id);
        // Payload features historically omit these default-valued fields in
        // compact JSON. Emit only explicitly non-default markers so ordinary
        // payloads retain their stable representation.
        if payload.is_ordered {
            self.set(e, "isOrdered", json!(true));
        }
        if payload.is_nonunique {
            self.set(e, "isUnique", json!(false));
        }
        if let Some(dir) = direction {
            self.set(e, "direction", json!(dir));
            self.set(e, "isComposite", json!(false));
        }
        // The payload parameter is referencable from where the accept/flow
        // is written (guards, later members): register it, with its typing
        // as inherited-member bases so `payload.member` chains resolve. It
        // is also an owned feature of the accept/flow element itself, so
        // register it in that element's body scope too (`msg.payload`
        // chains and the round-tripped `msg::payload` spelling).
        let body_scope = self.push_scope(Some(scope));
        self.register(scope, &payload.id.clone(), e, body_scope);
        if let Some(&owner_scope) = self.elem_scope.get(&parent) {
            self.register(owner_scope, &payload.id.clone(), e, body_scope);
        }
        for spec in &payload.specializations {
            if let FeatureSpecialization::TypedBy(types) = spec {
                for t in types {
                    if let TargetRef::Name(qn) = &t.target {
                        self.scopes[body_scope].bases.push(qn.clone());
                    }
                }
            }
        }
        let decl = FeatureDeclaration {
            specializations: payload.specializations.clone(),
            is_ordered: payload.is_ordered,
            is_nonunique: payload.is_nonunique,
            ..Default::default()
        };
        self.emit_specializations(e, &decl, scope);
        if let Some(mult) = &payload.multiplicity {
            self.emit_multiplicity(e, mult, scope);
        }
        if let Some(value) = &payload.value {
            let fv = self.new_relationship("FeatureValue", e, "value");
            self.set(fv, "isImplied", json!(false));
            self.build_expr(&value.expr, fv, scope, "expr");
        }
    }

    /// An expression argument as a parameter member (node parameters of
    /// send/accept/assign/if/while/for nodes).
    fn emit_expr_param(&mut self, parent: usize, seg: &str, expr: &Expr, scope: usize) {
        let pm = self.new_relationship("ParameterMembership", parent, seg);
        self.set(pm, "isImplied", json!(false));
        let ru = self.new_owned_element(self.ref_feature_metaclass(), pm, seg);
        self.contract_exprs.insert(ru, (scope, expr.clone()));
        self.set_synth_usage_flags(ru);
        let fv = self.new_relationship("FeatureValue", ru, "value");
        self.set(fv, "isImplied", json!(false));
        self.build_expr(expr, fv, scope, "expr");
    }

    /// An anonymous nested action usage as a parameter member (if/while/for
    /// bodies, transition effects).
    fn emit_usage_param(&mut self, parent: usize, seg: &str, u: &Usage, scope: usize) {
        let pm = self.new_relationship("ParameterMembership", parent, seg);
        self.set(pm, "isImplied", json!(false));
        let inner_scope = self.push_scope(Some(scope));
        self.build_usage_element_scoped(u, pm, inner_scope, seg, None);
    }

    /// Kind-specific lowering of usage details. Returns the end features of
    /// a `Connector` detail (for implied `source`/`target` registration).
    fn build_usage_detail(&mut self, e: usize, detail: &UsageDetail, scope: usize) -> Vec<usize> {
        match detail {
            UsageDetail::None => {}
            UsageDetail::Connector { ends } => {
                return ends
                    .iter()
                    .enumerate()
                    .map(|(i, end)| self.emit_connector_end(e, end, scope, i))
                    .collect();
            }
            UsageDetail::Binding { ends } => {
                for (i, end) in ends.iter().enumerate() {
                    self.emit_connector_end(e, end, scope, i);
                }
            }
            UsageDetail::Succession { source, target } => {
                // A succession always owns both ends (SysML.xtext
                // SuccessionAsUsage / TargetSuccession): a source the text
                // doesn't spell is a bare source end.
                match source {
                    Some(s) => self.emit_connector_end(e, s, scope, 0),
                    None => self.emit_connector_end(e, &Self::empty_connector_end(), scope, 0),
                };
                self.emit_connector_end(e, target, scope, 1);
            }
            UsageDetail::Flow {
                payload,
                source,
                target,
            } => {
                if let Some(p) = payload {
                    self.emit_payload(e, p, scope, "PayloadFeature");
                }
                for (i, end) in [source, target].into_iter().flatten().enumerate() {
                    let rel =
                        self.new_relationship("EndFeatureMembership", e, &format!("flowend{i}"));
                    self.set(rel, "isImplied", json!(false));
                    let fe = self.new_owned_element("FlowEnd", rel, &format!("end{i}"));
                    self.set(fe, "isEnd", json!(true));
                    // Pilot FlowEnd rule: a ReferenceSubsetting of the chain
                    // *prefix* (`tank` of `tank.fuelOut`, only when spelled)
                    // plus an owned ReferenceUsage whose FlowRedefinition
                    // targets the last step, resolved in the prefix's scope.
                    let (prefix, last) = match &end.target {
                        TargetRef::Chain(links) if links.len() >= 2 => (
                            Some(links[..links.len() - 1].to_vec()),
                            links[links.len() - 1].clone(),
                        ),
                        TargetRef::Chain(links) if links.len() == 1 => (None, links[0].clone()),
                        TargetRef::Name(qn) => (None, qn.clone()),
                        TargetRef::Chain(_) => continue,
                    };
                    if let Some(prefix) = &prefix {
                        let rs = self.new_relationship("ReferenceSubsetting", fe, "refsub");
                        self.set(rs, "isImplied", json!(false));
                        let prefix_target = if prefix.len() == 1 {
                            TargetRef::Name(prefix[0].clone())
                        } else {
                            TargetRef::Chain(prefix.clone())
                        };
                        self.set_ref(rs, "referencedFeature", scope, &prefix_target);
                        let fe_id = self.elements[fe].id;
                        self.set(rs, "subsettingFeature", id_ref(fe_id));
                    }
                    let fm = self.new_relationship("FeatureMembership", fe, "flowfeature");
                    self.set(fm, "isImplied", json!(false));
                    let ru = self.new_owned_element("ReferenceUsage", fm, "flowfeature");
                    // The flow feature is the source's output / the target's
                    // input (pilot sourceOutputFeature/targetInputFeature),
                    // referential like every ReferenceUsage.
                    self.set(ru, "direction", json!(if i == 0 { "out" } else { "in" }));
                    self.set(ru, "isComposite", json!(false));
                    self.set(ru, "isVariation", json!(false));
                    let rd = self.new_relationship("Redefinition", ru, "redef");
                    self.set(rd, "isImplied", json!(false));
                    let ru_id = self.elements[ru].id;
                    self.set(rd, "redefiningFeature", id_ref(ru_id));
                    self.pending.push(PendingRef {
                        elem: rd,
                        key: "redefinedFeature".to_string(),
                        scope,
                        qn: last,
                        exclude: None,
                        declared_only: false,
                        spec_idx: None,
                        chain: prefix,
                    });
                }
            }
            UsageDetail::Metadata { about } => {
                for (i, target) in about.iter().enumerate() {
                    let ann = self.new_relationship("Annotation", e, &format!("about{i}"));
                    self.explicit_metadata_annotations.push(ann);
                    self.set(ann, "isImplied", json!(false));
                    self.set_ref(
                        ann,
                        "annotatedElement",
                        scope,
                        &TargetRef::Name(target.clone()),
                    );
                }
            }
            UsageDetail::Satisfy {
                asserted: _,
                negated,
                by,
            } => {
                self.set(e, "isNegated", json!(*negated));
                if let Some(by) = by {
                    self.satisfy_by.push((e, scope, by.clone()));
                    let rel = self.new_relationship("SubjectMembership", e, "by");
                    self.set(rel, "isImplied", json!(false));
                    let ru = self.new_owned_element("ReferenceUsage", rel, "satisfactionSubject");
                    self.set(ru, "isVariation", json!(false));
                    // Pilot SatisfactionFeatureValue: the `by` target binds
                    // as a FeatureValue whose FeatureReferenceExpression
                    // owns a FeatureChainMember (`set_ref` retypes it to an
                    // OwningMembership when the target is an owned chain).
                    let fv = self.new_relationship("FeatureValue", ru, "value");
                    self.set(fv, "isImplied", json!(false));
                    let fre = self.new_owned_element("FeatureReferenceExpression", fv, "expr");
                    let m = self.new_relationship("Membership", fre, "ref");
                    self.set(m, "isImplied", json!(false));
                    self.set_ref(m, "memberElement", scope, by);
                }
            }
            UsageDetail::Assert { negated } => {
                self.set(e, "isNegated", json!(*negated));
            }
            UsageDetail::Accept {
                payload,
                trigger,
                via,
            } => {
                self.emit_payload(e, payload, scope, "ReferenceUsage");
                if let Some(t) = trigger {
                    let kind = match t.kind {
                        TriggerKind::At => "at",
                        TriggerKind::After => "after",
                        TriggerKind::When => "when",
                    };
                    let pm = self.new_relationship("ParameterMembership", e, "trigger");
                    self.set(pm, "isImplied", json!(false));
                    let te = self.new_owned_element("TriggerInvocationExpression", pm, "trigger");
                    self.contract_exprs.insert(te, (scope, t.expr.clone()));
                    self.set(te, "kind", json!(kind));
                    let am = self.new_relationship("ParameterMembership", te, "arg");
                    self.set(am, "isImplied", json!(false));
                    self.build_expr(&t.expr, am, scope, "expr");
                }
                if let Some(via) = via {
                    // The `via` target is the accept's `receiver` parameter
                    // (pilot NodeParameterMember — an `in` parameter whose
                    // value is the receiver expression).
                    let pm = self.new_relationship("ParameterMembership", e, "via");
                    self.set(pm, "isImplied", json!(false));
                    let ru = self.new_owned_element(self.ref_feature_metaclass(), pm, "via");
                    self.set_synth_usage_flags(ru);
                    self.set(ru, "direction", json!("in"));
                    self.set(ru, "isComposite", json!(false));
                    let fv = self.new_relationship("FeatureValue", ru, "value");
                    self.set(fv, "isImplied", json!(false));
                    self.build_expr(via, fv, scope, "expr");
                }
            }
            UsageDetail::Send { payload, via, to } => {
                // Positional parameter slots (payload, sender, receiver) —
                // empty slots get an empty parameter, per the grammar's
                // EmptyParameterMember, so the roles stay distinguishable.
                for (seg, slot) in [("payload", payload), ("via", via), ("receiver", to)] {
                    match slot {
                        Some(expr) => self.emit_expr_param(e, seg, expr, scope),
                        None => {
                            let pm = self.new_relationship("ParameterMembership", e, seg);
                            self.set(pm, "isImplied", json!(false));
                            let ru = self.new_owned_element(self.ref_feature_metaclass(), pm, seg);
                            self.set_synth_usage_flags(ru);
                        }
                    }
                }
            }
            UsageDetail::Assign { target, value } => {
                self.emit_expr_param(e, "target", target, scope);
                self.emit_expr_param(e, "value", value, scope);
            }
            UsageDetail::Terminate { target } => {
                if let Some(t) = target {
                    self.emit_expr_param(e, "terminatedOccurrence", t, scope);
                }
            }
            UsageDetail::IfNode {
                cond,
                then_body,
                else_body,
            } => {
                self.emit_expr_param(e, "condition", cond, scope);
                self.emit_usage_param(e, "then", then_body, scope);
                if let Some(else_body) = else_body {
                    self.emit_usage_param(e, "else", else_body, scope);
                }
            }
            UsageDetail::WhileLoop { cond, body, until } => {
                if let Some(c) = cond {
                    self.emit_expr_param(e, "condition", c, scope);
                }
                self.emit_usage_param(e, "body", body, scope);
                if let Some(u) = until {
                    self.emit_expr_param(e, "until", u, scope);
                }
            }
            UsageDetail::ForLoop { var, seq, body } => {
                let fm = self.new_relationship("FeatureMembership", e, "loopVariable");
                self.set(fm, "isImplied", json!(false));
                let seg = var
                    .id
                    .name
                    .as_ref()
                    .map(|n| n.value.clone())
                    .unwrap_or_else(|| "var".to_string());
                let ve = self.new_owned_element("ReferenceUsage", fm, &seg);
                self.set(ve, "isVariation", json!(false));
                self.set_identification(ve, &var.id);
                self.emit_specializations(ve, var, scope);
                self.emit_expr_param(e, "seq", seq, scope);
                self.emit_usage_param(e, "body", body, scope);
            }
            UsageDetail::Transition {
                source,
                trigger,
                guard,
                effect,
                target,
                is_default: _,
            } => {
                if let Some(source) = source {
                    let m = self.new_relationship("Membership", e, "source");
                    self.set(m, "isImplied", json!(false));
                    self.set_ref(m, "memberElement", scope, source);
                }
                // Trigger payload parameters (`accept pub : Publish`) are
                // referencable from the guard and effect: give the
                // transition its own scope for those parts.
                let t_scope = self.push_scope(Some(scope));
                if let Some(trigger) = trigger {
                    // The grammar's second EmptyParameterMember: a triggered
                    // transition also owns its payload as an `in` parameter,
                    // declared with the trigger payload's name (lift
                    // reconstructs it from the trigger, so it is dropped
                    // there and re-derived here).
                    if let UsageDetail::Accept { payload, .. } = trigger.as_ref() {
                        let pm = self.new_relationship("ParameterMembership", e, "payloadparam");
                        self.set(pm, "isImplied", json!(false));
                        let ru = self.new_owned_element("ReferenceUsage", pm, "payloadparam");
                        self.set(ru, "isVariation", json!(false));
                        self.set_identification(ru, &payload.id);
                        self.set(ru, "direction", json!("in"));
                        self.set(ru, "isComposite", json!(false));
                        // The parameter is a feature of the transition
                        // itself: chains rooted at the transition
                        // (`T.s.x`) resolve through it, with the trigger
                        // payload's typing as inherited-member bases.
                        // Resolution only — nothing new serializes (the
                        // lift re-derives this element from the trigger).
                        if let Some(&ebody) = self.elem_scope.get(&e) {
                            let ru_scope = self.push_scope(Some(scope));
                            for spec in &payload.specializations {
                                if let FeatureSpecialization::TypedBy(types) = spec {
                                    for t in types {
                                        if let TargetRef::Name(qn) = &t.target {
                                            self.scopes[ru_scope].bases.push(qn.clone());
                                        }
                                    }
                                }
                            }
                            self.register(ebody, &payload.id.clone(), ru, ru_scope);
                        }
                    }
                    let tm = self.new_relationship("TransitionFeatureMembership", e, "trigger");
                    self.set(tm, "isImplied", json!(false));
                    self.set(tm, "kind", json!("trigger"));
                    let ae = self.new_owned_element("AcceptActionUsage", tm, "trigger");
                    self.set(ae, "isComposite", json!(true));
                    self.set(ae, "isVariation", json!(false));
                    self.build_usage_detail(ae, trigger, t_scope);
                }
                if let Some(guard) = guard {
                    let gm = self.new_relationship("TransitionFeatureMembership", e, "guard");
                    self.set(gm, "isImplied", json!(false));
                    self.set(gm, "kind", json!("guard"));
                    self.build_expr(guard, gm, t_scope, "expr");
                    self.transition_guards
                        .insert(e, (t_scope, (**guard).clone()));
                }
                if let Some(effect) = effect {
                    let em = self.new_relationship("TransitionFeatureMembership", e, "effect");
                    self.set(em, "isImplied", json!(false));
                    self.set(em, "kind", json!("effect"));
                    let inner_scope = self.push_scope(Some(t_scope));
                    self.build_usage_element_scoped(effect, em, inner_scope, "effect", None);
                }
                if let Some(target) = target {
                    let sm = self.new_relationship("OwningMembership", e, "succession");
                    self.set(sm, "isImplied", json!(false));
                    self.set(sm, "visibility", json!("public"));
                    let succ = self.new_owned_element("SuccessionAsUsage", sm, "succession");
                    self.set(succ, "isComposite", json!(false));
                    self.set(succ, "isVariation", json!(false));
                    // TransitionSuccession = EmptySourceEndMember + target.
                    self.emit_connector_end(succ, &Self::empty_connector_end(), scope, 0);
                    self.emit_connector_end(succ, target, scope, 1);
                }
            }
        }
        Vec::new()
    }

    /// Like `build_usage_element` but with an explicit pre-created scope
    /// (for anonymous nested usages).
    fn build_usage_element_scoped(
        &mut self,
        u: &Usage,
        rel: usize,
        scope: usize,
        seg: &str,
        class_override: Option<&'static str>,
    ) -> usize {
        // Anonymous nested usages are always FeatureMembership-family
        // owned (parameters, loop bodies, effects) — featured.
        self.pending_featuring = true;
        self.pending_direction = None;
        self.pending_owner_ty = None;
        self.build_usage_element(u, rel, scope, seg, class_override)
    }

    // ---- expressions ----

    /// Build the abstract-syntax element tree for `expr`, owned via
    /// relationship `rel`. Returns the expression element index.
    fn build_expr(&mut self, expr: &Expr, rel: usize, scope: usize, seg: &str) -> usize {
        /// The wire value of a real literal. A JSON number is a double,
        /// which holds neither more significant digits than its
        /// precision nor an exponent that overflows it — and in-memory
        /// evaluation reads the literal exactly, so a rounded number on
        /// the wire would make the two disagree. The number therefore
        /// travels only when printing and re-reading it yields exactly
        /// the written value; otherwise the literal's own text does,
        /// the way an integer beyond 64 bits already travels as text.
        fn real_literal_value(raw: &str) -> Value {
            use crate::rational::Rational;
            let Some(number) = raw
                .parse::<f64>()
                .ok()
                .and_then(serde_json::Number::from_f64)
            else {
                return json!(raw);
            };
            match (
                Rational::parse_decimal(raw),
                Rational::parse_decimal(&number.to_string()),
            ) {
                (Some(written), Some(printed)) if written == printed => Value::Number(number),
                _ => json!(raw),
            }
        }
        match &expr.kind {
            ExprKind::Literal(lit) => {
                let (ty, value) = match lit {
                    Literal::Bool(b) => ("LiteralBoolean", json!(b)),
                    Literal::String(s) => ("LiteralString", json!(s)),
                    Literal::Integer(n) => (
                        "LiteralInteger",
                        n.parse::<i64>()
                            .map(|v| json!(v))
                            .unwrap_or_else(|_| json!(n)),
                    ),
                    Literal::Real(r) => ("LiteralRational", real_literal_value(r)),
                    Literal::Infinity => ("LiteralInfinity", Value::Null),
                };
                let e = self.new_owned_element(ty, rel, seg);
                if !matches!(lit, Literal::Infinity) {
                    self.set(e, "value", value);
                }
                e
            }
            ExprKind::Null => self.new_owned_element("NullExpression", rel, seg),
            ExprKind::Ref(qn) => {
                let e = self.new_owned_element("FeatureReferenceExpression", rel, seg);
                let m = self.new_relationship("Membership", e, "ref");
                self.set(m, "isImplied", json!(false));
                self.set_ref(m, "memberElement", scope, &TargetRef::Name(qn.clone()));
                e
            }
            ExprKind::Conditional {
                cond,
                then_branch,
                else_branch,
            } => {
                let e = self.operator_expr(rel, seg, "if");
                self.operand(e, cond, scope, 0);
                self.conditional_operand(e, then_branch, scope, 1);
                self.conditional_operand(e, else_branch, scope, 2);
                e
            }
            ExprKind::Binary { op, lhs, rhs } => {
                let e = self.operator_expr(rel, seg, binary_op_str(*op));
                self.operand(e, lhs, scope, 0);
                if matches!(
                    op,
                    BinaryOp::NullCoalescing
                        | BinaryOp::Implies
                        | BinaryOp::CondOr
                        | BinaryOp::CondAnd
                ) {
                    self.conditional_operand(e, rhs, scope, 1);
                } else {
                    self.operand(e, rhs, scope, 1);
                }
                e
            }
            ExprKind::Unary { op, operand } => {
                let name = match op {
                    UnaryOp::Plus => "+",
                    UnaryOp::Minus => "-",
                    UnaryOp::Tilde => "~",
                    UnaryOp::Not => "not",
                };
                let e = self.operator_expr(rel, seg, name);
                self.operand(e, operand, scope, 0);
                e
            }
            ExprKind::Classification { op, operand, ty } => {
                let name = match op {
                    ClassificationOp::IsType => "istype",
                    ClassificationOp::HasType => "hastype",
                    ClassificationOp::AtType => "@",
                    ClassificationOp::MetaAtType => "@@",
                    ClassificationOp::As => "as",
                    ClassificationOp::Meta => "meta",
                };
                let e = self.operator_expr(rel, seg, name);
                match operand {
                    // `x meta T` / `x @@ T`: the left side is a metadata
                    // reference (pilot `MetadataReference` returns
                    // MetadataAccessExpression), when it is a plain name.
                    Some(operand)
                        if matches!(op, ClassificationOp::Meta | ClassificationOp::MetaAtType)
                            && expr_target_name(operand).is_some() =>
                    {
                        let qn = expr_target_name(operand).unwrap();
                        let m = self.new_relationship("ParameterMembership", e, "operand0");
                        self.set(m, "isImplied", json!(false));
                        self.set(m, "visibility", json!("private"));
                        let f = self.new_owned_element("Feature", m, "param");
                        self.set(f, "direction", json!("in"));
                        let fv = self.new_relationship("FeatureValue", f, "value");
                        self.set(fv, "isImplied", json!(false));
                        let mae = self.new_owned_element("MetadataAccessExpression", fv, "expr");
                        let em = self.new_relationship("Membership", mae, "element");
                        self.set(em, "isImplied", json!(false));
                        self.set_ref(em, "memberElement", scope, &TargetRef::Name(qn));
                    }
                    Some(operand) => self.operand(e, operand, scope, 0),
                    // Implicit-subject spelling (`istype T` in a filter):
                    // pilot `SelfReferenceExpression` — a feature-reference
                    // expression whose referent is an owned empty feature.
                    None => {
                        let m = self.new_relationship("ParameterMembership", e, "operand0");
                        self.set(m, "isImplied", json!(false));
                        self.set(m, "visibility", json!("private"));
                        let f = self.new_owned_element("Feature", m, "param");
                        self.set(f, "direction", json!("in"));
                        let fv = self.new_relationship("FeatureValue", f, "value");
                        self.set(fv, "isImplied", json!(false));
                        let fre = self.new_owned_element("FeatureReferenceExpression", fv, "expr");
                        let sm = self.new_relationship("ReturnParameterMembership", fre, "self");
                        self.set(sm, "isImplied", json!(false));
                        self.new_owned_element("Feature", sm, "selfref");
                    }
                }
                // The type reference: an owned parameter Feature typed by
                // the target (pilot `TypeReferenceMember`/`TypeResultMember`;
                // casts use the return parameter).
                let m_ty = if matches!(op, ClassificationOp::As | ClassificationOp::Meta) {
                    "ReturnParameterMembership"
                } else {
                    "ParameterMembership"
                };
                let m = self.new_relationship(m_ty, e, "type");
                self.set(m, "isImplied", json!(false));
                let f = self.new_owned_element("Feature", m, "typeref");
                self.set(
                    f,
                    "direction",
                    json!(if m_ty == "ParameterMembership" {
                        "in"
                    } else {
                        "out"
                    }),
                );
                let ft = self.new_relationship("FeatureTyping", f, "typing");
                self.set(ft, "isImplied", json!(false));
                self.set_ref(ft, "type", scope, ty);
                let f_id = self.elements[f].id;
                self.set(ft, "typedFeature", id_ref(f_id));
                e
            }
            ExprKind::Extent { ty } => {
                let e = self.operator_expr(rel, seg, "all");
                let m = self.new_relationship("ReturnParameterMembership", e, "type");
                self.set(m, "isImplied", json!(false));
                let f = self.new_owned_element("Feature", m, "typeref");
                self.set(f, "direction", json!("out"));
                let ft = self.new_relationship("FeatureTyping", f, "typing");
                self.set(ft, "isImplied", json!(false));
                self.set_ref(ft, "type", scope, ty);
                let f_id = self.elements[f].id;
                self.set(ft, "typedFeature", id_ref(f_id));
                e
            }
            ExprKind::ChainStep { target, member } => {
                // Grammar (KerMLExpressions `PrimaryExpression`): everything
                // after the FIRST `.` is ONE `FeatureChainMember` — a
                // multi-step chain serializes as a single
                // FeatureChainExpression whose member is an
                // `OwnedFeatureChain`, never nested chain expressions
                // (pilot shape; parsing nests, lowering flattens).
                let foldable = |t: &TargetRef| matches!(t, TargetRef::Name(_));
                let mut rev_links: Vec<&TargetRef> = vec![member];
                let mut base: &Expr = target;
                if foldable(member) {
                    while let ExprKind::ChainStep {
                        target: t2,
                        member: m2,
                    } = &base.kind
                    {
                        if !foldable(m2) {
                            break;
                        }
                        rev_links.push(m2);
                        base = t2;
                    }
                }
                if rev_links.len() > 1 {
                    let links: Vec<QualifiedName> = rev_links
                        .into_iter()
                        .rev()
                        .map(|t| match t {
                            TargetRef::Name(q) => q.clone(),
                            TargetRef::Chain(_) => unreachable!("foldable is Name-only"),
                        })
                        .collect();
                    let e = self.new_owned_element("FeatureChainExpression", rel, seg);
                    self.set(e, "operator", json!("."));
                    self.operand(e, base, scope, 0);
                    let m = self.new_relationship("OwningMembership", e, "member");
                    self.set(m, "isImplied", json!(false));
                    let base_spine = chain_spine(base);
                    let feature = self.new_owned_element("Feature", m, "memberElement.chain");
                    for (i, link) in links.iter().enumerate() {
                        let fc = self.new_relationship(
                            "FeatureChaining",
                            feature,
                            &format!("chaining{i}"),
                        );
                        self.set(fc, "isImplied", json!(false));
                        // Each link resolves in its predecessor's scope; the
                        // first link's predecessor is the base expression's
                        // static spine (when it has one). Same contexts the
                        // nested form used, so resolution outcomes agree.
                        // A `$::`-rooted link (the round-tripped spelling
                        // of a resolved step) resolves absolutely with no
                        // self-exclusion, exactly like the single-member
                        // form — both directions must land on the same
                        // element or the round-trip gate trips.
                        let (exclude, declared_only, chain) = if link.is_global {
                            (None, false, None)
                        } else {
                            // Context = base spine + preceding links,
                            // anchored at the last `$::`-rooted link when
                            // one exists (an absolute link resolves on its
                            // own and the relative tail hangs off it — the
                            // lifted spelling of a resolved chain).
                            let mut c: Vec<QualifiedName> = base_spine.clone().unwrap_or_default();
                            c.extend_from_slice(&links[..i]);
                            if let Some(g) = c.iter().rposition(|q| q.is_global) {
                                c.drain(..g);
                            }
                            let chain = if c.is_empty() { None } else { Some(c) };
                            (self.pending_exclude, true, chain)
                        };
                        self.pending.push(PendingRef {
                            elem: fc,
                            key: "chainingFeature".to_string(),
                            scope,
                            qn: link.clone(),
                            exclude,
                            declared_only,
                            spec_idx: None,
                            chain,
                        });
                    }
                    let feature_id = self.elements[feature].id;
                    self.set(m, "memberElement", id_ref(feature_id));
                    return e;
                }
                let e = self.new_owned_element("FeatureChainExpression", rel, seg);
                // Metaclass-fixed operator (pilot `FeatureChainExpressionImpl`).
                self.set(e, "operator", json!("."));
                self.operand(e, target, scope, 0);
                let m = self.new_relationship("Membership", e, "member");
                self.set(m, "isImplied", json!(false));
                // The step names a member of the chain target: resolve it in
                // the spine target's scope when the spine is statically a
                // name chain; never let effective names of local unnamed
                // features capture it lexically.
                match member {
                    TargetRef::Name(qn) if !qn.is_global => {
                        self.pending.push(PendingRef {
                            elem: m,
                            key: "memberElement".to_string(),
                            scope,
                            qn: qn.clone(),
                            exclude: self.pending_exclude,
                            declared_only: true,
                            chain: chain_spine(target),
                            spec_idx: None,
                        });
                    }
                    // Absolute (`$::`-rooted) members — the round-tripped
                    // spelling of a resolved step — carry no lexical-capture
                    // risk: resolve them normally (no self-exclusion — the
                    // original chain-context resolution may legitimately
                    // have landed on the defining feature) so both
                    // directions land on the same element.
                    TargetRef::Name(qn) => {
                        self.pending.push(PendingRef {
                            elem: m,
                            key: "memberElement".to_string(),
                            scope,
                            qn: qn.clone(),
                            exclude: None,
                            declared_only: false,
                            chain: None,
                            spec_idx: None,
                        });
                    }
                    TargetRef::Chain(_) => {
                        self.set_ref(m, "memberElement", scope, member);
                    }
                }
                e
            }
            ExprKind::Index { target, index } => {
                let e = self.new_owned_element("IndexExpression", rel, seg);
                self.set(e, "operator", json!("#"));
                self.operand(e, target, scope, 0);
                self.operand(e, index, scope, 1);
                e
            }
            ExprKind::Bracket { target, arg } => {
                let e = self.operator_expr(rel, seg, "[");
                self.operand(e, target, scope, 0);
                self.operand(e, arg, scope, 1);
                e
            }
            ExprKind::Arrow { target, ty, args } => {
                // Arrow invocations lower identically to plain invocations
                // with the target as the first argument (the JSON reader
                // canonicalizes the sugar away, so the shapes — and thus the
                // deterministic IDs — must agree).
                let e = self.new_owned_element("InvocationExpression", rel, seg);
                let m = self.new_relationship("Membership", e, "fn");
                self.set(m, "isImplied", json!(false));
                self.set_ref(m, "memberElement", scope, ty);
                match args {
                    ArrowArgs::Body(body) => {
                        self.arg_expr(e, target, scope, 0);
                        self.arg_expr(e, body, scope, 1);
                    }
                    ArrowArgs::FunctionRef(f) => {
                        self.arg_expr(e, target, scope, 0);
                        let fm = self.new_relationship("FeatureMembership", e, "fnref");
                        self.set(fm, "isImplied", json!(false));
                        self.set_ref(fm, "memberElement", scope, &TargetRef::Name(f.clone()));
                    }
                    ArrowArgs::List(list) => {
                        self.arg_expr(e, target, scope, 0);
                        for (i, a) in list.iter().enumerate() {
                            self.argument(e, a, scope, i + 1, ty);
                        }
                    }
                }
                e
            }
            ExprKind::Collect { target, body } => {
                let e = self.new_owned_element("CollectExpression", rel, seg);
                self.set(e, "operator", json!("collect"));
                self.operand(e, target, scope, 0);
                self.operand(e, body, scope, 1);
                e
            }
            ExprKind::Select { target, body } => {
                let e = self.new_owned_element("SelectExpression", rel, seg);
                self.set(e, "operator", json!("select"));
                self.operand(e, target, scope, 0);
                self.operand(e, body, scope, 1);
                e
            }
            ExprKind::Invocation { ty, args } => {
                let e = self.new_owned_element("InvocationExpression", rel, seg);
                let m = self.new_relationship("Membership", e, "fn");
                self.set(m, "isImplied", json!(false));
                self.set_ref(m, "memberElement", scope, ty);
                for (i, a) in args.iter().enumerate() {
                    self.argument(e, a, scope, i, ty);
                }
                e
            }
            ExprKind::Constructor { ty, args } => {
                let e = self.new_owned_element("ConstructorExpression", rel, seg);
                let m = self.new_relationship("Membership", e, "type");
                self.set(m, "isImplied", json!(false));
                self.set_ref(m, "memberElement", scope, ty);
                let argument_owner = if self.graph_format == crate::model::GraphFormat::CanonicalV3
                {
                    let member = self.new_relationship("ReturnParameterMembership", e, "result");
                    self.set(member, "isImplied", json!(false));
                    let result = self.new_owned_element("Feature", member, "result");
                    self.set(result, "direction", json!("out"));
                    result
                } else {
                    e
                };
                for (i, a) in args.iter().enumerate() {
                    self.argument(argument_owner, a, scope, i, ty);
                }
                e
            }
            ExprKind::Body { members } => {
                // Expression body: an Expression whose members include the
                // `in` parameters and the trailing result expression.
                let e = self.new_owned_element("Expression", rel, seg);
                let body_scope = self.push_scope(Some(scope));
                for (i, m) in members.iter().enumerate() {
                    self.build_member(m, e, body_scope, i);
                }
                e
            }
            ExprKind::Sequence(items) => {
                // Comma sequences are right-nested OperatorExpressions
                // (operator ",").
                let e = self.operator_expr(rel, seg, ",");
                for (i, item) in items.iter().enumerate() {
                    self.operand(e, item, scope, i);
                }
                e
            }
            ExprKind::MetadataAccess { target } => {
                let e = self.new_owned_element("MetadataAccessExpression", rel, seg);
                let m = self.new_relationship("Membership", e, "element");
                self.set(m, "isImplied", json!(false));
                self.set_ref(m, "memberElement", scope, &TargetRef::Name(target.clone()));
                e
            }
        }
    }

    fn operator_expr(&mut self, rel: usize, seg: &str, operator: &str) -> usize {
        let e = self.new_owned_element("OperatorExpression", rel, seg);
        self.set(e, "operator", json!(operator));
        e
    }

    /// Wrap an operand/argument expression the way the pilot
    /// implementation does (`TypeUtil.addOwnedParameterTo`, KerML.xtext
    /// `ArgumentMember`): the ParameterMembership owns an unnamed `in`
    /// parameter Feature whose FeatureValue owns the actual expression.
    /// Operator-expression operands additionally get private visibility
    /// (pilot `OperandEList`); explicit argument lists keep the default.
    fn param_wrapped_expr(&mut self, membership: usize, expr: &Expr, scope: usize, private: bool) {
        if private {
            self.set(membership, "visibility", json!("private"));
        }
        let f = self.new_owned_element("Feature", membership, "param");
        self.set(f, "direction", json!("in"));
        let fv = self.new_relationship("FeatureValue", f, "value");
        self.set(fv, "isImplied", json!(false));
        self.build_expr(expr, fv, scope, "expr");
    }

    fn operand(&mut self, parent: usize, operand: &Expr, scope: usize, i: usize) {
        let m = self.new_relationship("ParameterMembership", parent, &format!("operand{i}"));
        self.set(m, "isImplied", json!(false));
        self.param_wrapped_expr(m, operand, scope, true);
    }

    fn conditional_operand(&mut self, parent: usize, expr: &Expr, scope: usize, i: usize) {
        if self.graph_format == crate::model::GraphFormat::LegacyV2 {
            self.operand(parent, expr, scope, i);
            return;
        }
        let m = self.new_relationship("ParameterMembership", parent, &format!("operand{i}"));
        self.set(m, "isImplied", json!(false));
        self.set(m, "visibility", json!("private"));
        let f = self.new_owned_element("Feature", m, "param");
        self.set(f, "direction", json!("in"));
        let fv = self.new_relationship("FeatureValue", f, "value");
        self.set(fv, "isImplied", json!(false));
        let reference = self.new_owned_element("FeatureReferenceExpression", fv, "expr");
        let member = self.new_relationship("FeatureMembership", reference, "expression");
        self.set(member, "isImplied", json!(false));
        self.build_expr(expr, member, scope, "expr");
    }

    /// A positional argument expression (same shape/segments as
    /// [`Self::argument`] without a name).
    fn arg_expr(&mut self, parent: usize, expr: &Expr, scope: usize, i: usize) {
        let m = self.new_relationship("ParameterMembership", parent, &format!("arg{i}"));
        self.set(m, "isImplied", json!(false));
        self.param_wrapped_expr(m, expr, scope, false);
    }

    fn argument(&mut self, parent: usize, arg: &Arg, scope: usize, i: usize, callee: &TargetRef) {
        let m = self.new_relationship("ParameterMembership", parent, &format!("arg{i}"));
        self.set(m, "isImplied", json!(false));
        if let Some(name) = &arg.name {
            // Pilot NamedArgument: the argument Feature owns a
            // ParameterRedefinition of the callee's parameter (which also
            // names the feature) — resolved in the callee's scope, like a
            // chain member.
            let f = self.new_owned_element("Feature", m, "param");
            self.set(f, "direction", json!("in"));
            let rd = self.new_relationship("Redefinition", f, "redef");
            self.set(rd, "isImplied", json!(false));
            let f_id = self.elements[f].id;
            self.set(rd, "redefiningFeature", id_ref(f_id));
            let chain = match callee {
                TargetRef::Name(qn) => Some(vec![qn.clone()]),
                TargetRef::Chain(links) if !links.is_empty() => Some(links.clone()),
                TargetRef::Chain(_) => None,
            };
            // The stored relationship already identifies this specialization.
            // Record its callee-context pending outcome in the same identity
            // index as declaration-written redefinitions; never rediscover its
            // bare parameter name in the lexical scope later.
            let spec_idx = self.spec_targets.len();
            self.spec_targets
                .push((f, "Redefinition", scope, name.clone()));
            self.pending.push(PendingRef {
                elem: rd,
                key: "redefinedFeature".to_string(),
                scope,
                qn: name.clone(),
                exclude: None,
                declared_only: false,
                spec_idx: Some(spec_idx),
                chain,
            });
            let fv = self.new_relationship("FeatureValue", f, "value");
            self.set(fv, "isImplied", json!(false));
            self.build_expr(&arg.value, fv, scope, "expr");
        } else {
            self.param_wrapped_expr(m, &arg.value, scope, false);
        }
    }

    // ---- name resolution ----

    fn resolve_pending(&mut self) {
        self.recorded_lookup_ready = false;
        self.recorded_lookup_graph = None;
        self.recorded_lookup_candidate = recorded_lookup::Graph::needed(self);
        if !self.recorded_lookup_candidate && self.explicit_metadata_annotations.is_empty() {
            self.seed = None;
            self.resolve_pending_pass();
            return;
        }
        let pending = self.pending.clone();
        let side = SideState::capture(self);
        // The bootstrap pass consumes the recorded library outcomes; keep a
        // recorded fixed point for replaying the library again below.
        let library_replay: Option<LibraryReplay> = self
            .lib_hints
            .as_ref()
            .zip(self.replay_completions.as_ref())
            .filter(|_| self.lib_hints_fixed_point)
            .map(|(hints, completions)| (hints.as_slice().to_vec(), completions.clone()));
        // Kept outcomes stand in for the bootstrap pass: the loop starts
        // against the graph of theirs, confirms them in one pass when the
        // units resolve as they did, and starts over cold when it does not
        // settle (see `settled`). A build replaying a library recording
        // resolves cold: the replay belongs to the bootstrap pass.
        if let Some(seed) = self.seed.take().filter(|_| self.lib_hints.is_none()) {
            let cold = recorded_lookup::Checkpoint::capture(self, &pending);
            self.apply_seed(&pending, &seed);
            self.refresh_metadata_associations();
            self.recorded_lookup_ready = self.recorded_lookup_candidate;
            let graph = recorded_lookup::Graph::build(self);
            self.note_root_imports_absent(&graph);
            let seeded = recorded_lookup::Checkpoint::capture(self, &pending);
            let previous = self.pass_outcomes(&pending);
            let passes = settled::seeded_passes();
            if self.resolve_pending_redo(
                &pending, &side, &seeded, graph, previous, None, false, passes,
            ) {
                return;
            }
            settled::note_seed_abandoned();
            cold.restore(self);
            self.pending = pending.clone();
            self.recorded_lookup_ready = false;
            self.recorded_lookup_graph = None;
        }
        self.resolve_pending_pass();
        let library_replayed = self.lib_replayed_all;
        let metadata_changed = self.refresh_metadata_associations();
        if self.recorded_lookup_incomplete {
            if !self.explicit_metadata_annotations.is_empty() {
                self.discard_unstable_metadata_associations();
            }
            return;
        }
        self.recorded_lookup_ready = self.recorded_lookup_candidate;
        let mut graph = recorded_lookup::Graph::build(self);
        self.note_root_imports_absent(&graph);
        if pending.is_empty() || (!graph.has_replay_context() && !metadata_changed) {
            self.recorded_lookup_graph = Some(graph);
            return;
        }
        // Each pass reads one complete snapshot. Never feed partially updated
        // endpoints back into inherited selection in the same pass.
        let bootstrap = recorded_lookup::Checkpoint::capture(self, &pending);
        let previous = self.pass_outcomes(&pending);
        if self.resolve_pending_redo(
            &pending,
            &side,
            &bootstrap,
            graph,
            previous,
            library_replay.as_ref(),
            library_replayed,
            REDO_PASSES,
        ) {
            return;
        }
        // Selection is non-monotone: circular references can oscillate.
        // Restore all bootstrap outputs together, never the last partial pass.
        bootstrap.restore(self);
        if !self.explicit_metadata_annotations.is_empty() {
            self.discard_unstable_metadata_associations();
        }
        self.recorded_lookup_ready = false;
        self.recorded_lookup_graph = None;
        self.recorded_lookup_incomplete = true;
    }

    /// A pass's outcomes for `pending`: the value of each reference and
    /// the specialization outcomes.
    fn pass_outcomes(&self, pending: &[PendingRef]) -> PassOutcomes {
        let values = pending
            .iter()
            .map(|p| {
                let key = p.key.split_once('#').map_or(p.key.as_str(), |(key, _)| key);
                self.elements[p.elem].props.get(key).cloned()
            })
            .collect();
        (values, self.spec_resolved.iter().copied().collect())
    }

    /// The redo passes, each against the lookup graph of the previous
    /// pass's outcomes (`graph`, built from `previous`), from the state
    /// `checkpoint` holds, until a pass changes no outcome: the graph it
    /// read is settled and kept, and the outcomes recorded. `false` when
    /// `passes` ran out, the builder holding the last pass's state.
    #[allow(clippy::too_many_arguments)]
    fn resolve_pending_redo(
        &mut self,
        pending: &[PendingRef],
        side: &SideState,
        checkpoint: &recorded_lookup::Checkpoint,
        mut graph: recorded_lookup::Graph,
        mut previous: PassOutcomes,
        library_replay: Option<&LibraryReplay>,
        library_replayed: bool,
        passes: usize,
    ) -> bool {
        for _ in 0..passes {
            let metadata = self.metadata_snapshot();
            checkpoint.restore(self);
            self.restore_metadata_snapshot(&metadata);
            self.recorded_lookup_graph = Some(graph);
            self.recorded_lookup_ready = self.recorded_lookup_candidate;
            side.restore(self);
            self.pending = pending.to_vec();
            // A library the bootstrap took entirely from its recorded fixed
            // point stays there while user units cannot change its outcomes:
            // replay it again rather than re-resolve every library reference.
            (self.lib_hints, self.replay_completions) = match library_replay {
                Some((hints, completions))
                    if library_replayed && self.library_outcomes_are_own() =>
                {
                    self.lib_replay_targets_only = true;
                    (Some(hints.clone().into_iter()), Some(completions.clone()))
                }
                _ => (None, None),
            };
            for p in pending {
                if let Some((key, _)) = p.key.split_once('#') {
                    self.elements[p.elem].props.insert(key, json!([]));
                }
            }
            self.resolve_pending_pass();
            // A recorded-only selection can avoid lexical walks that proved
            // implicit/structural roots absent during bootstrap. Retain those
            // cache invalidation dependencies even when the final target hit.
            if let (Some(before), Some(after)) = (&checkpoint.lib_record, &mut self.lib_record) {
                for ((_, prior_misses), (_, misses)) in before.iter().zip(after) {
                    for name in prior_misses {
                        if !misses.contains(name) {
                            misses.push(name.clone());
                        }
                    }
                }
            }
            let current = self.pass_outcomes(pending);
            // A pass that changed no outcome leaves the rows as the previous
            // pass left them, so the associations it would recompute and the
            // graph it would build are the ones it read: settle that graph
            // instead of building it again.
            if current == previous {
                let mut graph = self
                    .recorded_lookup_graph
                    .take()
                    .expect("a redo pass reads the graph the previous pass built");
                graph.settle(self);
                self.note_root_imports_absent(&graph);
                self.recorded_lookup_graph = Some(graph);
                self.record_settled(pending);
                return true;
            }
            self.refresh_metadata_associations();
            graph = recorded_lookup::Graph::build(self);
            self.note_root_imports_absent(&graph);
            previous = current;
        }
        false
    }

    /// A graph that takes implied roots as absent holds only while the root
    /// namespace imports nothing: a root import completes that miss, so a
    /// model adding one resolves jointly rather than on this library.
    fn note_root_imports_absent(&mut self, graph: &recorded_lookup::Graph) {
        if graph.takes_implied_roots_absent() && !self.root_misses.contains(ROOT_IMPORTS) {
            self.root_misses.insert(ROOT_IMPORTS.to_owned());
        }
    }

    /// Whether library resolution sees what it saw when its outcomes were
    /// recorded, root names aside (the recorded misses cover those): the
    /// library annotates nothing by association itself, no annotation
    /// reaches the metadata of a library element, and no external name
    /// stands in for an implied library root.
    fn library_outcomes_are_own(&self) -> bool {
        let boundary = self.lib_boundary;
        self.external_implied_names.is_empty()
            && self
                .explicit_metadata_annotations
                .iter()
                .all(|&annotation| annotation >= boundary)
            && self.metadata_about.keys().all(|&target| target >= boundary)
    }

    fn resolve_pending_pass(&mut self) {
        note_pass();
        let pending = std::mem::take(&mut self.pending);
        if self.id_spelled_targets.is_empty() {
            self.id_binding_pending.clear();
        }
        if self.id_spelled_targets.is_empty()
            && pending.iter().any(|p| {
                p.elem >= self.lib_boundary
                    && p.qn
                        .segments
                        .iter()
                        .any(|s| s.value.len() >= 32 && Uuid::parse_str(&s.value).is_ok())
            })
        {
            self.id_binding_pending = pending
                .iter()
                .filter(|p| p.elem >= self.lib_boundary)
                .cloned()
                .collect();
        }
        let mut hints = self.lib_hints.take();
        let completions = self.replay_completions.take();
        let mut replay_active = hints.is_some() && completions.is_some();
        let mut replayed_all = replay_active;
        let targets_only = std::mem::take(&mut self.lib_replay_targets_only);
        let completions = completions.unwrap_or_default();
        let recording = self.lib_record.is_some();
        let mut lib_pos = 0usize;
        // Shadow filtering reads only recorded specialization outcomes to
        // avoid re-entering resolution. Pair cache outcomes with their
        // original entries first, then resolve specialization refs before
        // ordinary refs so forward references see a complete shadow graph.
        // Recording remains in original library-pending order.
        let mut work: Vec<PendingWork> = pending
            .into_iter()
            .enumerate()
            .map(|(source_order, pending)| {
                let is_lib_ref = self.lib_boundary > 0 && pending.elem < self.lib_boundary;
                let hint = if is_lib_ref && replay_active {
                    match hints.as_mut().and_then(|it| it.next()) {
                        // An outcome that missed a root name the user units
                        // now supply is resolved afresh; the entry is still
                        // consumed to keep the positional alignment.
                        Some((outcome, misses)) => {
                            (!misses.iter().any(|m| completions.contains(m))
                                && (outcome.is_some() || !targets_only))
                                .then_some((outcome, misses))
                        }
                        None => {
                            replay_active = false;
                            None
                        }
                    }
                } else {
                    None
                };
                replayed_all &= !is_lib_ref || hint.is_some();
                let record_pos = if is_lib_ref && recording {
                    let pos = lib_pos;
                    lib_pos += 1;
                    Some(pos)
                } else {
                    None
                };
                PendingWork {
                    source_order,
                    pending,
                    lib_hint: hint,
                    record_pos,
                }
            })
            .collect();
        if let Some(record) = self.lib_record.as_mut() {
            record.resize(lib_pos, (None, Vec::new()));
        }
        work.sort_by_key(|work| (work.pending.spec_idx.is_none(), work.source_order));
        // Target-UUID validation map for replayed outcomes, built on first
        // use: deterministic IDs are assigned before resolution, so every
        // cached target must already exist among the library elements.
        let mut lib_ids: Option<HashMap<Uuid, usize>> = None;
        for PendingWork {
            pending:
                PendingRef {
                    elem,
                    key,
                    scope,
                    qn,
                    exclude,
                    declared_only,
                    chain,
                    spec_idx,
                },
            lib_hint,
            record_pos,
            ..
        } in work
        {
            let is_lib_ref = self.lib_boundary > 0 && elem < self.lib_boundary;
            if is_lib_ref {
                match lib_hint {
                    Some((Some(id), misses)) => {
                        let ids = lib_ids.get_or_insert_with(|| {
                            self.elements
                                .iter()
                                .take(self.lib_boundary)
                                .enumerate()
                                .map(|(i, e)| (e.id, i))
                                .collect()
                        });
                        if let Some(&target) = ids.get(&id) {
                            // Replay must record spec outcomes exactly like
                            // the slow path: the recorded-only readers
                            // (`recorded_redefinition_targets`,
                            // `recorded_conforms`) otherwise see library
                            // redefinitions cold but not warm, and user
                            // resolution through inherited-merge shadowing
                            // would differ across cache states.
                            if let Some(si) = spec_idx {
                                self.record_spec_outcome(si, Some(target), &misses);
                            }
                            self.record_ref_misses(elem, &key, &misses);
                            self.set_pending_value(elem, &key, id_ref(id));
                            continue;
                        }
                        // Unknown target — cache/content skew; fall through
                        // to a full resolve of this entry.
                        replayed_all = false;
                    }
                    Some((None, misses)) => {
                        if let Some(si) = spec_idx {
                            self.record_spec_outcome(si, None, &misses);
                        }
                        self.record_ref_misses(elem, &key, &misses);
                        self.unresolved.push((elem, qn.clone()));
                        let v = json!({ "@ref": qn.to_ref_string() });
                        self.set_pending_value(elem, &key, v);
                        continue;
                    }
                    None => {}
                }
            }
            let saved_identity_origin = self.set_identity_origin(elem);
            let (saved, saved_mode) = (self.exclude, self.declared_only);
            self.query_imports.clear();
            let saved_header = self.redefinition_lookup_owner;
            let saved_base = self.redefinition_lookup_base.take();
            self.recorded_lookup_suppressed = false;
            self.redefinition_lookup_owner = (key == "redefinedFeature"
                && crate::metaclass::conforms(self.elements[elem].ty, "Redefinition"))
            .then(|| exclude.and_then(|feature| self.owner_elem(feature)))
            .flatten();
            self.exclude = exclude;
            self.current_misses.clear();
            // Contextual chain-step resolution first (effective names are
            // legitimate inside the target's scope), then the recorded
            // lexical mode as fallback.
            self.declared_only = false;
            let mut was_ambiguous = false;
            let mut imported_membership = None;
            let mut resolved = if key == "importedNamespace" {
                // A namespace import's own target takes the outcome the
                // resolution machinery computed (entry self-excluded); a
                // plain re-resolve here could capture a member through the
                // completed import (`import Domain::*` importing a package
                // that owns a member also named `Domain`).
                self.import_scopes(scope);
                match self.import_targets.get(&(scope, qn.to_ref_string())) {
                    Some((target, walked)) => {
                        let walked = walked.clone();
                        self.query_imports.extend(walked);
                        *target
                    }
                    None => None,
                }
            } else {
                let mark = self.query_imports.len();
                let hit = self.resolve_chain_member(scope, chain.as_deref(), &qn);
                if hit.is_none() {
                    // A failed chain attempt's walks are not this site's.
                    self.query_imports.truncate(mark);
                }
                hit
            };
            // Lexical fallback: a plain (non-chain) reference resolves from
            // its written scope, and a `$::`-rooted chain member re-roots
            // deliberately (the lift prints chain links globally). A chain
            // continuation spelled as a relative qualified name may also
            // fall back (the lift prints members as longest-named
            // suffixes, `dynamics.dynamics::x_out`), but only when the
            // lexical hit *agrees with the chain*: KerML resolves each
            // chaining feature after the first relative to the previous
            // one, so the fallback element must be the member the chain
            // target reaches under the spelling's last segment — anything
            // else silently accepted references the chain cannot legally
            // denote (a payload name once captured an unrelated
            // same-named sibling state this way).
            let chained = chain.as_deref().is_some_and(|c| !c.is_empty());
            if resolved.is_none() && key != "importedNamespace" {
                self.declared_only = declared_only;
                let import_all = key == "importedMembership"
                    && self.elements[elem]
                        .props
                        .get("isImportAll")
                        .and_then(|v| v.as_bool())
                        == Some(true);
                let lexical = match self.resolve_result(scope, &qn, 0, import_all) {
                    LookupResult::Found(found, _, membership) => {
                        imported_membership = membership;
                        Some(found)
                    }
                    LookupResult::Ambiguous => {
                        was_ambiguous = true;
                        None
                    }
                    LookupResult::Missing => None,
                };
                resolved = if !chained || qn.is_global {
                    lexical
                } else if let Some(found) = lexical {
                    let last = QualifiedName {
                        is_global: false,
                        segments: qn.segments.last().cloned().into_iter().collect(),
                        span: qn.span,
                    };
                    self.declared_only = false;
                    (self.resolve_chain_member(scope, chain.as_deref(), &last) == Some(found))
                        .then_some(found)
                } else {
                    None
                };
            }
            let semantically_suppressed = self.recorded_lookup_suppressed;
            // Record the reference site while `resolved` is still the
            // element the name *denotes* (before the serialization
            // substitutions below). Library-internal sites are skipped:
            // the sealed snapshot replays them without reaching this
            // point, and cold/warm builds must record identically.
            if !is_lib_ref {
                if let Some(target) = resolved {
                    let kind = key.split_once('#').map_or(key.as_str(), |(b, _)| b);
                    let unit = self.unit_of_elem(elem);
                    let plain = chain.is_none()
                        && !declared_only
                        && key != "importedNamespace"
                        && self.id_spelled_target(scope, &qn).is_none();
                    // Chain-root provenance: re-resolve the spine's first
                    // link under the spine's own rules (contextual mode,
                    // caller's exclusion) — `resolve_chain_member` resolved
                    // it exactly this way above. Recorded whenever a chain
                    // context exists, whichever resolution path won: the
                    // chain receiver is what the written form denotes
                    // through, and that is the provenance question.
                    let chain_root = chain.as_deref().and_then(|c| c.first()).and_then(|first| {
                        let saved_dm = self.declared_only;
                        self.declared_only = false;
                        let root = self.resolve(scope, first, 0);
                        self.declared_only = saved_dm;
                        root.map(ElementRef)
                    });
                    self.ref_sites.push(RefSite {
                        unit,
                        span: qn.span,
                        name_span: qn.segments.last().map_or(qn.span, |s| s.span),
                        target: ElementRef(target),
                        kind: kind.to_string(),
                        scope: ScopeRef(scope),
                        exclude: exclude.map(ElementRef),
                        plain,
                        owner: ElementRef(elem),
                        chain_root,
                        via_imports: {
                            let mut walks: Vec<(ElementRef, AccessMode)> =
                                std::mem::take(&mut self.query_imports)
                                    .into_iter()
                                    .map(|(rel, access)| (ElementRef(rel), access_mode(access)))
                                    .collect();
                            // Most restrictive access per import.
                            walks.sort_unstable();
                            walks.dedup_by(|later, earlier| later.0 == earlier.0);
                            walks
                        },
                    });
                }
                // Interior qualifier segments name ancestor elements
                // (`NominalScenario::TimeStateRecord` — the first segment
                // denotes the attribute def): a rename of those must
                // respell them, so each resolvable proper prefix records
                // its own site even when a later segment makes the whole
                // reference unresolved or ambiguous.
                let unit = self.unit_of_elem(elem);
                // Prefixes name namespaces/types, not the Feature expected
                // by the complete header. Preserve its selected base context.
                let qualifier_scope = self.redefinition_lookup_base.unwrap_or(scope);
                let header = self.redefinition_lookup_owner.take();
                for k in 1..qn.segments.len() {
                    let prefix = QualifiedName {
                        is_global: qn.is_global,
                        segments: qn.segments[..k].to_vec(),
                        span: qn.span,
                    };
                    if let Some(t) = self.resolve(qualifier_scope, &prefix, 0) {
                        self.ref_sites.push(RefSite {
                            unit,
                            span: qn.span,
                            name_span: qn.segments[k - 1].span,
                            target: ElementRef(t),
                            kind: "qualifier".to_string(),
                            scope: ScopeRef(qualifier_scope),
                            exclude: None,
                            plain: false,
                            owner: ElementRef(elem),
                            chain_root: None,
                            via_imports: Vec::new(),
                        });
                    }
                }
                self.redefinition_lookup_owner = header;
            }
            // `importedMembership` is Membership-typed (KerML 7.2.5.2): a
            // membership import references the resolved member's owning
            // Membership, retaining the named alias Membership when present.
            if key == "importedMembership" {
                resolved = resolved.map(|t| {
                    imported_membership
                        .or(self.elements[t].owning_relationship)
                        .unwrap_or(t)
                });
            }
            // A `~P` typing references P's implicit ConjugatedPortDefinition.
            if self.elements[elem].ty == "ConjugatedPortTyping" && key == "type" {
                resolved = resolved.map(|t| self.conjugated_defs.get(&t).copied().unwrap_or(t));
            }
            if is_lib_ref && resolved.is_some_and(|target| target >= self.lib_boundary) {
                self.library_refs_to_users = true;
            }
            let value = match resolved {
                Some(target) => id_ref(self.elements[target].id),
                None => {
                    if was_ambiguous {
                        self.ambiguous.push((elem, qn.clone()));
                    } else {
                        if !is_lib_ref && !semantically_suppressed {
                            if let Some(site) =
                                self.blocked_site(scope, chain.as_deref(), &qn, elem)
                            {
                                self.blocked.push(site);
                            }
                        }
                        self.unresolved.push((elem, qn.clone()));
                    }
                    crate::properties::Atom::from(json!({ "@ref": qn.to_ref_string() }))
                }
            };
            self.redefinition_lookup_owner = saved_header;
            self.redefinition_lookup_base = saved_base;
            (self.exclude, self.declared_only) = (saved, saved_mode);
            self.identity_origin_unit = saved_identity_origin;
            let misses = std::mem::take(&mut self.current_misses);
            if let Some(si) = spec_idx {
                self.record_spec_outcome(si, resolved, &misses);
            }
            self.record_ref_misses(elem, &key, &misses);
            self.current_misses = misses;
            if let Some(pos) = record_pos {
                self.lib_record.as_mut().unwrap()[pos] = (
                    resolved.map(|t| self.elements[t].id),
                    std::mem::take(&mut self.current_misses),
                );
            }
            self.set_pending_value(elem, &key, value);
        }
        self.lib_replayed_all = replayed_all;
        self.ref_sites.sort_by_key(|site| {
            (
                site.unit,
                site.span.start,
                site.span.end,
                site.name_span.start,
                site.name_span.end,
            )
        });
    }

    /// Record a specialization reference's outcome with the root misses
    /// behind it, for resolutions that read it later.
    fn record_spec_outcome(&mut self, si: usize, target: Option<usize>, misses: &[String]) {
        if self.spec_resolved.len() <= si {
            self.spec_resolved.resize(si + 1, None);
        }
        self.spec_resolved[si] = target;
        // Only a build that records its library outcomes reads the misses.
        if self.lib_record.is_none() {
            return;
        }
        self.spec_misses.set(si, misses);
    }

    /// Record the root misses behind a relationship's single-valued outcome.
    fn record_ref_misses(&mut self, elem: usize, key: &str, misses: &[String]) {
        if key.contains('#') || self.lib_record.is_none() {
            return;
        }
        self.ref_misses.set(elem, misses);
    }

    /// A resolution read the recorded outcomes of these specialization
    /// entries: it depends on the root names their references missed.
    fn note_spec_misses(&mut self, entries: impl IntoIterator<Item = usize>) {
        for i in entries {
            if let Some(misses) = self.spec_misses.get(i) {
                note_misses(&mut self.current_misses, misses.iter());
            }
        }
    }

    /// Store a resolved (or `@ref`) value under a pending ref's key —
    /// `key#n` spellings append to the `key` array property.
    fn set_pending_value(
        &mut self,
        elem: usize,
        key: &str,
        value: impl Into<crate::properties::Atom>,
    ) {
        if let Some((base, _)) = key.split_once('#') {
            self.elements[elem].props.append(base, value);
        } else {
            self.set(elem, key, value);
        }
    }

    /// Element index for a binary interchange identity.
    pub(crate) fn element_index_of_uuid(&mut self, id: Uuid) -> Option<usize> {
        let stale = self.id_index.is_none() || self.id_index_built_for != self.elements.len();
        if stale {
            let n = self.elements.len();
            self.id_index_built_for = n;
            // The frozen rows through the table their freeze kept, copied,
            // and the rows after them tabled here; every row otherwise.
            let (mut index, start) = match self.prefix_ids.as_deref() {
                // (an identity override writes a frozen row's id: then every
                // row is tabled)
                Some(frozen)
                    if frozen.len() == self.lib_boundary
                        && self.lib_boundary <= n
                        && self.elements.base_untouched() =>
                {
                    (frozen.clone(), self.lib_boundary)
                }
                _ => (
                    crate::layered::IdMap::with_capacity_and_hasher(n, Default::default()),
                    0,
                ),
            };
            note_id_index_tabled(n - start);
            for (i, el) in self.elements.iter().enumerate().skip(start) {
                index.insert(el.id, i);
            }
            self.id_index = Some(Arc::new(index));
        }
        self.id_index.as_ref().unwrap().get(&id).copied()
    }

    /// The identity tables of a build on this builder's frozen rows, for a
    /// test to read a library name through.
    #[cfg(test)]
    fn identity_tables_for_test(&self) -> IdentityTables {
        IdentityTables {
            start: self.lib_boundary,
            by_id: crate::layered::IdMap::default(),
            names: Vec::new(),
            frozen: self.prefix_ids.clone(),
            table_names: None,
        }
    }

    /// The library name tables by id, the first entry of an id winning.
    fn library_table_names(&self) -> HashMap<Uuid, String> {
        let mut tables = HashMap::new();
        for (id, segments) in self.lib_qnames.iter().chain(self.lib_mem_qnames.iter()) {
            if let Some(last) = segments.last() {
                tables.entry(*id).or_insert_with(|| last.clone());
            }
        }
        tables
    }

    /// The multiplicity `e` declares of its own — the scope it was
    /// written in and its clause — through the owner index. `None` when
    /// `e` declares none; inherited ones are not walked.
    pub(crate) fn declared_multiplicity_of(&mut self, e: usize) -> Option<(usize, &Multiplicity)> {
        let rows = self.multiplicities.len();
        if self.mult_index.as_ref().is_none_or(|(n, _)| *n != rows) {
            let (mut map, from) = match self.library_multiplicity_rows() {
                Some(prepared) => (
                    crate::layered::LayeredMap::over(Arc::clone(
                        prepared.library_declared_multiplicities(),
                    )),
                    self.multiplicities.base_len(),
                ),
                None => (crate::layered::LayeredMap::default(), 0),
            };
            self.index_declared_multiplicities(from..rows, &mut map);
            self.mult_index = Some((rows, map));
        }
        let i = *self.mult_index.as_ref().unwrap().1.get(&e)?;
        let (_, scope, mult) = &self.multiplicities[i];
        Some((*scope, mult))
    }

    /// The prepared library this build stands on, while the build's element
    /// and multiplicity rows below its own are the library's frozen rows:
    /// the library's indexes of those rows then index them here too.
    pub(crate) fn library_multiplicity_rows(
        &self,
    ) -> Option<&Arc<crate::prepared::PreparedLibrary>> {
        self.prepared_from.as_ref().filter(|prepared| {
            self.elements.base_untouched()
                && Arc::ptr_eq(
                    self.elements.base_arc(),
                    prepared.builder.elements.base_arc(),
                )
                && self.multiplicities.base_untouched()
                && Arc::ptr_eq(
                    self.multiplicities.base_arc(),
                    prepared.builder.multiplicities.base_arc(),
                )
        })
    }

    /// Index the multiplicity rows `rows` by the element whose own
    /// multiplicity each declares into `index`, the first row winning.
    pub(crate) fn index_declared_multiplicities(
        &self,
        rows: std::ops::Range<usize>,
        index: &mut crate::layered::LayeredMap<usize, usize>,
    ) {
        for i in rows {
            let owner = self.multiplicities[i].0;
            // A named/body range's numeric domain is not a declaration of
            // that Multiplicity Feature's own cardinality.
            if crate::metaclass::conforms(self.elements[owner].ty, "Multiplicity") {
                continue;
            }
            index.entry(owner).or_insert(i);
        }
    }

    /// The multiplicity rows by the range each constrains, the last row
    /// winning: a build on a prepared library indexes its own rows over the
    /// library's index.
    pub(crate) fn multiplicity_range_rows(&self) -> crate::layered::LayeredMap<usize, usize> {
        let (mut rows, from) = match self.library_multiplicity_rows() {
            Some(prepared) => (
                crate::layered::LayeredMap::over(Arc::clone(
                    prepared.library_multiplicity_ranges(),
                )),
                self.multiplicities.base_len(),
            ),
            None => (crate::layered::LayeredMap::default(), 0),
        };
        self.index_multiplicity_ranges(from..self.multiplicities.len(), &mut rows);
        rows
    }

    /// Index the multiplicity rows `rows` by the multiplicity range each
    /// constrains into `index`, the last row winning.
    pub(crate) fn index_multiplicity_ranges(
        &self,
        rows: std::ops::Range<usize>,
        index: &mut crate::layered::LayeredMap<usize, usize>,
    ) {
        for i in rows {
            let owner = self.multiplicities[i].0;
            let range = if crate::metaclass::conforms(self.elements[owner].ty, "Multiplicity") {
                Some(owner)
            } else {
                self.local_multiplicity(owner).flatten()
            };
            if let Some(range) = range {
                index.insert(range, i);
            }
        }
    }

    /// Does `e` declare a multiplicity of its own?
    pub(crate) fn declares_multiplicity(&mut self, e: usize) -> bool {
        self.declared_multiplicity_of(e).is_some()
    }

    /// The elements owned by `e` through its owned memberships (any
    /// Membership kind), in declaration order — KerML
    /// `Namespace::ownedMember`. With `features_only`, just the members
    /// owned via FeatureMembership kinds (`Type::ownedFeature`), so a
    /// package answers none. Aliases own no element, so they never
    /// appear; anonymous members do.
    pub(crate) fn owned_member_elems(&self, e: usize, features_only: bool) -> Vec<usize> {
        let mut children: Vec<_> = self.elements[e]
            .owned_relationships
            .iter()
            .copied()
            .filter(|&r| {
                if features_only {
                    is_feature_membership(self.elements[r].ty)
                } else {
                    self.elements[r].ty.ends_with("Membership")
                }
            })
            .flat_map(|r| self.elements[r].children.iter().copied())
            .collect();
        // Preserve the former whole-graph scan's creation order even when
        // children were appended to an earlier relationship later in lowering.
        children.sort_unstable();
        children.dedup();
        children
    }

    /// Original unit index of the unit that built element `elem`.
    pub(crate) fn unit_of_elem(&self, elem: usize) -> usize {
        let elem = self
            .semantic_ownership
            .as_ref()
            .map_or(elem, |view| view.source_anchor(elem));
        match self.unit_starts.binary_search_by_key(&elem, |&(e, _)| e) {
            Ok(i) => self.unit_starts[i].1,
            Err(0) => 0,
            Err(i) => self.unit_starts[i - 1].1,
        }
    }

    /// Original unit index of the unit that created scope `s`.
    fn unit_of_scope(&self, s: usize) -> usize {
        match self.scope_starts.binary_search_by_key(&s, |&(sc, _)| sc) {
            Ok(i) => self.scope_starts[i].1,
            Err(0) => 0,
            Err(i) => self.scope_starts[i - 1].1,
        }
    }

    /// Alias members whose target does not resolve.
    fn check_aliases(&mut self) -> Vec<(usize, QualifiedName)> {
        let mut out = Vec::new();
        for s in 0..self.scopes.len() {
            for (i, (_, qn, _)) in self.scopes[s].aliases.clone().into_iter().enumerate() {
                let origin = self.identity_origin_unit;
                let unit = self
                    .alias_origins
                    .get(&(s, i))
                    .copied()
                    .unwrap_or_else(|| self.unit_of_scope(s));
                self.identity_origin_unit = Some(unit);
                let missing = self.resolve(s, &qn, 0).is_none();
                self.identity_origin_unit = origin;
                if missing {
                    out.push((unit, qn));
                }
            }
        }
        out
    }

    /// Root memberships of user units whose name a library unit also
    /// declares at the root, and that a root lookup of the name does not
    /// select (the library declaration wins — earlier candidate of
    /// non-overlapping metaclasses — or the pair is ambiguous). Read off
    /// the shared root scope so the verdict is the lookup's own, not a
    /// textual guess: a user root that *does* win the lookup is not
    /// reported. Name-sorted for deterministic output.
    fn check_root_shadowing(&self) -> Vec<RootShadowing> {
        let mut out = Vec::new();
        if self.lib_boundary == 0 || self.scopes.is_empty() {
            return out;
        }
        let boundary = self.lib_boundary;
        let mut collisions: Vec<(String, Vec<Binding>)> = self.scopes[0]
            .names
            .iter()
            .filter(|(_, bindings)| {
                bindings.iter().any(|b| b.elem < boundary)
                    && bindings.iter().any(|b| b.elem >= boundary)
            })
            .map(|(name, bindings)| (name.to_owned(), bindings.to_vec()))
            .collect();
        collisions.sort_by(|a, b| a.0.cmp(&b.0));
        for (name, bindings) in collisions {
            let (library_elem, resolves_to_library) =
                match self.binding_result(Some(&bindings), LookupAccess::All, None, false) {
                    LookupResult::Found(elem, _, _) if elem < boundary => (elem, true),
                    LookupResult::Found(..) => continue,
                    LookupResult::Ambiguous | LookupResult::Missing => {
                        let Some(first) = bindings.iter().find(|b| b.elem < boundary) else {
                            continue;
                        };
                        (first.elem, false)
                    }
                };
            for binding in bindings.iter().filter(|b| b.elem >= boundary) {
                let elem = binding.elem;
                let span = self
                    .decl_spans
                    .get(&elem)
                    .or_else(|| self.member_spans.get(&elem))
                    .copied()
                    .unwrap_or_default();
                out.push(RootShadowing {
                    unit: self.unit_of_elem(elem),
                    span,
                    name: name.clone(),
                    metaclass: self.elements[elem].ty,
                    library_metaclass: self.elements[library_elem].ty,
                    resolves_to_library,
                });
            }
        }
        out
    }

    /// Namespace imports that transitively import their own namespace back.
    /// Importing an *ancestor* namespace is not a cycle — only a loop in the
    /// import graph itself is.
    fn check_import_cycles(&mut self) -> Vec<(usize, QualifiedName)> {
        let mut out = Vec::new();
        for s in 0..self.scopes.len() {
            let imports = self.scopes[s].imports.clone();
            for entry in imports {
                let origin = self.set_identity_origin(entry.relationship);
                let resolved = self.resolve(s, &entry.target, 0);
                self.identity_origin_unit = origin;
                if let Some(elem) = resolved {
                    if let Some(&target) = self.elem_scope.get(&elem) {
                        if self.imports_reach(target, s) {
                            out.push((self.unit_of_scope(s), entry.target));
                        }
                    }
                }
            }
        }
        out
    }

    /// Whether `needle` is reachable from `from` over namespace-import
    /// edges (including `from == needle`).
    fn imports_reach(&mut self, from: usize, needle: usize) -> bool {
        let mut seen = std::collections::HashSet::new();
        let mut stack = vec![from];
        while let Some(s) = stack.pop() {
            if s == needle {
                return true;
            }
            if !seen.insert(s) {
                continue;
            }
            for imported in self.import_scopes(s).iter() {
                stack.push(imported.scope);
            }
        }
        false
    }

    /// After a user reference misses: the blocked-member record for it,
    /// if a wider visibility on one member would make it resolve. The
    /// probe finds the candidate; a re-resolution with that member
    /// admitted as if public confirms the repair (a path through several
    /// hidden members offers nothing); a second one as if protected says
    /// whether the narrower keyword suffices (the site reaches the member
    /// through a specialization).
    fn blocked_site(
        &mut self,
        scope: usize,
        chain: Option<&[QualifiedName]>,
        qn: &QualifiedName,
        owner: usize,
    ) -> Option<BlockedSite> {
        let (member, visibility) = self.probe_visibility_blocked(scope, chain, qn)?;
        if !self.resolves_widened(scope, chain, qn, member, LookupAccess::Public) {
            return None;
        }
        let protected_suffices = visibility == "private"
            && self.resolves_widened(scope, chain, qn, member, LookupAccess::Protected);
        let spelling = chain
            .unwrap_or(&[])
            .iter()
            .map(QualifiedName::to_display_string)
            .chain(std::iter::once(qn.to_display_string()))
            .collect::<Vec<_>>()
            .join(".");
        Some(BlockedSite {
            owner,
            name: qn.clone(),
            spelling,
            member,
            visibility,
            protected_suffices,
        })
    }

    /// The pending reference's own resolution, as the resolver first ran
    /// it: a chain step contextually (effective names admitted), a plain
    /// reference lexically under the pending's recorded mode.
    fn resolve_as_pending(
        &mut self,
        scope: usize,
        chain: Option<&[QualifiedName]>,
        qn: &QualifiedName,
    ) -> Option<usize> {
        match chain {
            Some(c) if !c.is_empty() => {
                let saved = self.declared_only;
                self.declared_only = false;
                let found = self.resolve_chain_member(scope, Some(c), qn);
                self.declared_only = saved;
                found
            }
            _ => self.resolve(scope, qn, 0),
        }
    }

    /// Whether the reference resolves to `member` once that member is
    /// admitted as if it had visibility `as_if` — the original access
    /// modes otherwise in force.
    fn resolves_widened(
        &mut self,
        scope: usize,
        chain: Option<&[QualifiedName]>,
        qn: &QualifiedName,
        member: usize,
        as_if: LookupAccess,
    ) -> bool {
        self.widen = Some((member, as_if));
        let found = self.resolve_as_pending(scope, chain, qn);
        self.widen = None;
        found == Some(member)
    }

    /// After a miss: the member the reference would reach if visibility
    /// were ignored, with its declared visibility — `None` when the name
    /// is simply absent or the candidate is public anyway (the miss had
    /// another cause). Runs with every access mode widened and records
    /// no import use, so it never changes what the model resolves. The
    /// reference's own exclusion and declared-only mode stay in force:
    /// a redefinition must not capture the redefining feature through
    /// its effective name.
    fn probe_visibility_blocked(
        &mut self,
        scope: usize,
        chain: Option<&[QualifiedName]>,
        qn: &QualifiedName,
    ) -> Option<(usize, &'static str)> {
        self.probing = true;
        let found = self.resolve_as_pending(scope, chain, qn);
        self.probing = false;
        let member = found?;
        let visibility = self.elements[member]
            .owning_relationship
            .and_then(|rel| self.elements[rel].props.get("visibility"))
            .and_then(|v| v.as_str())?;
        match visibility {
            "private" => Some((member, "private")),
            "protected" => Some((member, "protected")),
            _ => None,
        }
    }

    /// Resolve a chain step's member in the scope of its spine target:
    /// resolve the first link lexically, each further link (and finally the
    /// member's segments) as a member — owned or inherited — of the previous
    /// link's feature. `None` when there is no static spine or any link
    /// fails, so the caller can fall back to lexical resolution.
    pub(crate) fn resolve_chain_member(
        &mut self,
        scope: usize,
        chain: Option<&[QualifiedName]>,
        member: &QualifiedName,
    ) -> Option<usize> {
        let (first, rest) = chain?.split_first()?;
        let elem = self.resolve(scope, first, 0)?;
        let mut segments: Vec<Name> = Vec::new();
        for link in rest {
            segments.extend(link.segments.iter().cloned());
        }
        segments.extend(member.segments.iter().cloned());
        let sub = self.elem_scope.get(&elem).copied();
        // Member steps resolve against the *target's* scope, where landing
        // on the feature currently being defined is legitimate — recursive
        // rollups like `totalMass = mass + sum(subcomponents.totalMass)`
        // (Apollo study). The value-expression self-exclusion
        // is a lexical-capture guard and applied to the spine above only.
        let saved = self.exclude;
        self.exclude = None;
        let out = match self.resolve_rest_result(scope, elem, sub, &segments, 0, false) {
            LookupResult::Found(found, _, _) => Some(found),
            LookupResult::Missing | LookupResult::Ambiguous => None,
        };
        self.exclude = saved;
        out
    }

    /// Resolve a qualified name from `scope`, walking owning scopes outward.
    /// Each step consults, in order: owned members, aliases, membership
    /// imports, inherited members (specialization bases), and namespace
    /// imports — including re-exports and recursive (`::**`) imports.
    pub(crate) fn resolve(
        &mut self,
        scope: usize,
        qn: &QualifiedName,
        depth: usize,
    ) -> Option<usize> {
        match self.resolve_result(scope, qn, depth, false) {
            LookupResult::Found(elem, _, _) => Some(elem),
            LookupResult::Missing | LookupResult::Ambiguous => None,
        }
    }

    pub(crate) fn intrinsic_function_name(
        &mut self,
        scope: usize,
        qn: &QualifiedName,
    ) -> Option<String> {
        match self.resolve_result(scope, qn, 0, false) {
            LookupResult::Found(elem, _, _) if elem < self.lib_boundary => {
                crate::eval::library_intrinsic_for_id(self.elem_id(elem)).map(str::to_owned)
            }
            LookupResult::Missing
                if !qn.is_global
                    && qn.segments.len() == 1
                    && crate::eval::intrinsic_spelling(&qn.segments[0].value) =>
            {
                // A visibility failure is not an absent convenience name.
                // Probe with widened access without recording import usage.
                let probing = self.probing;
                self.probing = true;
                let absent = matches!(
                    self.resolve_result(scope, qn, 0, false),
                    LookupResult::Missing
                );
                self.probing = probing;
                absent.then(|| qn.segments[0].value.clone())
            }
            _ => None,
        }
    }

    /// Tooling lookup by absolute model path. Unlike source-language
    /// resolution, model introspection is allowed to address private and
    /// protected members; ambiguity is still an error.
    fn resolve_unrestricted(&mut self, scope: usize, qn: &QualifiedName) -> LookupResult {
        if qn.segments.is_empty() {
            return LookupResult::Missing;
        }
        let first = qn.segments[0].value.clone();
        let mut current = Some(if qn.is_global { 0 } else { scope });
        let stamp = self.next_stamp();
        while let Some(s) = current {
            match self.lookup_at(s, &first, 0, stamp, LookupAccess::All) {
                hit @ LookupResult::Found(elem, sub_scope, _) => {
                    return if qn.segments.len() == 1 {
                        hit
                    } else {
                        self.resolve_rest_unrestricted(elem, sub_scope, &qn.segments[1..], 0)
                    };
                }
                LookupResult::Ambiguous => return LookupResult::Ambiguous,
                LookupResult::Missing => {}
            }
            current = self.scopes[s].parent;
        }
        LookupResult::Missing
    }

    fn resolve_rest_unrestricted(
        &mut self,
        elem: usize,
        scope: Option<usize>,
        rest: &[Name],
        depth: usize,
    ) -> LookupResult {
        if rest.is_empty() {
            return LookupResult::Found(elem, scope, None);
        }
        let Some(scope) = scope else {
            return LookupResult::Missing;
        };
        let stamp = self.next_stamp();
        match self.lookup_at(scope, &rest[0].value, depth + 1, stamp, LookupAccess::All) {
            hit @ LookupResult::Found(next, next_scope, _) => {
                if rest.len() == 1 {
                    hit
                } else {
                    self.resolve_rest_unrestricted(next, next_scope, &rest[1..], depth + 1)
                }
            }
            other => other,
        }
    }

    /// Switch source provenance for expression and runtime-parameter queries.
    /// Return the previous origin for the caller to restore on every exit.
    #[inline]
    pub(crate) fn set_identity_origin(&mut self, element: usize) -> Option<usize> {
        let previous = self.identity_origin_unit;
        self.identity_origin_unit = Some(self.unit_of_elem(element));
        previous
    }

    /// Whether any name resolves by the identity it spells, which makes
    /// resolution depend on the identity origin.
    #[inline]
    pub(crate) fn has_id_spelled_targets(&self) -> bool {
        !self.id_spelled_targets.is_empty()
    }

    /// An identity carried through textual lifting is tied to its source
    /// site, not to its spelling: a different site can legitimately use
    /// that UUID as an ordinary declared name.
    #[inline]
    fn id_spelled_target(&self, _scope: usize, qn: &QualifiedName) -> Option<Uuid> {
        self.id_spelled_name(qn.segments.first()?)
    }

    #[inline]
    fn id_spelled_name(&self, first: &Name) -> Option<Uuid> {
        if self.id_spelled_targets.is_empty() {
            return None;
        }
        let (spelling, target) = self
            .id_spelled_targets
            .get(&(self.identity_origin_unit?, first.span.start, first.span.end))
            .copied()?;
        (Uuid::parse_str(&first.value).ok() == Some(spelling)).then_some(target)
    }

    /// Resolution with ambiguity retained. `allow_last_non_public` is used
    /// only by `import all` membership imports: intermediate qualifiers
    /// still obey normal visibility, while the imported membership itself
    /// may be private or protected.
    fn resolve_result(
        &mut self,
        scope: usize,
        qn: &QualifiedName,
        depth: usize,
        allow_last_non_public: bool,
    ) -> LookupResult {
        if depth > MAX_RESOLUTION_DEPTH || qn.segments.is_empty() {
            return LookupResult::Missing;
        }
        // Redefinition headers resolve from each direct general Type, in
        // declaration order, without admitting the declaring Type's members.
        // Starting contexts use frozen explicit endpoints even when lookup
        // inside those contexts still needs the contextual resolver.
        if self.recorded_lookup_ready
            && !self.recorded_lookup_incomplete
            && self.id_spelled_target(scope, qn).is_none()
        {
            if let Some(owner) = self.redefinition_lookup_owner {
                if let Some(&owner_scope) = self.elem_scope.get(&owner) {
                    if self.recorded_lookup_graph.is_none() {
                        self.recorded_lookup_graph = Some(recorded_lookup::Graph::build(self));
                    }
                    let graph = self.recorded_lookup_graph.as_mut().unwrap();
                    let complete = graph
                        .direct_bases(owner_scope, &mut self.current_misses)
                        .is_some();
                    let bases = graph.header_bases(owner_scope, &mut self.current_misses);
                    if let Some(bases) = bases {
                        let saved = self.redefinition_lookup_owner.take();
                        let mut result = LookupResult::Missing;
                        for base in bases {
                            let hit =
                                self.resolve_result(base, qn, depth + 1, allow_last_non_public);
                            match hit {
                                LookupResult::Found(e, _, _)
                                    if crate::metaclass::conforms(
                                        self.elements[e].ty,
                                        "Feature",
                                    ) =>
                                {
                                    result = hit;
                                    self.redefinition_lookup_base = Some(base);
                                    break;
                                }
                                LookupResult::Ambiguous => result = LookupResult::Ambiguous,
                                _ => {}
                            }
                        }
                        self.redefinition_lookup_owner = saved;
                        if complete || matches!(result, LookupResult::Found(..)) {
                            return result;
                        }
                    }
                }
                // An unsupported header keeps the contextual fallback, but
                // nested alias/base resolution must not restart this header.
                let saved = self.redefinition_lookup_owner.take();
                let result = self.resolve_result(scope, qn, depth, allow_last_non_public);
                self.redefinition_lookup_owner = saved;
                return result;
            }
        }
        let first = qn.segments[0].value.clone();
        if let Some(id) = self.id_spelled_target(scope, qn) {
            let Some(elem) = self.element_index_of_uuid(id) else {
                return LookupResult::Missing;
            };
            let sub_scope = self.elem_scope.get(&elem).copied();
            return self.resolve_rest_result(
                scope,
                elem,
                sub_scope,
                &qn.segments[1..],
                depth,
                allow_last_non_public,
            );
        }
        // `$::` roots resolution at the global namespace (scope 0).
        let mut current = Some(if qn.is_global { 0 } else { scope });
        let stamp = self.next_stamp();
        while let Some(s) = current {
            // The first segment is a lexical name, so it sees semantic names
            // only. An unnamed usage that merely spells its referenced
            // feature (`satisfy R by x;`, `assert c;`) has no name of its
            // own, and must not stand in for `R` when a sibling's reference
            // looks `R` up in an enclosing scope. Qualified member steps
            // still reach such a usage through that spelling.
            match self.lookup_at_with_names(s, &first, depth, stamp, LookupAccess::All, true) {
                hit @ LookupResult::Found(elem, sub_scope, _) => {
                    if qn.segments.len() == 1 {
                        return hit;
                    }
                    return self.resolve_rest_result(
                        scope,
                        elem,
                        sub_scope,
                        &qn.segments[1..],
                        depth,
                        allow_last_non_public,
                    );
                }
                LookupResult::Ambiguous => return LookupResult::Ambiguous,
                LookupResult::Missing => {}
            }
            current = self.scopes[s].parent;
        }
        LookupResult::Missing
    }

    /// Look `name` up in scope `s` without walking owning scopes: owned
    /// members, aliases, membership imports, inherited members, then
    /// namespace imports (transitively, so re-exports are visible).
    pub(crate) fn lookup(
        &mut self,
        s: usize,
        name: &str,
        depth: usize,
    ) -> Option<(usize, Option<usize>)> {
        let stamp = self.next_stamp();
        self.lookup_at(s, name, depth, stamp, LookupAccess::All)
            .option()
    }

    /// A fresh query number for one (start scope, name) lookup chase.
    fn next_stamp(&mut self) -> u64 {
        self.query_stamp += 1;
        self.query_stamp
    }

    /// [`Self::lookup`] within an active query. Completed outcomes are
    /// memoized per scope for the query; an in-progress cyclic re-entry
    /// answers missing. Import filters are evaluated by the caller against
    /// the cached candidate, so separate filtered paths remain independent.
    fn lookup_at(
        &mut self,
        s: usize,
        name: &str,
        depth: usize,
        stamp: u64,
        access: LookupAccess,
    ) -> LookupResult {
        self.lookup_at_with_names(s, name, depth, stamp, access, false)
    }

    /// Semantic import lookup excludes compatibility locators before merging
    /// candidates. Separate memo slots preserve replay lookup within the same
    /// query (for example while an alias resolves its target).
    fn lookup_at_with_names(
        &mut self,
        s: usize,
        name: &str,
        depth: usize,
        stamp: u64,
        access: LookupAccess,
        semantic_names: bool,
    ) -> LookupResult {
        let hit = if depth > MAX_RESOLUTION_DEPTH {
            LookupResult::Missing
        } else {
            let mode = access as usize + usize::from(semantic_names) * 3;
            if self.visit_stamp[s][mode] == stamp {
                self.visit_result[s][mode].unwrap_or(LookupResult::Missing)
            } else {
                self.visit_stamp[s][mode] = stamp;
                self.visit_result[s][mode] = None;
                let hit = self.lookup_body(s, name, depth, stamp, access, semantic_names);
                self.visit_result[s][mode] = Some(hit);
                hit
            }
        };
        // Cyclic re-entries and depth cutoffs also count as misses; that
        // only makes the prepared-path guard more conservative.
        if s == 0 && hit == LookupResult::Missing {
            self.note_root_miss(name);
        }
        hit
    }

    /// Every valued redefinition of a feature chain (`attribute :>> a.b =
    /// v;`), keyed by the type that owns the redefining feature: (the
    /// redefining feature, the chain's resolved links). Evaluation reads it
    /// whenever a chain of names walks through such an owner; it is built
    /// on first use, for the elements present then.
    pub(crate) fn chain_redefinitions(&mut self) -> ChainRedefinitions {
        if let Some((built_for, index)) = &self.chain_redefinitions {
            if *built_for == self.elements.len() {
                return Arc::clone(index);
            }
        }
        // A build whose rows, values and body scopes below its own are its
        // prepared library's, and none of whose own rows takes a library
        // row's id, finds for the library's features what the library finds
        // alone: it indexes only its own over the library's index.
        let (mut index, features) = match self.library_chain_redefinitions() {
            Some(library) => (
                crate::layered::LayeredMap::over(library),
                self.values.local_iter().map(|(&f, _)| f).collect(),
            ),
            None => (
                crate::layered::LayeredMap::default(),
                self.values.iter().map(|(&f, _)| f).collect(),
            ),
        };
        self.index_chain_redefinitions(features, &mut index);
        let index = Arc::new(index);
        self.chain_redefinitions = Some((self.elements.len(), Arc::clone(&index)));
        index
    }

    /// The prepared library's valued chain redefinitions, when this build
    /// finds for the library's features what the library finds alone (see
    /// [`Self::chain_redefinitions`]).
    fn library_chain_redefinitions(&mut self) -> Option<crate::prepared::ChainIndex> {
        let prepared = self.prepared_from.clone()?;
        let library = &prepared.builder;
        let boundary = self.lib_boundary;
        let shared = self.elements.base_untouched()
            && Arc::ptr_eq(self.elements.base_arc(), library.elements.base_arc())
            && boundary == self.elements.base_len()
            && Arc::ptr_eq(self.values.base_arc(), library.values.base_arc())
            && !self.values.local_iter().any(|(&f, _)| f < boundary)
            && Arc::ptr_eq(self.elem_scope.base_arc(), library.elem_scope.base_arc())
            && !self.elem_scope.local_iter().any(|(&e, _)| e < boundary);
        if !shared {
            return None;
        }
        let ids = self.prefix_ids.as_ref()?;
        if (boundary..self.elements.len()).any(|e| ids.contains_key(&self.elements[e].id)) {
            return None;
        }
        Some(Arc::clone(prepared.library_chain_redefinitions()))
    }

    /// Index the valued chain redefinitions of `features` by the type that
    /// owns each redefining feature into `index`, after the entries it holds.
    pub(crate) fn index_chain_redefinitions(
        &mut self,
        features: Vec<usize>,
        index: &mut crate::layered::LayeredMap<usize, Vec<(usize, Vec<usize>)>>,
    ) {
        for feature in features {
            let redefinitions: Vec<usize> = self.elements[feature]
                .owned_relationships
                .iter()
                .copied()
                .filter(|&r| self.elements[r].ty == "Redefinition")
                .collect();
            for redefinition in redefinitions {
                // A chain target is the anonymous feature the redefinition
                // owns, one FeatureChaining per link.
                let Some(&chain) = self.elements[redefinition].children.first() else {
                    continue;
                };
                let chainings: Vec<usize> = self.elements[chain]
                    .owned_relationships
                    .iter()
                    .copied()
                    .filter(|&r| self.elements[r].ty == "FeatureChaining")
                    .collect();
                if chainings.len() < 2 {
                    continue;
                }
                let total = chainings.len();
                let mut links = Vec::with_capacity(total);
                for chaining in chainings {
                    let Some(link) = self.elements[chaining]
                        .props
                        .get("chainingFeature")
                        .and_then(|v| v.as_reference())
                        .and_then(|id| self.element_index_of_uuid(id))
                    else {
                        break;
                    };
                    links.push(link);
                }
                // Every link must have resolved.
                if links.len() != total {
                    continue;
                }
                if let Some(owner) = self.owner_elem(feature) {
                    index.entry(owner).or_default().push((feature, links));
                }
            }
        }
    }

    // Kept out of line: `lookup_at` recurses deeply through imports and
    // aliases, and unoptimized frames pay for every temporary.
    #[inline(never)]
    fn note_root_miss(&mut self, name: &str) {
        if !self.root_misses.contains(name) {
            self.root_misses.insert(name.to_owned());
        }
        if !self.current_misses.iter().any(|m| m == name) {
            self.current_misses.push(name.to_owned());
        }
    }

    /// Set aside the lookup state of the query in progress before computing
    /// a lookup-cache entry. The entry outlives the query, so it must not
    /// depend on it: a probe's or a widened member's access, an excluded
    /// element, a chain step's declared names only, a redefinition header,
    /// a membership import or filter resolving its own target. Otherwise
    /// whichever reference first reads the entry decides it for all later
    /// ones — and a replayed build, which reads it from another reference,
    /// would resolve differently from a cold one.
    fn enter_fill_mode(&mut self) -> QueryMode {
        let filters = self.filters_active.contains(&true).then(|| {
            let idle = vec![false; self.filters_active.len()];
            std::mem::replace(&mut self.filters_active, idle)
        });
        QueryMode {
            probing: std::mem::replace(&mut self.probing, false),
            widen: self.widen.take(),
            exclude: self.exclude.take(),
            declared_only: std::mem::replace(&mut self.declared_only, false),
            header_owner: self.redefinition_lookup_owner.take(),
            header_base: self.redefinition_lookup_base.take(),
            member_imports: std::mem::take(&mut self.member_import_active),
            filters,
            suppressed: std::mem::replace(&mut self.recorded_lookup_suppressed, false),
        }
    }

    /// Restore the query state [`Self::enter_fill_mode`] set aside.
    fn leave_fill_mode(&mut self, query: QueryMode) {
        self.probing = query.probing;
        self.widen = query.widen;
        self.exclude = query.exclude;
        self.declared_only = query.declared_only;
        self.redefinition_lookup_owner = query.header_owner;
        self.redefinition_lookup_base = query.header_base;
        self.member_import_active = query.member_imports;
        if let Some(filters) = query.filters {
            self.filters_active = filters;
        }
        self.recorded_lookup_suppressed = query.suppressed;
    }

    /// Start computing a lookup-cache entry: the misses noted from here to
    /// [`Self::end_fill`] are the entry's own. The returned number marks
    /// the entry as [`FillMisses::Filling`] meanwhile.
    fn begin_fill(&mut self) -> usize {
        let interrupted = std::mem::take(&mut self.current_misses);
        self.fill_frames.push(interrupted);
        self.fill_frames.len()
    }

    /// Finish the innermost fill: its misses are also the misses of the
    /// resolution it interrupted, which read the entry it computed.
    fn end_fill(&mut self) -> FillMisses {
        let interrupted = self.fill_frames.pop().unwrap_or_default();
        let noted = std::mem::replace(&mut self.current_misses, interrupted);
        if noted.is_empty() {
            return FillMisses::None;
        }
        note_misses(&mut self.current_misses, &noted);
        FillMisses::Missed(noted.into())
    }

    fn set_base_misses(&mut self, s: usize, misses: FillMisses) {
        if self.base_misses.len() <= s {
            self.base_misses.resize(s + 1, FillMisses::None);
        }
        self.base_misses[s] = misses;
    }

    fn set_import_misses(&mut self, s: usize, misses: FillMisses) {
        if self.import_misses.len() <= s {
            self.import_misses.resize(s + 1, FillMisses::None);
        }
        self.import_misses[s] = misses;
    }

    /// A read of a lookup-cache entry notes the misses behind it: all of
    /// them once computed, and those noted so far while a fill that the
    /// reader runs inside computes it.
    #[inline]
    fn note_fill_misses(
        noted: &mut Vec<String>,
        frames: &[Vec<String>],
        misses: Option<&FillMisses>,
    ) {
        match misses {
            None | Some(FillMisses::None) => {}
            Some(FillMisses::Missed(names)) => note_misses(noted, names.iter()),
            // The fill's own misses sit in the frame of the first fill it
            // started; while it has none running they are `noted` itself.
            Some(&FillMisses::Filling(fill)) => {
                if let Some(own) = frames.get(fill) {
                    note_misses(noted, own);
                }
            }
        }
    }

    fn merge_lookup(&self, left: LookupResult, right: LookupResult) -> LookupResult {
        match (left, right) {
            (LookupResult::Ambiguous, _) | (_, LookupResult::Ambiguous) => LookupResult::Ambiguous,
            (LookupResult::Missing, hit) | (hit, LookupResult::Missing) => hit,
            (LookupResult::Found(a, ascope, am), LookupResult::Found(b, bscope, bm)) if a == b => {
                // Two import paths to one Membership agree. Distinct
                // aliases with this spelling remain indistinguishable even
                // when they happen to denote the same member element.
                let owning = self.elements[a].owning_relationship;
                if am.or(owning) == bm.or(owning) {
                    LookupResult::Found(a, ascope.or(bscope), am)
                } else {
                    LookupResult::Ambiguous
                }
            }
            (LookupResult::Found(a, ascope, am), LookupResult::Found(b, _, _))
                if !metaclasses_overlap(self.elements[a].ty, self.elements[b].ty) =>
            {
                // KerML Membership::isDistinguishableFrom: concrete sibling
                // metaclasses with equal names do not make the namespace
                // ambiguous. Context-sensitive selection is a later stage;
                // retain the earlier candidate here for stable traversal.
                LookupResult::Found(a, ascope, am)
            }
            (LookupResult::Found(..), LookupResult::Found(..)) => LookupResult::Ambiguous,
        }
    }

    /// The features `e` redefines as lookup reads them: the recorded
    /// written ones, those the positional plan materialized once the model
    /// is semantically ready, and — before that, while references are
    /// still being resolved — those its position pairs it with, read off
    /// its owner's heritage (`positional_redefinition_targets`), so that a
    /// usage's `out fuelEconomy` shadows the definition's it redefines by
    /// position whenever a chain reaches both.
    fn shadowing_redefinition_targets(
        &mut self,
        e: usize,
        read: &mut Vec<usize>,
        memo: &mut parameters::SlotMemo,
    ) -> Vec<usize> {
        let mut targets = self.recorded_redefinition_targets(e, read);
        if let Some(owner) = self.owner_elem(e) {
            for target in self.positional_targets(e, owner, memo) {
                if !targets.contains(&target) {
                    targets.push(target);
                }
            }
        }
        targets
    }

    /// Distinct same-named hits inherited from different bases are not
    /// ambiguous when one (transitively) redefines another (KerML 8.3.3:
    /// a redefined feature's membership is not inherited alongside its
    /// redefinition) — the redefining feature shadows its target. An
    /// overriding usage `part :>> c : N;` inherits `d` both through the
    /// redefinition target's type (the original) and through `N` (the
    /// override); the override wins.
    fn drop_redefined_hits(&mut self, hits: &mut Vec<LookupResult>) {
        let mut found: Vec<usize> = hits
            .iter()
            .filter_map(|h| h.option().map(|(e, _)| e))
            .collect();
        found.sort_unstable();
        found.dedup();
        if found.len() < 2 {
            return;
        }
        // Only a competing inherited lookup needs semantic redefinitions.
        // Ordinary owned-name lookups must not initialize the entire graph.
        self.ensure_positional_redefinitions();
        // The specialization entries whose recorded outcomes decide the
        // shadowing: this lookup depends on what their references missed.
        let mut read = Vec::new();
        let mut memo = parameters::SlotMemo::default();
        let mut shadowed: Vec<usize> = Vec::new();
        for &e in &found {
            let mut stack = self.shadowing_redefinition_targets(e, &mut read, &mut memo);
            let mut seen = HashSet::new();
            while let Some(t) = stack.pop() {
                if !seen.insert(t) {
                    continue;
                }
                if found.contains(&t) && !shadowed.contains(&t) {
                    shadowed.push(t);
                }
                stack.extend(self.shadowing_redefinition_targets(t, &mut read, &mut memo));
            }
        }
        // Implicit redefinition by name (SysML): a usage owned by a type
        // that specializes another candidate's owning type redefines the
        // inherited feature it shares a name with, even without a spelled
        // `:>>` — `part def Sub :> Gen { part item : Special; }` where
        // `Gen` declares `item` too. Only a *strict* one-way conformance
        // shadows (mutual or unrelated owners stay ambiguous), and only a
        // usage-family element overrides (the rule is SysML 7.x usage
        // semantics; KerML features need the explicit spelling).
        let remaining: Vec<usize> = found
            .iter()
            .copied()
            .filter(|e| !shadowed.contains(e))
            .collect();
        // Not a parameter of a behavior or step, a result or an end: those
        // redefine by position (`redefines_by_position`), and a reused
        // name at another position is a collision, which the enumeration
        // keeps and the distinguishability check reports.
        if remaining.len() > 1 {
            for &x in &remaining {
                if !self.elements[x].ty.ends_with("Usage") || self.redefines_by_position(x) {
                    continue;
                }
                let Some(ox) = self.owner_elem(x) else {
                    continue;
                };
                for &y in &remaining {
                    if x == y || shadowed.contains(&y) {
                        continue;
                    }
                    let Some(oy) = self.owner_elem(y) else {
                        continue;
                    };
                    if ox != oy
                        && self.recorded_conforms(ox, oy, &mut read)
                        && !self.recorded_conforms(oy, ox, &mut read)
                    {
                        shadowed.push(y);
                    }
                }
            }
        }
        self.note_spec_misses(read);
        if shadowed.is_empty() {
            return;
        }
        hits.retain(|h| match h.option() {
            Some((e, _)) => !shadowed.contains(&e),
            None => true,
        });
    }

    /// The element owning `e` (the owner of the scope `e` was declared
    /// in). Read-only — safe inside a lookup.
    /// The first scope owner at or above `scope` — the element whose
    /// body the scope (transitively) sits in.
    pub(crate) fn nearest_scope_owner(&self, mut s: usize) -> Option<usize> {
        loop {
            if let Some(o) = self.scopes[s].owner {
                return Some(o);
            }
            s = self.scopes[s].parent?;
        }
    }

    pub(crate) fn owner_elem(&self, e: usize) -> Option<usize> {
        let s = *self.elem_scope.get(&e)?;
        self.scopes[self.scopes[s].parent?].owner
    }

    /// Parameters include membership-defined subjects/actors and ordinary
    /// directed features (`in`, `out`, `inout`) in calculation/action bodies.
    pub(crate) fn is_parameter(&self, e: usize) -> bool {
        self.elements[e].owning_relationship.is_some_and(|r| {
            crate::metaclass::conforms(self.elements[r].ty, "ParameterMembership")
                || (is_feature_membership(self.elements[r].ty)
                    && self.elements[e]
                        .props
                        .get("direction")
                        .and_then(|v| v.as_str())
                        .is_some())
        })
    }

    /// A featured reference stands for another instance. Package-owned
    /// usages also have isComposite=false, but remain ordinary usages
    /// whose type defaults can be evaluated directly.
    pub(crate) fn is_reference_feature(&self, e: usize) -> bool {
        self.is_parameter(e)
            || (self.elements[e]
                .props
                .get("isComposite")
                .and_then(|v| v.as_bool())
                == Some(false)
                && self.elements[e]
                    .owning_relationship
                    .is_some_and(|r| is_feature_membership(self.elements[r].ty)))
    }

    /// Whether `e` declares its own non-default value expression. The
    /// expression is fixed; its result may still depend on unknown inputs.
    pub(crate) fn has_own_fixed_value(&self, e: usize) -> bool {
        self.values.contains_key(&e) && !self.default_values.contains(&e)
    }

    /// Whether evaluating this calculation would require running statements,
    /// including a body inherited through typing or specialization. Walks
    /// the specialization index when one has been built since lowering
    /// settled the table, else scans the table.
    pub(crate) fn calculation_requires_execution(&self, elem: usize) -> bool {
        if self.executable_calculations.is_empty() {
            return false;
        }
        // Lowering can still append entries, which an index built from a
        // partial table would miss.
        let index = self.spec_index.as_ref().filter(|_| self.semantic_ready);
        let mut stack = vec![elem];
        let mut seen = HashSet::new();
        while let Some(e) = stack.pop() {
            if !seen.insert(e) {
                continue;
            }
            if self.executable_calculations.contains(&e) {
                return true;
            }
            // Every entry is one of the four kinds the index keeps, listed
            // per owner in table order: both branches push the same targets
            // in the same order.
            match index {
                Some(index) => {
                    for &i in index.get(&e).into_iter().flatten() {
                        stack.extend(self.spec_resolved.get(i).copied().flatten());
                    }
                }
                None => {
                    for (i, (owner, _, _, _)) in self.spec_targets.iter().enumerate() {
                        if *owner == e {
                            stack.extend(self.spec_resolved.get(i).copied().flatten());
                        }
                    }
                }
            }
        }
        false
    }

    /// [`Self::calculation_requires_execution`], building the
    /// specialization index first once lowering has settled the table —
    /// for callers that may mutate the builder.
    pub(crate) fn indexed_calculation_requires_execution(&mut self, elem: usize) -> bool {
        if self.semantic_ready && !self.executable_calculations.is_empty() {
            self.ensure_spec_index();
        }
        self.calculation_requires_execution(elem)
    }

    /// Is `sup` reachable from `sub` through *recorded* explicit
    /// specialization outcomes? Like [`Self::recorded_redefinition_targets`],
    /// a direct scan with no resolution and no index — this runs inside
    /// `lookup_body` (see that method's doc for why both are off-limits).
    /// The entries whose outcomes it read are added to `read`.
    fn recorded_conforms(&self, sub: usize, sup: usize, read: &mut Vec<usize>) -> bool {
        if sub == sup {
            return true;
        }
        let mut stack = vec![sub];
        let mut seen = HashSet::new();
        while let Some(x) = stack.pop() {
            if !seen.insert(x) {
                continue;
            }
            for (i, (owner, kind, _, _)) in self.spec_targets.iter().enumerate() {
                if *owner == x
                    && matches!(
                        *kind,
                        "FeatureTyping" | "Subclassification" | "Subsetting" | "Redefinition"
                    )
                {
                    read.push(i);
                    if let Some(t) = self.spec_resolved.get(i).copied().flatten() {
                        if t == sup {
                            return true;
                        }
                        if t != x {
                            stack.push(t);
                        }
                    }
                }
            }
        }
        false
    }

    /// The recorded-outcome Redefinition targets of `e`, by direct scan —
    /// no index, no resolution. [`Self::drop_redefined_hits`] runs inside
    /// `lookup_body`, so it must never re-enter resolution (a fallback
    /// resolve of an unrecorded target recurses through the same lookup)
    /// nor build the permanent `spec_index` mid-lowering while
    /// `spec_targets` is still growing. The scan is linear but only runs
    /// on the rare multi-candidate merges.
    /// The entries whose outcomes it read are added to `read`.
    fn recorded_redefinition_targets(&self, e: usize, read: &mut Vec<usize>) -> Vec<usize> {
        let mut out = Vec::new();
        for (i, (owner, kind, _, _)) in self.spec_targets.iter().enumerate() {
            if *owner == e && *kind == "Redefinition" {
                read.push(i);
                if let Some(t) = self.spec_resolved.get(i).copied().flatten() {
                    if t != e && !out.contains(&t) {
                        out.push(t);
                    }
                }
            }
        }
        if self.semantic_ready {
            if let Some(plan) = self.effective_positional_redefinitions() {
                for &target in plan.targets.get(&e).into_iter().flatten() {
                    if !out.contains(&target) {
                        out.push(target);
                    }
                }
            }
        }
        out
    }

    /// [`Self::recorded_redefinition_targets`] through the specialization
    /// index — for callers that run after lowering, when the index is
    /// permanent (enumeration; never `lookup_body`).
    pub(crate) fn indexed_redefinition_targets(&mut self, e: usize) -> Vec<usize> {
        self.ensure_spec_index();
        let mut out = Vec::new();
        if let Some(entries) = self.spec_index.as_ref().unwrap().get(&e) {
            for &i in entries {
                if self.spec_targets[i].1 != "Redefinition" {
                    continue;
                }
                if let Some(t) = self.spec_resolved.get(i).copied().flatten() {
                    if t != e && !out.contains(&t) {
                        out.push(t);
                    }
                }
            }
        }
        out
    }

    /// The element owning scope `s` (the type whose body it is), if any.
    pub(crate) fn scope_owner(&self, s: usize) -> Option<usize> {
        self.scopes[s].owner
    }

    /// The scope lexically enclosing `s`.
    pub(crate) fn scope_parent(&self, s: usize) -> Option<usize> {
        self.scopes[s].parent
    }

    /// The resolved explicit specialization targets of `e` spelled with
    /// one of the relationship `kinds` (`"Subsetting"`, `"Redefinition"`,
    /// `"FeatureTyping"`, `"Subclassification"`), through the
    /// specialization index (same caller restriction as
    /// [`Self::indexed_redefinition_targets`]).
    pub(crate) fn indexed_specialization_targets(
        &mut self,
        e: usize,
        kinds: &[&str],
    ) -> Vec<usize> {
        self.ensure_spec_index();
        let mut out = Vec::new();
        if let Some(entries) = self.spec_index.as_ref().unwrap().get(&e) {
            for &i in entries {
                if !kinds.contains(&self.spec_targets[i].1) {
                    continue;
                }
                if let Some(t) = self.spec_resolved.get(i).copied().flatten() {
                    if t != e && !out.contains(&t) {
                        out.push(t);
                    }
                }
            }
        }
        out
    }

    /// [`Self::recorded_conforms`] through the specialization index (same
    /// caller restriction as [`Self::indexed_redefinition_targets`]).
    pub(crate) fn indexed_conforms(&mut self, sub: usize, sup: usize) -> bool {
        if sub == sup {
            return true;
        }
        self.ensure_spec_index();
        let index = self.spec_index.as_ref().unwrap();
        let mut stack = vec![sub];
        let mut seen = HashSet::new();
        while let Some(x) = stack.pop() {
            if !seen.insert(x) {
                continue;
            }
            for &i in index.get(&x).into_iter().flatten() {
                if let Some(t) = self.spec_resolved.get(i).copied().flatten() {
                    if t == sup {
                        return true;
                    }
                    if t != x {
                        stack.push(t);
                    }
                }
            }
        }
        false
    }

    /// Whether the import relationship `rel` contributes memberships to a
    /// walk running at `access`: the import's own visibility must be
    /// admitted (KerML `nonPrivateMemberships` takes the public and the
    /// protected imports; `expose` is protected). Unspelled means public.
    fn import_admitted(&self, rel: usize, access: LookupAccess) -> bool {
        let vis = match self.elements[rel]
            .props
            .get("visibility")
            .and_then(|a| a.as_str())
        {
            Some("private") => LookupAccess::All,
            Some("protected") => LookupAccess::Protected,
            _ => LookupAccess::Public,
        };
        access.admits(vis)
    }

    fn binding_result(
        &self,
        bindings: Option<&[Binding]>,
        access: LookupAccess,
        exclude: Option<usize>,
        semantic_names: bool,
    ) -> LookupResult {
        let mut result = LookupResult::Missing;
        for binding in bindings.into_iter().flatten().copied() {
            if Some(binding.elem) == exclude
                || (semantic_names && self.reference_locator_has_no_semantic_name(binding.elem))
            {
                continue;
            }
            let widened =
                matches!(self.widen, Some((e, as_if)) if e == binding.elem && access.admits(as_if));
            if !access.admits(binding.visibility) && !widened {
                continue;
            }
            result = self.merge_lookup(
                result,
                LookupResult::Found(binding.elem, binding.sub_scope, None),
            );
        }
        result
    }

    fn lookup_body(
        &mut self,
        s: usize,
        name: &str,
        depth: usize,
        stamp: u64,
        access: LookupAccess,
        semantic_names: bool,
    ) -> LookupResult {
        let access = if self.probing {
            LookupAccess::All
        } else {
            access
        };
        let direct =
            self.binding_result(self.scopes[s].names.get(name), access, self.exclude, false);
        if direct != LookupResult::Missing {
            return direct;
        }
        // An excluded redefining feature's target must not be supplied
        // by anonymous siblings borrowing that same target's name. Keep
        // declared local names and inherited effective names available.
        // This applies equally to pending relationship refs and base-scope
        // lookup, so emitted edges and inherited member lookup agree.
        let circular_effective_name = self
            .exclude
            .and_then(|e| self.elem_scope.get(&e))
            .is_some_and(|&own| {
                self.scopes[own].parent == Some(s)
                    && self.scopes[own].redefinition_names.contains(name)
            });
        if !self.declared_only && !circular_effective_name {
            let effective = self.binding_result(
                self.scopes[s].effective_names.get(name),
                access,
                self.exclude,
                semantic_names,
            );
            if effective != LookupResult::Missing {
                return effective;
            }
        }
        // Clone alias/import targets only on a name match — these run on
        // every scope visit of every failing lookup, so the common
        // no-match case must not allocate.
        let mut aliases = LookupResult::Missing;
        for i in 0..self.scopes[s].aliases.len() {
            if self.scopes[s].aliases[i].0 != name
                || !self.import_admitted(self.scopes[s].aliases[i].2, access)
            {
                continue;
            }
            let target = self.scopes[s].aliases[i].1.clone();
            let origin = self.identity_origin_unit;
            if !self.id_spelled_targets.is_empty() {
                self.identity_origin_unit = Some(
                    self.alias_origins
                        .get(&(s, i))
                        .copied()
                        .unwrap_or_else(|| self.unit_of_scope(s)),
                );
            }
            let resolved = self.resolve_result(s, &target, depth + 1, false);
            self.identity_origin_unit = origin;
            match resolved {
                LookupResult::Found(elem, _, _) => {
                    aliases = self.merge_lookup(
                        aliases,
                        LookupResult::Found(
                            elem,
                            self.elem_scope.get(&elem).copied(),
                            Some(self.scopes[s].aliases[i].2),
                        ),
                    );
                }
                LookupResult::Ambiguous => aliases = LookupResult::Ambiguous,
                LookupResult::Missing => {}
            }
        }
        if aliases != LookupResult::Missing {
            return aliases;
        }
        let mut implied = LookupResult::Missing;
        for &(end_name, elem, sub) in &self.scopes[s].implied_ends {
            if end_name == name && Some(elem) != self.exclude {
                implied = self.merge_lookup(implied, LookupResult::Found(elem, Some(sub), None));
            }
        }
        if implied != LookupResult::Missing {
            return implied;
        }
        let mut imported_members = LookupResult::Missing;
        for i in 0..self.scopes[s].member_imports.len() {
            let entry = &self.scopes[s].member_imports[i];
            if entry.target.segments.last().map(|n| n.value == name) != Some(true)
                || (access == LookupAccess::Public && !entry.is_public)
            {
                continue;
            }
            // An entry must not resolve its own target through itself
            // (`import vehicle::**;` — see `member_import_active`).
            if !self.member_import_active.insert((s, i)) {
                continue;
            }
            let entry = self.scopes[s].member_imports[i].clone();
            let origin = self.set_identity_origin(entry.relationship);
            let resolved = self.resolve_result(s, &entry.target, depth + 1, entry.is_import_all);
            self.identity_origin_unit = origin;
            self.member_import_active.remove(&(s, i));
            match resolved {
                LookupResult::Found(elem, _, membership) => {
                    if self.filters_admit(s, &entry.filters, elem, depth) {
                        if !self.probing {
                            self.used_imports.insert(entry.relationship);
                            self.query_imports.push((entry.relationship, access));
                        }
                        let sub = self.elem_scope.get(&elem).copied();
                        imported_members = self.merge_lookup(
                            imported_members,
                            LookupResult::Found(elem, sub, membership),
                        );
                    }
                }
                LookupResult::Ambiguous => imported_members = LookupResult::Ambiguous,
                LookupResult::Missing => {}
            }
        }
        if imported_members != LookupResult::Missing {
            return imported_members;
        }
        if self.recorded_lookup_ready
            && !self.recorded_lookup_incomplete
            && !self.probing
            && self.widen.is_none()
            && !self.declared_only
        {
            if self.recorded_lookup_graph.is_none() {
                self.recorded_lookup_graph = Some(recorded_lookup::Graph::build(self));
            }
            if let Some((hits, suppressed)) = self.recorded_lookup_graph.as_mut().unwrap().select(
                s,
                name,
                access,
                self.exclude,
                false,
                &mut self.current_misses,
            ) {
                self.recorded_lookup_suppressed |= suppressed;
                return hits.into_iter().fold(LookupResult::Missing, |result, hit| {
                    self.merge_lookup(result, hit)
                });
            }
        }
        let mut hits: Vec<LookupResult> = Vec::new();
        for base in self.base_scopes(s) {
            hits.push(self.lookup_at_with_names(
                base,
                name,
                depth + 1,
                stamp,
                access.inherited(),
                semantic_names,
            ));
        }
        self.drop_redefined_hits(&mut hits);
        let mut inherited = LookupResult::Missing;
        for hit in hits {
            inherited = self.merge_lookup(inherited, hit);
        }
        if inherited != LookupResult::Missing {
            return inherited;
        }
        let mut imported = LookupResult::Missing;
        let imports = self.import_scopes(s);
        for entry in imports.iter() {
            if access == LookupAccess::Public && !entry.is_public {
                continue;
            }
            let hit = if entry.recursive {
                self.lookup_recursive(
                    entry.scope,
                    name,
                    depth + 1,
                    stamp,
                    if entry.is_import_all {
                        LookupAccess::All
                    } else {
                        LookupAccess::Public
                    },
                )
            } else {
                self.lookup_at_with_names(
                    entry.scope,
                    name,
                    depth + 1,
                    stamp,
                    if entry.is_import_all {
                        LookupAccess::All
                    } else {
                        LookupAccess::Public
                    },
                    true,
                )
            };
            match hit {
                LookupResult::Found(elem, sub, membership) => {
                    if self.filters_admit(s, &entry.filters, elem, depth) {
                        if !self.probing {
                            self.used_imports.insert(entry.relationship);
                            self.query_imports.push((entry.relationship, access));
                        }
                        imported =
                            self.merge_lookup(imported, LookupResult::Found(elem, sub, membership));
                    }
                }
                LookupResult::Ambiguous => imported = LookupResult::Ambiguous,
                LookupResult::Missing => {}
            }
        }
        imported
    }

    /// Recursive-import lookup: `name` in `s` or any transitively nested
    /// named scope. All same-precedence candidates are retained; distinct
    /// hits are ambiguous instead of being selected by declaration order.
    fn lookup_recursive(
        &mut self,
        s: usize,
        name: &str,
        depth: usize,
        stamp: u64,
        access: LookupAccess,
    ) -> LookupResult {
        if depth > MAX_RESOLUTION_DEPTH {
            return LookupResult::Missing;
        }
        let access = if self.probing {
            LookupAccess::All
        } else {
            access
        };
        let mut result = self.lookup_at_with_names(s, name, depth, stamp, access, true);
        let key = (s, access as u8);
        let subs = match self.recursive_subs.get(&key) {
            Some(subs) => Arc::clone(subs),
            None => {
                let mut subs: Vec<usize> = self.scopes[s]
                    .names
                    .values()
                    .flatten()
                    .filter(|binding| access.admits(binding.visibility))
                    .filter_map(|binding| binding.sub_scope)
                    .collect();
                subs.sort_unstable();
                subs.dedup();
                let subs: Arc<[usize]> = subs.into();
                self.recursive_subs.insert(key, Arc::clone(&subs));
                subs
            }
        };
        for &sub in subs.iter() {
            let hit = self.lookup_recursive(sub, name, depth + 1, stamp, access);
            result = self.merge_lookup(result, hit);
        }
        result
    }

    /// The scopes made visible in `s` by its namespace imports.
    ///
    /// The cache is permanent, so the computation must not depend on the
    /// ambient recursion depth of whichever lookup touched the scope first:
    /// import targets resolve with a fresh depth budget (a first touch deep
    /// inside a cyclic import walk would otherwise exhaust the guard and
    /// poison the cache with an empty set — making resolution outcomes
    /// depend on file order). Cycle safety comes from the placeholder seed
    /// below and the per-query visit stamps, not from inherited depth.
    fn import_scopes(&mut self, s: usize) -> Arc<Vec<ImportedScope>> {
        if let Some(cached) = &self.import_cache[s] {
            Self::note_fill_misses(
                &mut self.current_misses,
                &self.fill_frames,
                self.import_misses.get(s),
            );
            return Arc::clone(cached);
        }
        // The cache outlives any query: it must never hold what a
        // visibility-blind probe, a widened member or another query's mode
        // would resolve.
        let query = self.enter_fill_mode();
        let fill = self.begin_fill();
        self.set_import_misses(s, FillMisses::Filling(fill));
        let result = self.import_scopes_uncached(s);
        let misses = self.end_fill();
        self.set_import_misses(s, misses);
        self.leave_fill_mode(query);
        result
    }

    fn import_scopes_uncached(&mut self, s: usize) -> Arc<Vec<ImportedScope>> {
        // Placeholder breaks cycles while computing. An import target may
        // itself be visible only through an earlier import of the same
        // scope (`import P::*; import P_Member::*;`), and resolving it
        // re-enters this scope's cache — so iterate to a fixpoint. Each
        // entry resolves with every *other* entry's current outcome seeded
        // (never its own): `import Domain::*;` where the imported package
        // owns a member also named `Domain` must not capture that member
        // through the import itself on the second pass — the
        // namespace-import analogue of `member_import_active`.
        self.import_cache[s] = Some(Arc::new(Vec::new()));
        let imports = self.scopes[s].imports.clone();
        let mut outcomes: Vec<Option<(usize, ImportedScope)>> = vec![None; imports.len()];
        let mut walked: Vec<ImportWalks> = vec![Vec::new(); imports.len()];
        // The resolved outcomes, in import order, as the cache wants them.
        // The vector is handed to the cache and taken back rather than
        // rebuilt per entry, with entry `i`'s own row lifted out for the
        // duration of its resolve — rebuilding it would copy every other
        // entry's outcome once per entry per pass.
        let mut seeds: Vec<ImportedScope> = Vec::new();
        for _ in 0..=imports.len() {
            let mut changed = false;
            for i in 0..imports.len() {
                let entry = imports[i].clone();
                let at = outcomes[..i].iter().filter(|o| o.is_some()).count();
                let mine = outcomes[i].as_ref().map(|_| seeds.remove(at));
                self.import_cache[s] = Some(Arc::new(std::mem::take(&mut seeds)));
                let mark = self.query_imports.len();
                let origin = self.set_identity_origin(entry.relationship);
                let next = self.resolve(s, &entry.target, 0).and_then(|elem| {
                    self.elem_scope.get(&elem).map(|&sc| {
                        (
                            elem,
                            ImportedScope {
                                scope: sc,
                                recursive: entry.recursive,
                                is_import_all: entry.is_import_all,
                                filters: entry.filters.clone(),
                                relationship: entry.relationship,
                                is_public: entry.is_public,
                            },
                        )
                    })
                });
                self.identity_origin_unit = origin;
                walked[i] = self.query_imports.drain(mark..).collect();
                // Re-entry into this scope reads the seed; it never
                // replaces it, so the vector comes back as it was left.
                seeds = self.import_cache[s]
                    .take()
                    .map(|seeds| Arc::try_unwrap(seeds).unwrap_or_else(|shared| (*shared).clone()))
                    .unwrap_or_default();
                if next != outcomes[i] {
                    if let Some((_, scope)) = &next {
                        seeds.insert(at, scope.clone());
                    }
                    outcomes[i] = next;
                    changed = true;
                } else if let Some(mine) = mine {
                    seeds.insert(at, mine);
                }
            }
            if !changed {
                break;
            }
        }
        // Record per-entry element outcomes so the serialized
        // `importedNamespace` reference resolves to exactly what the
        // machinery imported (a plain re-resolve of the pending could
        // capture a member through the completed import).
        let mut result: Vec<ImportedScope> = Vec::new();
        for (i, o) in outcomes.into_iter().enumerate() {
            let key = (s, imports[i].target.to_ref_string());
            self.import_targets.insert(
                key,
                (o.as_ref().map(|(e, _)| *e), std::mem::take(&mut walked[i])),
            );
            if let Some((_, scope)) = o {
                if !result.contains(&scope) {
                    result.push(scope);
                }
            }
        }
        let result = Arc::new(result);
        self.import_cache[s] = Some(Arc::clone(&result));
        result
    }

    /// Record import filter expressions and return their indices into
    /// [`Self::filter_exprs`]. `scope` is where the expressions' names
    /// (metaclass references like `Safety`) resolve from.
    fn record_filters(&mut self, filters: &[Expr], owner: usize, scope: usize) -> Vec<usize> {
        filters
            .iter()
            .map(|f| {
                self.filter_exprs.push((owner, scope, f.clone()));
                self.filters_active.push(false);
                self.filter_exprs.len() - 1
            })
            .collect()
    }

    /// Do the filter conditions guarding an import of scope `s` admit
    /// `elem`? `entry` holds the import's own bracket filters; the scope's
    /// `filter expr;` conditions apply to every import. All conditions
    /// conjoin; a member is hidden only when some condition provably
    /// evaluates to false (undecided conditions keep it visible — checker
    /// policy, and what keeps unsupported filter shapes from breaking
    /// resolution).
    fn filters_admit(&mut self, s: usize, entry: &[usize], elem: usize, depth: usize) -> bool {
        if entry.is_empty() && self.scopes[s].filters.is_empty() {
            return true;
        }
        let scope_fids = self.scopes[s].filters.clone();
        for &fid in entry.iter().chain(&scope_fids) {
            if self.filter_verdict(fid, elem, depth) == Tri::False {
                return false;
            }
        }
        true
    }

    /// Three-valued verdict of one recorded filter condition against one
    /// candidate element. Re-entrant evaluation (a filter whose own name
    /// resolution walks back through the filtered import) answers
    /// undecided.
    fn filter_verdict(&mut self, fid: usize, elem: usize, depth: usize) -> Tri {
        if depth > MAX_RESOLUTION_DEPTH || self.filters_active[fid] {
            return Tri::Unknown;
        }
        self.filters_active[fid] = true;
        let (owner, scope, expr) = self.filter_exprs[fid].clone();
        let origin = self.set_identity_origin(owner);
        let out = self.filter_expr_verdict(&expr, scope, elem, depth);
        self.identity_origin_unit = origin;
        self.filters_active[fid] = false;
        out
    }

    /// Evaluate the supported filter fragment: `@M` metadata/metaclass
    /// tests, `(as M).attr` boolean metadata-attribute access, and the
    /// boolean connectives over them. Everything else is undecided.
    fn filter_expr_verdict(&mut self, expr: &Expr, scope: usize, elem: usize, depth: usize) -> Tri {
        match &expr.kind {
            ExprKind::Literal(Literal::Bool(b)) => {
                if *b {
                    Tri::True
                } else {
                    Tri::False
                }
            }
            ExprKind::Unary {
                op: UnaryOp::Not,
                operand,
            } => match self.filter_expr_verdict(operand, scope, elem, depth) {
                Tri::True => Tri::False,
                Tri::False => Tri::True,
                Tri::Unknown => Tri::Unknown,
            },
            ExprKind::Binary { op, lhs, rhs } => {
                let and_or = match op {
                    BinaryOp::CondAnd | BinaryOp::AndAmp => true,
                    BinaryOp::CondOr | BinaryOp::OrBar => false,
                    _ => return Tri::Unknown,
                };
                let l = self.filter_expr_verdict(lhs, scope, elem, depth);
                // Short-circuit on the deciding operand.
                if (and_or && l == Tri::False) || (!and_or && l == Tri::True) {
                    return l;
                }
                let r = self.filter_expr_verdict(rhs, scope, elem, depth);
                match (and_or, l, r) {
                    (true, Tri::True, v) | (false, Tri::False, v) => v,
                    (true, _, Tri::False) => Tri::False,
                    (false, _, Tri::True) => Tri::True,
                    _ => Tri::Unknown,
                }
            }
            // `@M` — the candidate is annotated by (or is an instance of
            // the metaclass) `M`. Only the implicit-subject spelling is a
            // filter test.
            ExprKind::Classification {
                op: ClassificationOp::AtType,
                operand: None,
                ty,
            } => match ty.as_name() {
                Some(qn) => self.metadata_test(scope, qn, elem, depth),
                None => Tri::Unknown,
            },
            // `(as M).attr` — a boolean attribute of the candidate's `M`
            // metadata annotation.
            ExprKind::ChainStep { target, member } => {
                let ExprKind::Classification {
                    op: ClassificationOp::As,
                    operand: None,
                    ty,
                } = &target.kind
                else {
                    return Tri::Unknown;
                };
                let TargetRef::Name(meta_qn) = &**ty else {
                    return Tri::Unknown;
                };
                let TargetRef::Name(attr) = member else {
                    return Tri::Unknown;
                };
                self.metadata_attr_verdict(scope, meta_qn, attr, elem, depth)
            }
            _ => Tri::Unknown,
        }
    }

    /// `@M`: does `elem` carry a metadata annotation whose typing conforms
    /// to `M` — or, when `M` is a reflection metaclass, is `elem`'s own
    /// metaclass `M` (or a specialization)? Annotations are static model
    /// facts, so an annotation miss against a plain metadata definition is
    /// a definite false.
    fn metadata_test(
        &mut self,
        scope: usize,
        qn: &QualifiedName,
        elem: usize,
        depth: usize,
    ) -> Tri {
        let Some(target) = self.resolve(scope, qn, depth + 1) else {
            return Tri::Unknown;
        };
        self.metadata_conforms(target, elem)
    }

    /// The post-resolution core of `@target`: annotation conformance
    /// first, then the reflection test when `target` is a reflection
    /// metaclass. Shared between import-filter verdicts and expression
    /// evaluation.
    pub(crate) fn metadata_conforms(&mut self, target: usize, elem: usize) -> Tri {
        let metas = self.metadata_of.get(&elem).cloned().unwrap_or_default();
        for m in metas {
            if self.conforms_upward(m, target) {
                return Tri::True;
            }
        }
        if self.is_reflection_target(target) {
            let result = self.metaclass_test(target, elem);
            if result != Tri::False || !self.metadata_associations_incomplete {
                return result;
            }
        }
        if self.metadata_associations_incomplete {
            Tri::Unknown
        } else {
            Tri::False
        }
    }

    /// Is `@target` a *reflection* test — one against the candidate's own
    /// metaclass rather than its annotations? KerML `metaclass` members
    /// always are; the standard `SysML`/`KerML` reflection libraries spell
    /// their metaclasses `metadata def` (e.g. `metadata def PartUsage
    /// specializes ItemUsage` in `SysML.sysml`), so library metadata
    /// definitions owned by those packages count too.
    pub(crate) fn is_reflection_target(&self, target: usize) -> bool {
        match self.elements[target].ty {
            "Metaclass" => true,
            "MetadataDefinition" if target < self.lib_boundary => self
                .top_level_owner(target)
                .and_then(|p| self.effective_name(p))
                .is_some_and(|n| n == "SysML" || n == "KerML"),
            _ => false,
        }
    }

    /// The top-level package the element (with a body scope) is nested in.
    fn top_level_owner(&self, e: usize) -> Option<usize> {
        let mut s = *self.elem_scope.get(&e)?;
        loop {
            let p = self.scopes[s].parent?;
            if self.scopes[p].parent.is_none() {
                return self.scopes[s].owner;
            }
            s = p;
        }
    }

    /// Reflection test: look the candidate's own metaclass name up among
    /// the target metaclass's siblings (the reflection package), falling
    /// back to the standard reflection libraries by name — the two are
    /// explicitly connected (`SysML` metaclasses specialize `KerML`
    /// ones), so a cross-package test is decidable. Walk the explicit
    /// specialization closure; undecided only when the metaclass element
    /// cannot be found at all.
    fn metaclass_test(&mut self, target: usize, elem: usize) -> Tri {
        let ty_name = self.elements[elem].ty;
        let sibling = self
            .elem_scope
            .get(&target)
            .copied()
            .and_then(|t| self.scopes[t].parent)
            .and_then(|p| {
                self.scopes[p]
                    .names
                    .get(ty_name)
                    .and_then(|bindings| bindings.first())
                    .map(|binding| binding.elem)
            });
        let Some(me) = sibling.or_else(|| self.reflection_metaclass(ty_name)) else {
            return Tri::Unknown;
        };
        if self.conforms_upward(me, target) {
            Tri::True
        } else {
            Tri::False
        }
    }

    /// The standard reflection libraries' metaclass element for an
    /// abstract-syntax metaclass name (`SysML::PartDefinition`, KerML
    /// fallback), if the standard library is loaded.
    pub(crate) fn reflection_metaclass(&mut self, ty_name: &str) -> Option<usize> {
        let span = sysmlv2_syntax::Span::new(0, 0);
        ["SysML", "KerML"].iter().find_map(|pkg| {
            let qn = QualifiedName {
                is_global: true,
                segments: vec![
                    Name {
                        value: (*pkg).to_string(),
                        span,
                    },
                    Name {
                        value: ty_name.to_string(),
                        span,
                    },
                ],
                span,
            };
            self.resolve(0, &qn, 0)
        })
    }

    /// `(as M).attr`: the boolean value bound to `attr` inside the
    /// candidate's `M` annotation (`@M { attr = true; }`). Literal
    /// bindings only — anything else is undecided. A candidate without an
    /// `M` annotation is a definite false (the `as` cast is empty).
    fn metadata_attr_verdict(
        &mut self,
        scope: usize,
        meta_qn: &QualifiedName,
        attr: &QualifiedName,
        elem: usize,
        depth: usize,
    ) -> Tri {
        // A missing incoming annotation can change the cardinality of this
        // cast and its selected attribute values, even beside a known value.
        if self.metadata_associations_incomplete {
            return Tri::Unknown;
        }
        let Some(target) = self.resolve(scope, meta_qn, depth + 1) else {
            return Tri::Unknown;
        };
        // Interchange spells a chain member by its declaration identity. A
        // qualified or identity-bound spelling must name the same member of
        // the cast metadata type before its key can select an annotation value.
        // Merely taking the final segment could capture an unrelated feature.
        let key = if attr.is_global
            || attr.segments.len() != 1
            || self.id_spelled_target(scope, attr).is_some()
        {
            let LookupResult::Found(declaration, _, _) =
                self.resolve_result(scope, attr, depth + 1, false)
            else {
                return Tri::Unknown;
            };
            if !crate::metaclass::conforms(self.elements[declaration].ty, "Feature") {
                return Tri::Unknown;
            }
            let Some(key) = self.effective_name(declaration) else {
                return Tri::Unknown;
            };
            let member = Name {
                value: key.clone(),
                span: Span::default(),
            };
            let target_scope = self.elem_scope.get(&target).copied();
            if !matches!(
                self.resolve_rest_result(scope, target, target_scope, &[member], depth + 1, false),
                LookupResult::Found(found, _, _) if found == declaration
            ) {
                return Tri::Unknown;
            }
            key
        } else {
            attr.segments[0].value.clone()
        };
        let metas = self.metadata_of.get(&elem).cloned().unwrap_or_default();
        let mut selected = None;
        for metadata in metas {
            if self.conforms_upward(metadata, target) && selected.replace(metadata).is_some() {
                // This scalar filter evaluator cannot choose one member of a
                // multi-valued metadata cast by declaration order.
                return Tri::Unknown;
            }
        }
        let Some(m) = selected else {
            return Tri::False;
        };
        // The annotation's `attr` member — declared (`isMandatory =
        // true;`) or redefining (`:>> isMandatory = true;`, findable
        // by its effective name).
        let Some(&ms) = self.elem_scope.get(&m) else {
            return Tri::Unknown;
        };
        let f = self.scopes[ms]
            .names
            .get(&key)
            .or_else(|| self.scopes[ms].effective_names.get(&key))
            .and_then(|bindings| match bindings {
                [binding] => Some(binding),
                _ => None,
            })
            .map(|binding| binding.elem);
        let Some(f) = f else {
            return Tri::Unknown;
        };
        match self.values.get(&f).map(|(_, e)| &e.kind) {
            Some(ExprKind::Literal(Literal::Bool(true))) => Tri::True,
            Some(ExprKind::Literal(Literal::Bool(false))) => Tri::False,
            _ => Tri::Unknown,
        }
    }

    /// The body scopes of the specialization bases of the element owning
    /// scope `s` (inherited-member resolution). Base names resolve from the
    /// owning scope's parent.
    fn base_scopes(&mut self, s: usize) -> Vec<usize> {
        self.base_scopes_split(s).0
    }

    /// [`Self::base_scopes`] with the explicit/implied boundary: the
    /// returned `usize` is the count of leading entries resolved from
    /// *written* heritage (specializations, typings, chain bases); the
    /// remainder are implied (Tables 31/32 library bases, binary connector
    /// bases, positional parameter, end and result redefinitions, semantic
    /// metadata).
    pub(crate) fn base_scopes_split(&mut self, s: usize) -> (Vec<usize>, usize) {
        if let Some(cached) = &self.base_cache[s] {
            Self::note_fill_misses(
                &mut self.current_misses,
                &self.fill_frames,
                self.base_misses.get(s),
            );
            return self.with_dynamic_scope_bases(s, cached.clone());
        }
        // As for `import_scopes`: cached bases never come from a probe or
        // another query's mode, and the import walks that resolve the base
        // names belong to the specialization's own reference sites, not to
        // whichever lookup first fills the cache — a prepared library
        // rebuilds its base caches under the user's lookups, and cold and
        // warm builds must record identical sites.
        let query = self.enter_fill_mode();
        let mark = self.query_imports.len();
        let origin = self.identity_origin_unit;
        if let Some(owner) = self.scopes[s].owner {
            self.set_identity_origin(owner);
        }
        let fill = self.begin_fill();
        self.set_base_misses(s, FillMisses::Filling(fill));
        let result = self.base_scopes_uncached(s);
        let misses = self.end_fill();
        self.set_base_misses(s, misses);
        self.identity_origin_unit = origin;
        self.query_imports.truncate(mark);
        self.leave_fill_mode(query);
        self.with_dynamic_scope_bases(s, result)
    }

    fn with_dynamic_scope_bases(
        &self,
        scope: usize,
        (mut bases, explicit): (Vec<usize>, usize),
    ) -> (Vec<usize>, usize) {
        // Keep cached construction bases static. The read-only accepted overlay
        // adds real existing scopes without contaminating later static planning.
        if let Some(owner) = self.scopes[scope].owner {
            if let Some(plan) = self.effective_dynamic_plan() {
                for target in plan.added_bases.get(&owner).into_iter().flatten() {
                    if let Some(&target_scope) = self.elem_scope.get(target) {
                        if target_scope != scope && !bases.contains(&target_scope) {
                            bases.push(target_scope);
                        }
                    }
                }
            }
        }
        (bases, explicit)
    }

    fn base_scopes_uncached(&mut self, s: usize) -> (Vec<usize>, usize) {
        self.base_cache[s] = Some((Vec::new(), 0));
        let bases = self.scopes[s].bases.clone();
        let implied_bases = self.scopes[s].implied_bases.clone();
        let chain_bases = self.scopes[s].chain_bases.clone();
        let from = self.scopes[s].parent.unwrap_or(s);
        let mut result = Vec::new();
        // A base name must never resolve to the element being specialized
        // itself (its effective name may equal the base's name).
        let saved = self.exclude;
        let saved_header = self.redefinition_lookup_owner.take();
        let saved_header_base = self.redefinition_lookup_base.take();
        self.exclude = self.scopes[s].owner;
        // A redefinition remains a base even when the declaring Type's
        // filtered inherited view suppresses its target. Use the same header
        // context as the stored relationship, not ordinary member lookup.
        let redefinitions: Vec<_> = if let Some(owner) = self.scopes[s].owner.filter(|&owner| {
            self.elements[owner]
                .owned_relationships
                .iter()
                .any(|&r| self.elements[r].ty == "Redefinition")
        }) {
            if self.semantic_ready {
                self.ensure_spec_index();
                self.spec_index
                    .as_ref()
                    .unwrap()
                    .get(&owner)
                    .into_iter()
                    .flatten()
                    .filter(|&&i| self.spec_targets[i].1 == "Redefinition")
                    .map(|&i| self.spec_targets[i].3.clone())
                    .collect()
            } else {
                // Lowering can still append specialization declarations;
                // never establish its permanent index from a partial prefix.
                self.spec_targets
                    .iter()
                    .filter(|(source, kind, _, _)| *source == owner && *kind == "Redefinition")
                    .map(|(_, _, _, qn)| qn.clone())
                    .collect()
            }
        } else {
            Vec::new()
        };
        let header_owner = self.scopes[s]
            .owner
            .and_then(|owner| self.owner_elem(owner));
        // Fresh depth budget: the cache is permanent, so outcomes must not
        // depend on the first caller's recursion depth (see import_scopes).
        for qn in &bases {
            self.redefinition_lookup_owner = redefinitions
                .iter()
                .any(|target| target == qn)
                .then_some(header_owner)
                .flatten();
            if let Some(elem) = self.resolve(from, qn, 0) {
                if let Some(&sc) = self.elem_scope.get(&elem) {
                    if sc != s {
                        result.push(sc);
                    }
                }
            }
        }
        self.redefinition_lookup_owner = None;
        self.redefinition_lookup_base = None;
        // A chain-written base contributes the chain's *last* link: the
        // spine resolves like any reference (member steps in the previous
        // target's scope), and the landed feature's members are inherited.
        for links in &chain_bases {
            let empty = QualifiedName {
                is_global: false,
                segments: Vec::new(),
                span: Span::default(),
            };
            if let Some(elem) = self.resolve_chain_member(from, Some(links), &empty) {
                if let Some(&sc) = self.elem_scope.get(&elem) {
                    if sc != s && !result.contains(&sc) {
                        result.push(sc);
                    }
                }
            }
        }
        let explicit = result.len();
        for qn in &implied_bases {
            if let Some(elem) = self.resolve(from, qn, 0) {
                if let [package, member] = qn.segments.as_slice() {
                    if let Some(role) = implied::binary_role_name(&package.value, &member.value) {
                        if !self.binary_lookup_target(elem, role) {
                            continue;
                        }
                    }
                }
                if let Some(&sc) = self.elem_scope.get(&elem) {
                    if sc != s && !result.contains(&sc) {
                        result.push(sc);
                    }
                }
            }
        }
        // A parameter, end or result redefines its general's feature at the
        // same position by implication (KerML
        // `checkFeatureParameterRedefinition`, `checkFeatureEndRedefinition`,
        // `checkFeatureResultRedefinition`), and a redefining feature inherits
        // the members of what it redefines: `in q;` declared first under
        // `action def Swapped :> A` reads the members of `A`'s first
        // parameter, whatever that one is named. The pairing is read off the
        // owning type's heritage here; the implied relationships materialize
        // the same edges for the whole model later.
        if let Some(feature) = self.scopes[s].owner {
            if let Some(owner) = self.owner_elem(feature) {
                for target in self.positional_redefinition_targets(feature, owner) {
                    if let Some(&sc) = self.elem_scope.get(&target) {
                        if sc != s && !result.contains(&sc) {
                            result.push(sc);
                        }
                    }
                }
            }
        }
        self.exclude = saved;
        // Semantic metadata (KerML 9.2 metaobject semantics): an element
        // annotated with a SemanticMetadata subtype implicitly specializes
        // the metadata's `baseType` value — resolution-only, like the
        // Table 31/32 implied library bases, so the base's members resolve
        // as inherited members of the annotated element's body.
        if let Some(owner) = self.scopes[s].owner {
            for t in self.semantic_base_targets(owner, 0) {
                if let Some(&sc) = self.elem_scope.get(&t) {
                    if sc != s && !result.contains(&sc) {
                        result.push(sc);
                    }
                }
            }
        }
        self.redefinition_lookup_owner = saved_header;
        self.redefinition_lookup_base = saved_header_base;
        self.base_cache[s] = Some((result.clone(), explicit));
        (result, explicit)
    }

    /// Enumerate the members scope `s` inherits through its heritage —
    /// the resolver's own walk ([`Self::base_scopes_split`]) run for
    /// enumeration instead of name lookup. Returns
    /// `(member element, contributing scope)` pairs — the heritage scope
    /// or import that made the member visible — in direct-base order,
    /// composing each base's public/protected contributions and already
    /// filtered inheritance, plus the inherited **alias Membership**
    /// relationship indices from the heritage scopes and from every
    /// imported scope the walk visited, and whether a depth guard cut
    /// the walk short. Memoized per (scope, `include_implied`).
    ///
    /// Inheritance semantics (KerML `inheritableMemberships` /
    /// `nonPrivateMemberships`, enumerated):
    /// - private memberships do not inherit; **public and protected imported
    ///   memberships re-export** through heritage (membership imports,
    ///   namespace imports incl. `::**`, re-export chains, filter
    ///   conditions applied);
    /// - removal is **redefinition-driven, not name-driven**: a member is
    ///   dropped when another *inherited* candidate (transitively)
    ///   redefines it, when its own redefinition closure meets a feature
    ///   **directly** redefined by an **owned** feature (the OCL
    ///   `ownedFeature.redefinition.redefinedFeature` intersection — one
    ///   hop from the owned side, by the normative text; redefiners of
    ///   unrelated branches never suppress each other), or under SysML's
    ///   implicit same-name usage redefinition
    ///   (strict one-way owner conformance — see `drop_redefined_hits`).
    ///   Same-name members of unrelated heritage branches are all
    ///   retained (name lookup answers ambiguous; the memberships still
    ///   inherit);
    /// - `include_implied` extends the walk over the implied heritage
    ///   (Tables 31/32 library bases, binary connector bases, positional
    ///   parameter, end and result redefinitions, semantic metadata) at
    ///   *every* level.
    ///
    /// Ordinary member identities and alias memberships are kept separately
    /// internally, then projected to Membership handles by the public API.
    /// Redefinition removal compares their distinct Membership identities;
    /// aliases to Features participate as both candidates and blockers.
    /// Acyclic inheritance is evaluated bottom-up without a depth cap;
    /// cycles use a bounded partial walk and are reported as incomplete.
    pub(crate) fn inherited_bindings(
        &mut self,
        s: usize,
        include_implied: bool,
    ) -> Arc<InheritedBindings> {
        if include_implied && self.semantic_ready {
            self.ensure_positional_redefinitions();
        }
        if let Some(hit) = self.inherited_cache.get(&(s, include_implied)) {
            return Arc::clone(hit);
        }
        if let Some(shared) = self.library_inherited_bindings(s, include_implied) {
            self.inherited_cache
                .insert((s, include_implied), Arc::clone(&shared));
            return shared;
        }
        // Enumeration resolves bases and import targets the way lookup
        // does; that must not count as a use of the model's imports.
        // (Its lookups may also add root-miss guard entries, which only
        // make the prepared-path guard more conservative.)
        let used_imports = self.used_imports.clone();
        let query_imports = std::mem::take(&mut self.query_imports);
        // A scope with no members, imports or aliases of its own
        // contributes nothing to its enumeration but its heritage.
        let heritage_key = {
            let sc = &self.scopes[s];
            (sc.names.values().next().is_none()
                && sc.effective_names.values().next().is_none()
                && sc.imports.is_empty()
                && sc.member_imports.is_empty()
                && sc.aliases.is_empty()
                && sc.implied_ends.is_empty()
                && sc
                    .owner
                    .is_none_or(|e| self.owned_member_elems(e, false).is_empty()))
            .then(|| (self.base_scopes_split(s).0, include_implied))
        };
        let result = match heritage_key
            .as_ref()
            .and_then(|k| self.inherited_by_heritage.get(k))
        {
            Some(hit) => Arc::clone(hit),
            None => {
                let result = Arc::new(self.inherited_bindings_uncached(s, include_implied));
                if !result.truncated && !result.incomplete {
                    if let Some(k) = heritage_key {
                        self.inherited_by_heritage.insert(k, Arc::clone(&result));
                    }
                }
                result
            }
        };
        self.used_imports = used_imports;
        self.query_imports = query_imports;
        if !result.truncated && !result.incomplete {
            self.inherited_cache
                .insert((s, include_implied), Arc::clone(&result));
        }
        result
    }

    fn inherited_bindings_uncached(
        &mut self,
        s: usize,
        include_implied: bool,
    ) -> InheritedBindings {
        // Build dependencies iteratively, then let each base contribute its
        // already-filtered inherited memberships. Pooling raw ancestors loses
        // removals made by intermediate types and changes positional ordering.
        let mut state = HashMap::new();
        let mut order = Vec::new();
        let mut pending = vec![(s, false)];
        while let Some((scope, exiting)) = pending.pop() {
            if self.inherited_cache.contains_key(&(scope, include_implied)) {
                continue;
            }
            // A library base's memberships as the library's own build gives
            // them; a cut-short or incomplete one is walked here as before.
            if scope != s && !exiting {
                if let Some(shared) = self.library_inherited_bindings(scope, include_implied) {
                    self.inherited_cache
                        .insert((scope, include_implied), shared);
                    continue;
                }
            }
            if exiting {
                state.insert(scope, 2);
                order.push(scope);
                continue;
            }
            match state.get(&scope) {
                Some(2) => continue,
                Some(1) => {
                    let mut result = self.inherited_bindings_walk(s, include_implied, true);
                    // Cycle exclusions depend on the requested root. Never
                    // reuse a root-relative partial result as a base's closure.
                    result.incomplete = true;
                    return result;
                }
                _ => {}
            }
            state.insert(scope, 1);
            pending.push((scope, true));
            let (mut bases, explicit) = self.base_scopes_split(scope);
            if !include_implied {
                bases.truncate(explicit);
            }
            pending.extend(bases.into_iter().rev().map(|b| (b, false)));
        }
        let mut result = InheritedBindings::default();
        for scope in order {
            let value = self.inherited_bindings_walk(scope, include_implied, false);
            if scope == s {
                result = value;
            } else {
                self.inherited_cache
                    .insert((scope, include_implied), Arc::new(value));
            }
        }
        result
    }

    fn inherited_bindings_walk(
        &mut self,
        s: usize,
        include_implied: bool,
        recursive: bool,
    ) -> InheritedBindings {
        let heritage = |b: &mut Self, sc: usize| {
            let (all, explicit) = b.base_scopes_split(sc);
            if include_implied {
                all
            } else {
                all[..explicit].to_vec()
            }
        };
        let mut visited: HashSet<usize> = HashSet::from([s]);
        let mut pending: Vec<(usize, usize)> = heritage(self, s)
            .into_iter()
            .rev()
            .map(|b| (b, 1))
            .collect();
        // (element, contributing scope), each direct base before the next.
        let mut collected: Vec<(usize, usize)> = Vec::new();
        let mut seen_elems: HashSet<usize> = HashSet::new();
        let mut alias_rels: Vec<usize> = Vec::new();
        let mut membership_order = Vec::new();
        let mut truncated = false;
        let mut incomplete = false;
        while let Some((base, depth)) = pending.pop() {
            if visited.contains(&base) {
                continue;
            }
            if depth > MAX_RESOLUTION_DEPTH {
                truncated = true;
                continue;
            }
            visited.insert(base);
            // Preserve direct-base order; order each base's own members by
            // declaration, including members with no declared name.
            let mut found: Vec<(usize, usize)> = Vec::new();
            {
                let b = base;
                let begin = found.len();
                if let Some(owner) = self.scopes[b].owner {
                    found.extend(
                        self.owned_member_elems(owner, false)
                            .into_iter()
                            .filter(|&e| {
                                self.elements[e].owning_relationship.is_none_or(|r| {
                                    self.elements[r]
                                        .props
                                        .get("visibility")
                                        .and_then(|v| v.as_str())
                                        != Some("private")
                                })
                            })
                            .map(|e| (e, b)),
                    );
                }
                for map in [&self.scopes[b].names, &self.scopes[b].effective_names] {
                    for bindings in map.values() {
                        for binding in bindings {
                            if binding.visibility == LookupAccess::All {
                                continue; // private: not inherited
                            }
                            found.push((binding.elem, b));
                        }
                    }
                }
                found[begin..].sort_by_key(|&(e, scope)| {
                    let protected = self.elements[e].owning_relationship.is_some_and(|r| {
                        self.elements[r]
                            .props
                            .get("visibility")
                            .and_then(|v| v.as_str())
                            == Some("protected")
                    });
                    (protected, e, scope)
                });
                // nonPrivateMemberships unions public owned/imported,
                // protected owned/imported, then inherited memberships. An
                // import's visibility controls admission, not its target's.
                let owned = std::mem::take(&mut found);
                for access in [LookupAccess::Public, LookupAccess::Protected] {
                    let own: Vec<_> = owned
                        .iter()
                        .copied()
                        .filter(|&(e, _)| {
                            self.elements[e]
                                .owning_relationship
                                .is_none_or(|r| self.import_admitted(r, access))
                        })
                        .collect();
                    let mut own_order: Vec<_> = own
                        .iter()
                        .filter_map(|&(e, _)| self.elements[e].owning_relationship)
                        .collect();
                    let mut aliases = Vec::new();
                    self.scope_alias_rels(b, access, &[], &mut aliases);
                    own_order.extend(aliases.iter().copied());
                    own_order.sort_unstable();
                    own_order.dedup();
                    membership_order.extend(own_order);
                    alias_rels.extend(aliases);
                    found.extend(own);
                    let mut imported = InheritedBindings::default();
                    membership_order.extend(self.imported_bindings(
                        b,
                        include_implied,
                        access,
                        &mut imported,
                    ));
                    found.extend(imported.members);
                    alias_rels.extend(imported.alias_rels);
                    truncated |= imported.truncated;
                    incomplete |= imported.incomplete;
                }
                if !recursive {
                    if let Some(inherited) = self.inherited_cache.get(&(b, include_implied)) {
                        membership_order.extend(inherited.membership_order.iter().copied());
                        found.extend(inherited.members.iter().copied());
                        alias_rels.extend(inherited.alias_rels.iter().copied());
                        truncated |= inherited.truncated;
                        incomplete |= inherited.incomplete;
                    }
                }
            }
            for (elem, scope) in found {
                if seen_elems.insert(elem) {
                    collected.push((elem, scope));
                }
            }
            if recursive {
                pending.extend(
                    heritage(self, base)
                        .into_iter()
                        .rev()
                        .map(|b| (b, depth + 1)),
                );
            }
        }
        self.reduce_inherited_bindings(
            self.scopes[s].owner,
            include_implied,
            InheritedBindings {
                members: collected,
                alias_rels,
                membership_order,
                truncated,
                incomplete,
                implicit_redefinitions: Vec::new(),
            },
            None,
        )
    }

    /// Preserve compatibility bookkeeping around the shared identity reducer.
    fn reduce_inherited_bindings(
        &mut self,
        owner: Option<usize>,
        include_implied: bool,
        mut candidates: InheritedBindings,
        steps: Option<&mut usize>,
    ) -> InheritedBindings {
        let reduced = self.reduce_membership_projection(
            owner,
            include_implied,
            MembershipProjection {
                membership_order: std::mem::take(&mut candidates.membership_order),
                truncated: candidates.truncated,
                incomplete: candidates.incomplete,
                implicit_redefinitions: Vec::new(),
            },
            steps,
        );
        let retained: HashSet<_> = reduced.membership_order.iter().copied().collect();
        let mut seen_members = HashSet::new();
        candidates.members.retain(|(member, _)| {
            self.elements[*member]
                .owning_relationship
                .is_some_and(|membership| retained.contains(&membership))
                && seen_members.insert(*member)
        });
        let mut seen_aliases = HashSet::new();
        candidates
            .alias_rels
            .retain(|membership| retained.contains(membership) && seen_aliases.insert(*membership));
        candidates.membership_order = reduced.membership_order;
        candidates.truncated = reduced.truncated;
        candidates.incomplete = reduced.incomplete;
        candidates.implicit_redefinitions = reduced.implicit_redefinitions;
        candidates
    }

    /// One redefinition reducer for global and context-sensitive candidates.
    fn reduce_membership_projection(
        &mut self,
        owner: Option<usize>,
        include_implied: bool,
        candidates: MembershipProjection,
        mut steps: Option<&mut usize>,
    ) -> MembershipProjection {
        let MembershipProjection {
            mut membership_order,
            truncated,
            mut incomplete,
            ..
        } = candidates;
        macro_rules! charge {
            ($count:expr) => {
                if let Some(steps) = steps.as_deref_mut() {
                    *steps = steps.saturating_add($count);
                    if *steps > crate::eval::MAX_STEPS {
                        return MembershipProjection {
                            truncated: true,
                            incomplete: true,
                            ..Default::default()
                        };
                    }
                }
            };
        }
        charge!(membership_order.len());
        if include_implied {
            incomplete |= owner.is_some_and(|e| {
                !self.dynamic_evidence_current(e)
                    || self
                        .effective_positional_redefinitions()
                        .is_some_and(|plan| plan.incomplete.contains(&e))
            });
        }
        // An empty inherited projection cannot be shadowed by an owned member.
        // Keep the readiness side effect of the ordinary path when planning
        // has not yet run; once ready, no owned-feature scan is necessary.
        if membership_order.is_empty()
            && (!include_implied
                || !self.semantic_ready
                || self.effective_positional_redefinitions().is_some())
        {
            return MembershipProjection {
                membership_order,
                truncated,
                incomplete,
                implicit_redefinitions: Vec::new(),
            };
        }
        // Membership identity, not memberElement identity, distinguishes
        // contributors. Resolve each unique relationship's target once; the
        // same target may intentionally participate through distinct aliases.
        let mut seen_memberships = HashSet::new();
        membership_order.retain(|m| seen_memberships.insert(*m));
        let resolved: Vec<_> = membership_order
            .iter()
            .map(|&membership| (membership, self.stored_membership_member(membership)))
            .collect();
        let mut seen_members = HashSet::new();
        let collected: Vec<_> = resolved
            .iter()
            .filter_map(|&(membership, member)| {
                let member = member?;
                (self.elements[member].owning_relationship == Some(membership)
                    && seen_members.insert(member))
                .then_some(member)
            })
            .collect();
        let mut feature_memberships: HashMap<usize, usize> = HashMap::new();
        for &(_, member) in &resolved {
            charge!(1);
            if let Some(e) = member {
                if crate::metaclass::conforms(self.elements[e].ty, "Feature") {
                    *feature_memberships.entry(e).or_default() += 1;
                }
            } else {
                incomplete = true;
            }
        }
        // Only actual owned Features seed the direct-target intersection.
        // An owned alias of a redefining Feature is not an ownedFeature.
        let owned = owner
            .map(|owner| self.owned_member_elems(owner, true))
            .unwrap_or_default();
        let mut owned_direct = HashSet::new();
        for &e in &owned {
            charge!(1);
            owned_direct.extend(self.semantic_redefinition_targets(e, include_implied));
        }
        let mut shadow = HashSet::new();
        // Reuse traversal storage; closures are consumed immediately rather
        // than retained once per Feature. Every candidate remains a blocker
        // even when another candidate or an owned Feature removes it.
        let mut closure = HashSet::new();
        let mut stack = Vec::new();
        for (&e, &count) in &feature_memberships {
            closure.clear();
            stack.push(e);
            let mut intersects_owned = false;
            while let Some(t) = stack.pop() {
                charge!(1);
                if !closure.insert(t) {
                    continue;
                }
                // Exclude only the candidate's own Membership, including in
                // a cycle. Another Membership of the same Feature still counts.
                if t != e || count > 1 {
                    shadow.insert(t);
                }
                intersects_owned |= owned_direct.contains(&t);
                stack.extend(self.semantic_redefinition_targets(t, include_implied));
            }
            if intersects_owned {
                shadow.insert(e);
            }
        }
        // (c) SysML implicit same-name usage redefinition: a usage-family
        //     member whose owning type strictly conforms over another
        //     candidate's owner redefines the same-named candidate
        //     without a spelled `:>>`. Not a parameter of a behavior or
        //     step, a result or an end: those redefine by position
        //     (`redefines_by_position`), and a reused name at another
        //     position is a collision, not a redefinition.
        let mut by_name: HashMap<&str, Vec<usize>> = HashMap::new();
        for e in owned.iter().copied().chain(collected.iter().copied()) {
            // Both spellings share the lookup name space: a short name can
            // shadow (or be shadowed by) a declared name, as in lookup.
            for key in ["declaredName", "declaredShortName"] {
                if let Some(n) = self.elements[e].props.get(key).and_then(|a| a.as_str()) {
                    by_name.entry(n).or_default().push(e);
                }
            }
        }
        let groups: Vec<Vec<usize>> = by_name.into_values().filter(|g| g.len() > 1).collect();
        let mut implicit_redefinitions: Vec<(usize, usize)> = Vec::new();
        for group in groups {
            for &x in &group {
                if !self.elements[x].ty.ends_with("Usage")
                    || shadow.contains(&x)
                    || self.redefines_by_position(x)
                {
                    continue;
                }
                let Some(ox) = self.owner_elem(x) else {
                    continue;
                };
                for &y in &group {
                    charge!(1);
                    if x == y || shadow.contains(&y) {
                        continue;
                    }
                    let Some(oy) = self.owner_elem(y) else {
                        continue;
                    };
                    if ox != oy && self.indexed_conforms(ox, oy) && !self.indexed_conforms(oy, ox) {
                        shadow.insert(y);
                        implicit_redefinitions.push((y, x));
                    }
                }
            }
        }
        membership_order.clear();
        membership_order.extend(resolved.into_iter().filter_map(|(membership, member)| {
            member
                .is_none_or(|member| !shadow.contains(&member))
                .then_some(membership)
        }));
        implicit_redefinitions.sort_unstable();
        implicit_redefinitions.dedup();
        MembershipProjection {
            membership_order,
            truncated,
            incomplete,
            implicit_redefinitions,
        }
    }

    /// The bindings scope `b`'s imports contribute at `admitted` access —
    /// the enumeration counterpart of `lookup_body`'s import arms:
    /// `Protected` for an inheriting type (public and protected imports
    /// of the base re-export, private ones do not — KerML
    /// `nonPrivateMemberships`), `All` for the namespace's own
    /// `importedMembership` (every owned import, whatever its
    /// visibility). Member elements, alias Membership relationship
    /// indices and the truncation flag land in `out`; the returned indices
    /// retain Membership discovery order for the ordered import closure.
    fn imported_bindings(
        &mut self,
        b: usize,
        include_implied: bool,
        admitted: LookupAccess,
        out: &mut InheritedBindings,
    ) -> Vec<usize> {
        let mut context = MembershipContext::default();
        self.imported_bindings_with_context(b, include_implied, admitted, out, &mut context)
    }

    fn imported_bindings_with_context(
        &mut self,
        b: usize,
        include_implied: bool,
        admitted: LookupAccess,
        out: &mut InheritedBindings,
        context: &mut MembershipContext,
    ) -> Vec<usize> {
        if include_implied && self.semantic_ready {
            self.ensure_positional_redefinitions();
        }
        let mut order = Vec::new();
        let mut seen = HashMap::new();
        let mut excluded = vec![b];
        self.collect_import_edges(
            b,
            admitted,
            include_implied,
            &[],
            &mut excluded,
            &mut seen,
            out,
            &mut order,
            0,
            admitted == LookupAccess::All,
            context,
        );
        if admitted == LookupAccess::All {
            // Namespace::importedMemberships is distinct from the raw
            // visibility-specific operation used for re-export/inheritance.
            if let Some(owner) = self.scopes[b].owner {
                let (retained, incomplete) = self.distinguishable_import_memberships(owner, order);
                order = retained;
                out.incomplete |= incomplete;
            }
            // Package::importedMemberships filters the Namespace result.
            let filters = self.scopes[b].filters.clone();
            order.retain(|&rel| {
                self.stored_membership_member(rel)
                    .is_none_or(|member| self.import_filter_set_admits(&filters, member))
            });
            let retained: HashSet<_> = order.iter().copied().collect();
            out.members.retain(|&(element, _)| {
                self.elements[element]
                    .owning_relationship
                    .is_some_and(|rel| retained.contains(&rel))
            });
            out.alias_rels.retain(|rel| retained.contains(rel));
        }
        order
    }

    /// Import relationships in declaration order. A recursive membership
    /// import contributes its Membership before its namespace traversal.
    #[allow(clippy::too_many_arguments)]
    fn collect_import_edges(
        &mut self,
        sc: usize,
        access: LookupAccess,
        include_implied: bool,
        chain: &[(usize, Vec<usize>)],
        excluded: &mut Vec<usize>,
        seen: &mut HashMap<ImportVisit, ImportProjection>,
        out: &mut InheritedBindings,
        order: &mut Vec<usize>,
        depth: usize,
        defer_package_filters: bool,
        context: &mut MembershipContext,
    ) -> Option<Vec<usize>> {
        if !context.charge(1 + self.scopes[sc].member_imports.len() + self.scopes[sc].imports.len())
        {
            out.incomplete = true;
            out.truncated = true;
            return None;
        }
        let members = self.scopes[sc].member_imports.clone();
        let namespaces = self.import_scopes(sc);
        let resolved_imports: HashSet<_> =
            namespaces.iter().map(|entry| entry.relationship).collect();
        if self.scopes[sc].imports.iter().any(|entry| {
            self.import_admitted(entry.relationship, access)
                && !resolved_imports.contains(&entry.relationship)
        }) {
            out.incomplete = true;
        }
        let mut entries: Vec<_> = members
            .iter()
            .enumerate()
            .map(|(i, e)| (e.relationship, false, i))
            .chain(
                namespaces
                    .iter()
                    .enumerate()
                    .map(|(i, e)| (e.relationship, true, i)),
            )
            .collect();
        entries.sort_unstable();
        let mut blocked = Vec::new();
        let mut complete = true;
        for (rel, namespace, i) in entries {
            if !self.import_admitted(rel, access) {
                continue;
            }
            if namespace {
                let entry = &namespaces[i];
                let sub_access = if entry.is_import_all {
                    LookupAccess::All
                } else {
                    LookupAccess::Public
                };
                let mut chain2 = chain.to_vec();
                let mut filters = entry.filters.clone();
                if !defer_package_filters {
                    filters.extend_from_slice(&self.scopes[sc].filters);
                }
                chain2.push((sc, filters));
                match self.collect_import_scope(
                    excluded,
                    entry.scope,
                    sub_access,
                    entry.recursive,
                    include_implied,
                    &chain2,
                    seen,
                    out,
                    order,
                    depth,
                    context,
                ) {
                    Some(bounds) => blocked.extend(bounds),
                    None => complete = false,
                }
            } else {
                let entry = &members[i];
                let origin = self.set_identity_origin(entry.relationship);
                let resolved = self.resolve_result(sc, &entry.target, 0, entry.is_import_all);
                self.identity_origin_unit = origin;
                if let LookupResult::Found(elem, _, membership) = resolved {
                    let local_filters = self.scopes[sc].filters.clone();
                    if self.import_filter_set_admits(&entry.filters, elem)
                        && (defer_package_filters
                            || self.import_filter_set_admits(&local_filters, elem))
                        && self.chain_admits(chain, elem)
                    {
                        if let Some(rel) = membership {
                            out.alias_rels.push(rel);
                        } else {
                            out.members.push((elem, sc));
                        }
                        if let Some(rel) = membership.or(self.elements[elem].owning_relationship) {
                            order.push(rel);
                        } else {
                            out.incomplete = true;
                        }
                    }
                } else {
                    out.incomplete = true;
                }
            }
        }
        complete.then_some(blocked)
    }

    /// Enumerate what one namespace-import edge makes visible in scope
    /// `sc` — the faithful mirror of `lookup_at` + `lookup_recursive`
    /// over that scope:
    /// - owned memberships, including unnamed members, admitted by `access`;
    /// - alias memberships admitted by `access`;
    /// - the scope's own member imports and namespace re-exports, each
    ///   under **its own** policy (filters, `import all`, `::**`) — an
    ///   outer entry never overrides a nested entry's policy; filter
    ///   conditions **compose** along the path (`chain`);
    /// - the scope's heritage (`base_scopes`), at inherited access —
    ///   lookup resolves inherited members through an import, so
    ///   enumeration follows;
    /// - for `::**` (`recursive`), descent into owned members' scopes.
    #[allow(clippy::too_many_arguments)]
    fn collect_import_scope(
        &mut self,
        excluded: &mut Vec<usize>,
        sc: usize,
        access: LookupAccess,
        recursive: bool,
        include_implied: bool,
        chain: &[(usize, Vec<usize>)],
        seen: &mut HashMap<ImportVisit, ImportProjection>,
        out: &mut InheritedBindings,
        order: &mut Vec<usize>,
        depth: usize,
        context: &mut MembershipContext,
    ) -> Option<Vec<usize>> {
        // Namespace::importedMemberships seeds excluded with itself.
        // This exclusion is independent of access, recursion and filters.
        if !context.charge(1) {
            out.incomplete = true;
            out.truncated = true;
            return None;
        }
        let is_excluded = excluded.contains(&sc);
        if !context.namespace_test(sc, is_excluded) {
            out.incomplete = true;
            out.truncated = true;
            return None;
        }
        if is_excluded {
            return Some(vec![sc]);
        }
        // The filter chain is part of the visit key: a scope first reached
        // through a filtered path must still be visited through an
        // unfiltered one, whatever the import order.
        let mut signature: Vec<(usize, usize)> = chain
            .iter()
            .flat_map(|(scope, filters)| filters.iter().map(move |&f| (*scope, f)))
            .collect();
        signature.sort_unstable();
        signature.dedup();
        let key: ImportVisit = (sc, access as u8, recursive, signature);
        // Redefinition removal is nonmonotonic in namespace exclusions.
        // Reuse only when every consulted inclusion/exclusion decision agrees,
        // rather than assuming that more exclusions can only remove results.
        if let Some(visit) = seen.get(&key) {
            if context.reuse_namespace(visit, excluded) {
                return Some(visit.blocked.clone());
            }
        }
        // A cut visit is not recorded, so a shorter path found later can
        // still complete it; only a genuinely new visit counts as a cut.
        if depth > MAX_RESOLUTION_DEPTH {
            out.truncated = true;
            return None;
        }
        context.begin_namespace(excluded);
        excluded.push(sc);
        let mut blocked = Vec::new();
        let mut complete = true;
        let own_cost = self.scopes[sc]
            .owner
            .map_or(0, |owner| self.elements[owner].owned_relationships.len());
        if !context.charge(own_cost + self.scopes[sc].aliases.len()) {
            excluded.pop();
            context.finish_namespace(Vec::new());
            out.incomplete = true;
            out.truncated = true;
            return None;
        }
        // Visibility is a property of Memberships, including unnamed ones;
        // lookup's name index alone cannot enumerate this collection.
        let mut candidates: Vec<usize> = if let Some(owner) = self.scopes[sc].owner {
            self.owned_member_elems(owner, false)
                .into_iter()
                .filter(|&elem| {
                    self.elements[elem]
                        .owning_relationship
                        .is_some_and(|rel| self.import_admitted(rel, access))
                })
                .collect()
        } else {
            self.scopes[sc]
                .names
                .values()
                .chain(self.scopes[sc].effective_names.values())
                .flatten()
                .filter(|b| access.admits(b.visibility))
                .map(|b| b.elem)
                .collect()
        };
        candidates.sort_unstable();
        candidates.dedup();
        let mut subs: Vec<usize> = if recursive {
            candidates
                .iter()
                .filter_map(|e| self.elem_scope.get(e).copied())
                .collect()
        } else {
            Vec::new()
        };
        let mut own_memberships = Vec::new();
        for elem in candidates {
            if self.chain_admits(chain, elem) {
                out.members.push((elem, sc));
                if let Some(rel) = self.elements[elem].owning_relationship {
                    own_memberships.push(rel);
                }
            }
        }
        let alias_start = out.alias_rels.len();
        self.scope_alias_rels(sc, access, chain, &mut out.alias_rels);
        own_memberships.extend_from_slice(&out.alias_rels[alias_start..]);
        own_memberships.sort_unstable();
        own_memberships.dedup();
        order.extend(own_memberships);
        match self.collect_import_edges(
            sc,
            access,
            include_implied,
            chain,
            excluded,
            seen,
            out,
            order,
            depth + 1,
            false,
            context,
        ) {
            Some(bounds) => blocked.extend(bounds),
            None => complete = false,
        }
        if recursive {
            subs.sort_unstable();
            subs.dedup();
            for sub in subs {
                let result = self.collect_import_scope(
                    excluded,
                    sub,
                    access,
                    true,
                    include_implied,
                    chain,
                    seen,
                    out,
                    order,
                    depth + 1,
                    context,
                );
                match result {
                    Some(bounds) => blocked.extend(bounds),
                    None => complete = false,
                }
            }
        }
        if self.scopes[sc]
            .owner
            .is_some_and(|owner| crate::metaclass::conforms(self.elements[owner].ty, "Type"))
        {
            let family = context.new_type_family();
            let inherited = self.contextual_inherited_bindings(
                self.scopes[sc].owner.expect("checked Type owner"),
                include_implied && !recursive,
                excluded,
                &[],
                family,
                context,
                0,
            );
            out.truncated |= inherited.truncated;
            out.incomplete |= inherited.incomplete;
            complete &= !inherited.truncated;
            for &membership in &inherited.membership_order {
                if !context.charge(1) {
                    out.incomplete = true;
                    out.truncated = true;
                    complete = false;
                    break;
                }
                if !self.import_admitted(membership, access) {
                    continue;
                }
                let Some(element) = self.stored_membership_member(membership) else {
                    out.incomplete = true;
                    continue;
                };
                if !self.chain_admits(chain, element) {
                    continue;
                }
                if self.elements[element].owning_relationship == Some(membership) {
                    out.members.push((element, sc));
                } else {
                    out.alias_rels.push(membership);
                }
                order.push(membership);
            }
        }
        excluded.pop();
        if !complete {
            context.finish_namespace(Vec::new());
            return None;
        }
        // This visit always excludes itself; only caller-supplied boundary
        // exclusions affect whether its completed result is reusable.
        blocked.retain(|&s| s != sc);
        blocked.sort_unstable();
        blocked.dedup();
        let visit = context.finish_namespace(blocked.clone());
        seen.insert(key, visit);
        Some(blocked)
    }

    /// Every filter set along an import path admits `elem`.
    fn chain_admits(&mut self, chain: &[(usize, Vec<usize>)], elem: usize) -> bool {
        chain
            .iter()
            .all(|(_, filters)| self.import_filter_set_admits(filters, elem))
    }

    fn import_filter_set_admits(&mut self, filters: &[usize], elem: usize) -> bool {
        filters
            .iter()
            .all(|&filter| self.filter_verdict(filter, elem, 0) != Tri::False)
    }

    /// Alias Membership relationships of scope `sc` admitted by `access`
    /// (an alias's declared visibility maps like a member's) and by the
    /// filter chain, tested against the alias's resolved target when it
    /// resolves. Appended in relationship-creation order.
    fn scope_alias_rels(
        &mut self,
        sc: usize,
        access: LookupAccess,
        chain: &[(usize, Vec<usize>)],
        alias_out: &mut Vec<usize>,
    ) {
        let Some(owner) = self.scopes[sc].owner else {
            return;
        };
        let rels: Vec<usize> = self.elements[owner]
            .owned_relationships
            .iter()
            .copied()
            .filter(|&r| {
                if self.elements[r].ty != "Membership" {
                    return false;
                }
                let named = self.elements[r]
                    .props
                    .get("memberName")
                    .is_some_and(|v| !v.is_null())
                    || self.elements[r]
                        .props
                        .get("memberShortName")
                        .is_some_and(|v| !v.is_null());
                if !named {
                    return false;
                }
                let vis = match self.elements[r]
                    .props
                    .get("visibility")
                    .and_then(|a| a.as_str())
                {
                    Some("private") => LookupAccess::All,
                    Some("protected") => LookupAccess::Protected,
                    _ => LookupAccess::Public,
                };
                access.admits(vis)
            })
            .collect();
        for r in rels {
            if let Some(target) = self.alias_target_elem(r) {
                if !self.chain_admits(chain, target) {
                    continue;
                }
            }
            alias_out.push(r);
        }
    }

    /// The element an alias Membership's resolved `memberElement`
    /// denotes, when it resolved to an in-model id.
    fn alias_target_elem(&mut self, rel: usize) -> Option<usize> {
        let id = self.elements[rel]
            .props
            .get("memberElement")?
            .as_reference()?;
        self.element_index_of_uuid(id)
    }

    /// The bases used by member lookup, including implicit library bases and
    /// semantic metadata. This query preserves lookup's self-exclusion rules.
    pub(crate) fn context_bases(&mut self, e: usize) -> Vec<usize> {
        let Some(&scope) = self.elem_scope.get(&e) else {
            return Vec::new();
        };
        self.base_scopes(scope)
            .into_iter()
            .filter_map(|s| self.scopes[s].owner)
            .collect()
    }

    /// The resolved `baseType` targets of the element's SemanticMetadata
    /// annotations: for each annotation whose metadata definition conforms
    /// to `Metaobjects::SemanticMetadata`, resolve the definition's
    /// `baseType` feature value (idiomatically `f meta SysML::Usage` or
    /// `f as SysML::Usage` — the feature reference under the cast) in the
    /// scope that value was written in. Never serialized — consumed by
    /// [`Self::base_scopes`] as implied bases only.
    fn semantic_base_targets(&mut self, elem: usize, depth: usize) -> Vec<usize> {
        if depth > MAX_RESOLUTION_DEPTH {
            return Vec::new();
        }
        let metas = match self.metadata_of.get(&elem) {
            Some(m) if !m.is_empty() => m.clone(),
            _ => return Vec::new(),
        };
        let (saved_ex, saved_dm) = (self.exclude, self.declared_only);
        (self.exclude, self.declared_only) = (None, false);
        let mut out = Vec::new();
        if let Some(sem) = self.semantic_metadata_elem() {
            for m in metas {
                for def in self.direct_typing_elems(m) {
                    if !self.conforms_upward(def, sem) {
                        continue;
                    }
                    let Some(&def_scope) = self.elem_scope.get(&def) else {
                        continue;
                    };
                    // The definition's `baseType` member: the `:>> baseType`
                    // redefinition is an unnamed feature found by effective
                    // name, or inherited (valueless) when not redefined.
                    let Some((bt, _)) = self.lookup(def_scope, "baseType", depth + 1) else {
                        continue;
                    };
                    let target = match self.values.get(&bt) {
                        Some((vs, expr)) => {
                            semantic_base_ref(&expr.kind).map(|qn| (*vs, qn.clone()))
                        }
                        None => None,
                    };
                    let Some((vscope, qn)) = target else { continue };
                    if let Some(t) = self.resolve(vscope, &qn, depth + 1) {
                        if t != elem && !out.contains(&t) {
                            out.push(t);
                        }
                    }
                }
            }
        }
        (self.exclude, self.declared_only) = (saved_ex, saved_dm);
        out
    }

    /// `Metaobjects::SemanticMetadata`, resolved from the global namespace
    /// once and memoized. Callers must have neutralized `exclude` /
    /// `declared_only` (the memo must not capture a mode-dependent miss).
    fn semantic_metadata_elem(&mut self) -> Option<usize> {
        if let Some(memo) = self.semantic_metadata {
            Self::note_fill_misses(
                &mut self.current_misses,
                &self.fill_frames,
                Some(&self.semantic_metadata_misses),
            );
            return memo;
        }
        self.begin_fill();
        let r = self.resolve(0, &lib_qn("Metaobjects::SemanticMetadata"), 0);
        self.semantic_metadata_misses = self.end_fill();
        self.semantic_metadata = Some(r);
        r
    }

    /// The resolved targets of the element's *explicit* typings and
    /// specializations (`FeatureTyping`, `Subclassification`,
    /// `Subsetting`, `Redefinition`) — the upward edges a declared-type
    /// walk follows. Implied library bases are not included. The
    /// owner-index is built lazily once and shared.
    pub(crate) fn explicit_supertype_elems(&mut self, e: usize) -> Vec<usize> {
        let mut out = Vec::new();
        for (_, t) in self.explicit_specialization_elems(e) {
            if !out.contains(&t) {
                out.push(t);
            }
        }
        out
    }

    /// [`Self::explicit_supertype_elems`] keeping each edge's
    /// relationship metaclass — the graphical notation distinguishes
    /// typing, subclassification, subsetting, and redefinition arrows.
    pub(crate) fn explicit_specialization_elems(&mut self, e: usize) -> Vec<(&'static str, usize)> {
        self.ensure_spec_index();
        let indices = self.spec_index.as_ref().unwrap().get(&e).cloned();
        let mut out: Vec<(&'static str, usize)> = Vec::new();
        for i in indices.unwrap_or_default() {
            // Prefer the outcome recorded during pending resolution: it
            // carries the original exclusion semantics (`part redefines x`
            // must land on the *inherited* x, not the redefining part's
            // own registered name — a plain re-resolve self-loops there).
            let recorded = self.spec_resolved.get(i).copied().flatten();
            self.note_spec_misses([i]);
            let t = match recorded {
                Some(t) => Some(t),
                // Redefinition resolution is identity-bound: its original
                // exclusion/header/callee-chain context cannot be recreated
                // by an ordinary lexical lookup. An unresolved outcome stays
                // missing, including a named argument with a lexical namesake.
                None if self.spec_targets[i].1 == "Redefinition" => None,
                None => {
                    let (_, _, scope, qn) = self.spec_targets[i].clone();
                    self.resolve(scope, &qn, 0)
                }
            };
            if let Some(t) = t {
                let kind = self.spec_targets[i].1;
                if t != e && !out.contains(&(kind, t)) {
                    out.push((kind, t));
                }
            }
        }
        out
    }

    /// Build the owner → specialization-entry index once. Reading the
    /// index never resolves anything — safe to call from inside a lookup.
    /// A build whose specialization rows below its own are its prepared
    /// library's frozen rows indexes only its own over the library's index.
    fn ensure_spec_index(&mut self) {
        if self.spec_index.is_none() {
            let library = self.prepared_from.as_ref().filter(|prepared| {
                self.spec_targets.base_untouched()
                    && Arc::ptr_eq(
                        self.spec_targets.base_arc(),
                        prepared.builder.spec_targets.base_arc(),
                    )
            });
            let (mut index, from) = match library {
                Some(prepared) => (
                    crate::layered::LayeredMap::over(Arc::clone(prepared.library_spec_index())),
                    self.spec_targets.base_len(),
                ),
                None => (crate::layered::LayeredMap::default(), 0),
            };
            self.index_spec_rows(from..self.spec_targets.len(), &mut index);
            self.spec_index = Some(index);
        }
    }

    /// Index the explicit typing and specialization rows `rows` of
    /// `spec_targets` by owner into `index`, after the entries it holds.
    pub(crate) fn index_spec_rows(
        &self,
        rows: std::ops::Range<usize>,
        index: &mut crate::layered::LayeredMap<usize, Vec<usize>>,
    ) {
        for i in rows {
            let (owner, kind, _, _) = &self.spec_targets[i];
            if matches!(
                *kind,
                "FeatureTyping" | "Subclassification" | "Subsetting" | "Redefinition"
            ) {
                index.entry(*owner).or_default().push(i);
            }
        }
    }

    /// Is `target` reachable from `e` through the explicit
    /// typing/specialization closure? (Implied library bases are not
    /// walked — for user-owned targets the explicit closure is
    /// complete; conformance to library types may ride implied bases.)
    pub(crate) fn conforms_upward(&mut self, e: usize, target: usize) -> bool {
        if e == target {
            return true;
        }
        let mut seen = std::collections::HashSet::new();
        let mut stack = vec![e];
        while let Some(s) = stack.pop() {
            if !seen.insert(s) {
                continue;
            }
            for t in self.explicit_supertype_elems(s) {
                if t == target {
                    return true;
                }
                stack.push(t);
            }
        }
        false
    }

    /// Like [`Self::conforms_upward`], but the walk also follows the
    /// implied specializations that semantic-metadata annotations create
    /// (KerML 9.2 metaobject semantics): an element annotated with a
    /// `SemanticMetadata` subtype specializes the metadata's `baseType`
    /// value, so classification must reach the base type through the
    /// annotation even though no explicit edge is recorded. The
    /// metadata-definition conformance test inside
    /// [`Self::semantic_base_targets`] stays on the explicit walk, so the
    /// mutual recursion terminates.
    pub(crate) fn conforms_upward_semantic(&mut self, e: usize, target: usize) -> bool {
        if e == target {
            return true;
        }
        let mut seen = std::collections::HashSet::new();
        let mut stack = vec![e];
        while let Some(s) = stack.pop() {
            if !seen.insert(s) {
                continue;
            }
            for t in self.explicit_supertype_elems(s) {
                if t == target {
                    return true;
                }
                stack.push(t);
            }
            for t in self.semantic_base_targets(s, 0) {
                if t == target {
                    return true;
                }
                stack.push(t);
            }
        }
        false
    }

    /// The scope an element's own declaration lives in (the parent of its
    /// body scope) — where its feature-value expression would resolve
    /// from, had it one.
    pub(crate) fn owner_scope_of(&self, e: usize) -> Option<usize> {
        self.elem_scope.get(&e).and_then(|&s| self.scopes[s].parent)
    }

    /// The resolved targets of the element's explicit `FeatureTyping`s
    /// (its declared types), in declaration order.
    pub(crate) fn direct_typing_elems(&mut self, e: usize) -> Vec<usize> {
        self.explicit_supertype_elems(e); // ensure the index exists
        let indices = self
            .spec_index
            .as_ref()
            .and_then(|m| m.get(&e))
            .cloned()
            .unwrap_or_default();
        let mut out = Vec::new();
        for i in indices {
            let (_, kind, scope, qn) = self.spec_targets[i].clone();
            if kind == "FeatureTyping" {
                self.note_spec_misses([i]);
                let target = self
                    .spec_resolved
                    .get(i)
                    .copied()
                    .flatten()
                    .or_else(|| self.resolve(scope, &qn, 0));
                if let Some(t) = target {
                    if !out.contains(&t) {
                        out.push(t);
                    }
                }
            }
        }
        out
    }

    /// The resolved targets of the element's explicit `Redefinition`s,
    /// read from the builder's recorded pending outcomes (`spec_resolved`
    /// — a redefinition target must resolve with the owner excluded, so
    /// re-resolving here would self-hit).
    pub(crate) fn redefinition_target_elems(&mut self, e: usize) -> Vec<usize> {
        self.ensure_spec_index();
        let indices = self
            .spec_index
            .as_ref()
            .and_then(|m| m.get(&e))
            .cloned()
            .unwrap_or_default();
        let mut out = Vec::new();
        for i in indices {
            if self.spec_targets[i].1 == "Redefinition" {
                self.note_spec_misses([i]);
                if let Some(t) = self.spec_resolved.get(i).copied().flatten() {
                    if t != e && !out.contains(&t) {
                        out.push(t);
                    }
                }
            }
        }
        out
    }

    /// The element's explicit `Subsetting`s written as names (`:> a`), each
    /// as (resolved target, scope its spelling resolves from, spelling), from
    /// the builder's recorded pending outcomes. Reference subsettings,
    /// redefinitions and chain-written targets are not among them.
    pub(crate) fn written_subsetting_targets(
        &mut self,
        e: usize,
    ) -> Vec<(usize, usize, QualifiedName)> {
        self.ensure_spec_index();
        let indices = self
            .spec_index
            .as_ref()
            .and_then(|m| m.get(&e))
            .cloned()
            .unwrap_or_default();
        let mut out = Vec::new();
        for i in indices {
            if self.spec_targets[i].1 != "Subsetting" {
                continue;
            }
            self.note_spec_misses([i]);
            if let Some(t) = self.spec_resolved.get(i).copied().flatten() {
                if t != e {
                    let (_, _, scope, qn) = &self.spec_targets[i];
                    out.push((t, *scope, qn.clone()));
                }
            }
        }
        out
    }

    /// Find the local multiplicity, declining an invalid second declaration.
    /// Body constraints participate even if their ranges are not indexed.
    pub(crate) fn local_multiplicity(&self, e: usize) -> Option<Option<usize>> {
        let mut members = self.elements[e]
            .owned_relationships
            .iter()
            .filter(|&&r| crate::metaclass::conforms(self.elements[r].ty, "Membership"))
            .flat_map(|&r| self.elements[r].children.iter())
            .filter(|&&child| crate::metaclass::conforms(self.elements[child].ty, "Multiplicity"))
            .copied();
        let first = members.next();
        members.next().is_none().then_some(first)
    }

    /// Reuse the supported positional redefinition graph for parameters and
    /// connector ends. Incomplete owner heritage cannot establish bounds.
    pub(crate) fn cardinality_positional_targets(
        &mut self,
        e: usize,
        steps: &mut usize,
    ) -> Option<Vec<usize>> {
        if !self.dynamic_evidence_current(e) {
            return None;
        }
        if (self.is_parameter(e)
            || self.elements[e]
                .props
                .get("isEnd")
                .and_then(|v| v.as_bool())
                == Some(true))
            && self.effective_positional_redefinitions().is_none()
            && !self.ensure_positional_redefinitions_with_budget(steps)
        {
            return None;
        }
        let targets = self.completed_positional_targets(e)?;
        *steps = steps.saturating_add(targets.len());
        (*steps <= crate::eval::MAX_STEPS).then(|| targets.to_vec())
    }

    /// Read only a completed positional snapshot. Bounded readers borrow the
    /// targets and charge before traversal without entering legacy planning.
    fn completed_positional_targets(&self, e: usize) -> Option<&[usize]> {
        if !self.dynamic_evidence_current(e) {
            return None;
        }
        if !self.is_parameter(e)
            && self.elements[e]
                .props
                .get("isEnd")
                .and_then(|v| v.as_bool())
                != Some(true)
        {
            return Some(&[]);
        }
        let plan = self.effective_positional_redefinitions()?;
        if self
            .owner_elem(e)
            .is_some_and(|owner| plan.incomplete.contains(&owner))
        {
            return None;
        }
        Some(plan.targets.get(&e).map_or(&[][..], Vec::as_slice))
    }

    /// SysML's implicit singleton declaration applies only to structural usages
    /// owned by a definition or usage, without explicit owned subsettings.
    /// Call only after ruling out explicit bounds and owned subsettings.
    pub(crate) fn default_cardinality(&self, e: usize) -> (i128, Option<i128>) {
        let conforms = crate::metaclass::conforms;
        let featured = self.owner_elem(e).is_some_and(|owner| {
            let ty = self.elements[owner].ty;
            conforms(ty, "Definition") || conforms(ty, "Usage")
        });
        if self.structural_usage(e) && featured {
            (1, Some(1))
        } else {
            (0, None)
        }
    }

    /// An attribute, port or item usage (connections excluded): the usages
    /// SysML declares singletons when a definition or usage owns them.
    pub(crate) fn structural_usage(&self, e: usize) -> bool {
        let conforms = crate::metaclass::conforms;
        let ty = self.elements[e].ty;
        conforms(ty, "AttributeUsage")
            || conforms(ty, "PortUsage")
            || (conforms(ty, "ItemUsage") && !conforms(ty, "ConnectionUsage"))
    }

    pub(crate) fn resolve_rest(
        &mut self,
        elem: usize,
        scope: Option<usize>,
        rest: &[Name],
        depth: usize,
    ) -> Option<usize> {
        match self.resolve_rest_result(scope.unwrap_or(0), elem, scope, rest, depth, false) {
            LookupResult::Found(found, _, _) => Some(found),
            LookupResult::Missing | LookupResult::Ambiguous => None,
        }
    }

    fn scope_is_within(&self, mut scope: usize, ancestor: usize) -> bool {
        loop {
            if scope == ancestor {
                return true;
            }
            let Some(parent) = self.scopes[scope].parent else {
                return false;
            };
            scope = parent;
        }
    }

    /// Whether `origin` is nested in a feature/type whose specialization
    /// closure contains the element owning `target`. This is the KerML
    /// protected-membership access case, including a nested feature typed
    /// by a specializing type.
    fn scope_can_access_protected(&mut self, mut origin: usize, target: usize) -> bool {
        loop {
            if self.scope_reaches_base(origin, target, &mut HashSet::new()) {
                return true;
            }
            let Some(parent) = self.scopes[origin].parent else {
                return false;
            };
            origin = parent;
        }
    }

    fn scope_reaches_base(
        &mut self,
        scope: usize,
        target: usize,
        seen: &mut HashSet<usize>,
    ) -> bool {
        if !seen.insert(scope) {
            return false;
        }
        for base in self.base_scopes(scope) {
            if base == target || self.scope_reaches_base(base, target, seen) {
                return true;
            }
        }
        false
    }

    fn resolve_rest_result(
        &mut self,
        origin: usize,
        elem: usize,
        scope: Option<usize>,
        rest: &[Name],
        depth: usize,
        allow_last_non_public: bool,
    ) -> LookupResult {
        if rest.is_empty() {
            return LookupResult::Found(elem, scope, None);
        }
        if let Some(id) = self.id_spelled_name(&rest[0]) {
            if depth > MAX_RESOLUTION_DEPTH {
                return LookupResult::Missing;
            }
            let Some(next) = self.element_index_of_uuid(id) else {
                return LookupResult::Missing;
            };
            let next_scope = self.elem_scope.get(&next).copied();
            return self.resolve_rest_result(
                origin,
                next,
                next_scope,
                &rest[1..],
                depth + 1,
                allow_last_non_public,
            );
        }
        let Some(scope) = scope else {
            return LookupResult::Missing;
        };
        let access =
            if self.scope_is_within(origin, scope) || (allow_last_non_public && rest.len() == 1) {
                LookupAccess::All
            } else if self.scope_can_access_protected(origin, scope) {
                LookupAccess::Protected
            } else {
                LookupAccess::Public
            };
        let stamp = self.next_stamp();
        match self.lookup_at(scope, &rest[0].value, depth + 1, stamp, access) {
            hit @ LookupResult::Found(next, next_scope, _) => {
                if rest.len() == 1 {
                    hit
                } else {
                    self.resolve_rest_result(
                        origin,
                        next,
                        next_scope,
                        &rest[1..],
                        depth + 1,
                        allow_last_non_public,
                    )
                }
            }
            other => other,
        }
    }
}

fn qn_span(qn: &QualifiedName) -> Span {
    Span {
        start: qn.segments.first().map_or(0, |n| n.span.start),
        end: qn.segments.last().map_or(0, |n| n.span.end),
    }
}

/// A reference property value: the element with identity `id`.
fn id_ref(id: Uuid) -> crate::properties::Atom {
    crate::properties::Atom::reference(id)
}

/// A reference in interchange form.
fn id_value(id: Uuid) -> Value {
    json!({ "@id": id.to_string() })
}

/// Non-Type namespaces: owners whose usage members lower as
/// OwningMembership rather than FeatureMembership (the document root
/// Namespace, packages, and library packages).
fn is_namespace_metaclass(ty: &str) -> bool {
    matches!(ty, "Namespace" | "Package" | "LibraryPackage")
}

/// The subset of the normative abstract-syntax generalization graph needed
/// for name distinguishability among element metaclasses produced by the
/// textual lowering. Sibling metaclasses are distinguishable; a metaclass
/// and any of its supertypes are not.
fn direct_metaclass_supers(ty: &str) -> &'static [&'static str] {
    match ty {
        // KerML classifiers/features.
        "Classifier" => &["Type"],
        "Class" | "DataType" | "Association" | "Behavior" | "Metaclass" => &["Classifier"],
        "Structure" => &["Class"],
        "AssociationStructure" => &["Association", "Structure"],
        "Interaction" => &["Behavior", "Association"],
        "Function" => &["Behavior"],
        "Predicate" => &["Function"],
        "Step" | "Expression" | "Connector" => &["Feature"],
        "BooleanExpression" => &["Expression"],
        "Invariant" => &["BooleanExpression"],

        // SysML definition hierarchy relevant to concrete textual kinds.
        "OccurrenceDefinition" => &["Definition"],
        "ItemDefinition" => &["OccurrenceDefinition"],
        "PartDefinition" => &["ItemDefinition"],
        "PortDefinition" => &["OccurrenceDefinition"],
        "AnalysisCaseDefinition" | "VerificationCaseDefinition" | "UseCaseDefinition" => {
            &["CaseDefinition"]
        }
        "ConcernDefinition" | "ViewpointDefinition" => &["RequirementDefinition"],
        "AttributeDefinition"
        | "MetadataDefinition"
        | "ConnectionDefinition"
        | "InterfaceDefinition"
        | "AllocationDefinition"
        | "FlowDefinition"
        | "ActionDefinition"
        | "StateDefinition"
        | "CalculationDefinition"
        | "ConstraintDefinition"
        | "RequirementDefinition"
        | "CaseDefinition"
        | "ViewDefinition"
        | "RenderingDefinition"
        | "EnumerationDefinition" => &["Definition"],

        // SysML usage hierarchy and reference-usage specializations.
        "OccurrenceUsage" => &["Usage"],
        "ItemUsage" => &["OccurrenceUsage"],
        "PartUsage" => &["ItemUsage"],
        "PortUsage" | "EventOccurrenceUsage" => &["OccurrenceUsage"],
        "PerformActionUsage" => &["ActionUsage"],
        "ExhibitStateUsage" => &["StateUsage"],
        "IncludeUseCaseUsage" => &["UseCaseUsage"],
        "SatisfyRequirementUsage" => &["RequirementUsage"],
        "AssertConstraintUsage" => &["ConstraintUsage"],
        "AnalysisCaseUsage" | "VerificationCaseUsage" | "UseCaseUsage" => &["CaseUsage"],
        "ConcernUsage" | "ViewpointUsage" => &["RequirementUsage"],
        "SuccessionFlowUsage" => &["FlowUsage"],
        "AcceptActionUsage"
        | "SendActionUsage"
        | "AssignmentActionUsage"
        | "TerminateActionUsage"
        | "IfActionUsage"
        | "WhileLoopActionUsage"
        | "ForLoopActionUsage"
        | "MergeNode"
        | "DecisionNode"
        | "JoinNode"
        | "ForkNode" => &["ActionUsage"],
        "AttributeUsage"
        | "EnumerationUsage"
        | "MetadataUsage"
        | "ConnectionUsage"
        | "InterfaceUsage"
        | "AllocationUsage"
        | "FlowUsage"
        | "ActionUsage"
        | "StateUsage"
        | "CalculationUsage"
        | "ConstraintUsage"
        | "RequirementUsage"
        | "CaseUsage"
        | "ViewUsage"
        | "RenderingUsage"
        | "ReferenceUsage"
        | "SuccessionAsUsage"
        | "BindingConnectorAsUsage"
        | "TransitionUsage" => &["Usage"],
        _ => &[],
    }
}

fn metaclass_conforms_name(specific: &str, general: &str) -> bool {
    if specific == general {
        return true;
    }
    direct_metaclass_supers(specific)
        .iter()
        .any(|parent| metaclass_conforms_name(parent, general))
}

fn metaclasses_overlap(a: &str, b: &str) -> bool {
    metaclass_conforms_name(a, b) || metaclass_conforms_name(b, a)
}

/// If this member is a bare end usage (`end name? ::> target;` with nothing
/// else), return it as a connector end.
fn bare_end_member(m: &Member) -> Option<ConnectorEnd> {
    let MemberKind::Usage(u) = &m.kind else {
        return None;
    };
    let p = &u.prefix;
    let d = &u.declaration;
    let bare_prefix = p.is_end
        && p.direction.is_none()
        && !p.is_derived
        && !p.is_abstract
        && !p.is_variation
        && !p.is_constant
        && !p.is_ref
        && !p.is_individual
        && p.portion.is_none()
        && !p.is_variant
        && p.metadata.is_empty()
        && p.end_cross.is_none()
        && !p.is_composite
        && !p.is_portion
        && !p.is_variable
        && !p.is_type_member;
    if !bare_prefix
        || u.value.is_some()
        || u.body.is_some()
        || m.visibility.is_some()
        || m.leading_then
        || m.leading_then_multiplicity.is_some()
        || d.id.short_name.is_some()
        || d.is_ordered
        || d.is_nonunique
        || d.is_sufficient
        || d.conjugates.is_some()
        || d.chains.is_some()
        || d.inverse_of.is_some()
        || !d.featured_by.is_empty()
        || !matches!(u.detail, UsageDetail::None)
    {
        return None;
    }
    let [FeatureSpecialization::References(target)] = d.specializations.as_slice() else {
        return None;
    };
    Some(ConnectorEnd {
        multiplicity: d.multiplicity.clone(),
        name: d.id.name.clone(),
        target: target.clone(),
    })
}

/// Build a [`QualifiedName`] for a library path like `"Parts::Part"`.
/// The left spine of a feature-chain expression as link names, when it is
/// statically a plain name chain (`subscribing.sub` → `[subscribing, sub]`).
/// `None` for computed targets (invocations, indexing, …) or global names.
fn chain_spine(e: &Expr) -> Option<Vec<QualifiedName>> {
    match &e.kind {
        // A `$::`-rooted first link is as statically known as a plain one
        // (`resolve` honors the rooting) — the lift prints chain spines
        // globally, and both spellings must resolve through the same
        // chain-context path or the round-trip flips resolution outcomes.
        ExprKind::Ref(qn) => Some(vec![qn.clone()]),
        // A cast spine types the step: the member of `(x as T).m` — and of
        // the filter idiom `(as T).m` — is a member of `T`.
        ExprKind::Classification {
            op: ClassificationOp::As,
            ty,
            ..
        } => Some(vec![ty.as_name()?.clone()]),
        ExprKind::ChainStep { target, member } => {
            let mut spine = chain_spine(target)?;
            let TargetRef::Name(qn) = member else {
                return None;
            };
            if qn.is_global {
                return None;
            }
            spine.push(qn.clone());
            Some(spine)
        }
        _ => None,
    }
}

/// The plain (possibly qualified) name a reference-like expression spells,
/// if it is one — used for the `meta`/`@@` left side, which the grammar
/// restricts to a metadata reference.
fn expr_target_name(e: &Expr) -> Option<QualifiedName> {
    match &e.kind {
        ExprKind::Ref(qn) => Some(qn.clone()),
        _ => None,
    }
}

/// Comment/documentation body normalization, matching the pilot
/// implementation's `ElementUtil.processCommentBody`: drop the `/*`/`*/`
/// delimiters and leading whitespace, and strip each continuation line's
/// leading whitespace and `*` margin (one following space consumed).
/// Two deliberate deltas, both required by the round-trip gate (the JSON
/// body must survive print → parse → emit): trailing empty lines are kept
/// (Java's `split` drops them; the pilot's first-pass output is identical
/// either way), and the transform is iterated to a **fixpoint** — the
/// pilot's single pass is not idempotent (margin lines can leave leading
/// empty lines or whitespace a second pass would eat).
fn process_comment_body(body: &str) -> String {
    let mut cur = body.to_string();
    for _ in 0..8 {
        let next = process_comment_body_once(&cur);
        if next == cur {
            break;
        }
        cur = next;
    }
    cur
}

fn process_comment_body_once(body: &str) -> String {
    let mut s: String = match body.find("/*") {
        Some(p) => format!("{}{}", &body[..p], &body[p + 2..]),
        None => body.to_string(),
    };
    s = s.trim_start().to_string();
    if s.ends_with("*/") {
        s.truncate(s.len() - 2);
    }
    let lines: Vec<&str> = s
        .split('\n')
        .map(|l| l.strip_suffix('\r').unwrap_or(l))
        .collect();
    if lines.len() == 1 {
        return lines[0].to_string();
    }
    let mut out = String::new();
    for (i, line) in lines.iter().enumerate() {
        let t = line.trim_start();
        let t = t
            .strip_prefix("* ")
            .or_else(|| t.strip_prefix('*'))
            .unwrap_or(t);
        if i != 0 {
            out.push('\n');
        }
        out.push_str(t);
    }
    out
}

/// Effective name of an unnamed feature: the last segment of the first
/// redefined (KerML 8.2.3.5) or referenced (SysML reference forms) feature,
/// in declaration order.
fn id_matches(id: &Identification, name: &str) -> bool {
    [&id.name, &id.short_name]
        .into_iter()
        .flatten()
        .any(|n| n.value == name)
}

/// The usage a member declares directly or through a role keyword.
fn member_usage(m: &Member) -> Option<&Usage> {
    match &m.kind {
        MemberKind::Usage(u)
        | MemberKind::Subject(u)
        | MemberKind::Actor(u)
        | MemberKind::Stakeholder(u)
        | MemberKind::Objective(u)
        | MemberKind::FramedConcern(u)
        | MemberKind::RequirementVerification(u)
        | MemberKind::Render(u)
        | MemberKind::Return(u) => Some(u),
        _ => None,
    }
}

fn member_id(m: &Member) -> Option<&Identification> {
    match &m.kind {
        MemberKind::Package(p) => Some(&p.id),
        MemberKind::Definition(d) => Some(&d.id),
        MemberKind::Alias(a) => Some(&a.id),
        MemberKind::Dependency(d) => Some(&d.id),
        MemberKind::Relationship(r) => Some(&r.id),
        MemberKind::MultiplicityDecl(d) => Some(&d.id),
        MemberKind::Comment(c) => Some(&c.id),
        MemberKind::Doc(d) => Some(&d.id),
        MemberKind::TextualRep(r) => Some(&r.id),
        _ => member_usage(m).map(|u| &u.declaration.id),
    }
}

fn member_body(m: &Member) -> Option<&[Member]> {
    match &m.kind {
        MemberKind::Package(p) => p.body.as_deref(),
        MemberKind::Definition(d) => d.body.as_deref(),
        _ => member_usage(m).and_then(|u| u.body.as_deref()),
    }
}

/// The names one syntactic member contributes to its namespace. `None` for
/// members whose contribution needs resolution (re-exporting imports).
fn member_names(m: &Member, out: &mut HashSet<String>) -> Option<()> {
    match &m.kind {
        MemberKind::Import(_) | MemberKind::Expose(_) => return None,
        MemberKind::Filter(_) | MemberKind::Result(_) | MemberKind::InitialNode(_) => {
            return Some(());
        }
        _ => {}
    }
    let id = member_id(m)?;
    out.extend(
        [&id.name, &id.short_name]
            .into_iter()
            .flatten()
            .map(|n| n.value.clone()),
    );
    if let Some(u) = member_usage(m) {
        if u.declaration.id.name.is_none() {
            out.extend(effective_ref_name(
                &u.declaration,
                matches!(
                    u.kind,
                    UsageKind::Perform | UsageKind::Exhibit | UsageKind::Include
                ),
                u.prefix.is_variant,
            ));
        }
    }
    Some(())
}

/// The names the members of a user namespace contribute to an import of
/// it. Unless the import is `all`, a private or protected import in the
/// namespace re-exports nothing to it.
fn user_member_names(
    members: &[Member],
    recursive: bool,
    import_all: bool,
    out: &mut HashSet<String>,
) -> Option<()> {
    for m in members {
        if !import_all
            && matches!(m.kind, MemberKind::Import(_))
            && matches!(
                m.visibility,
                Some(Visibility::Private | Visibility::Protected)
            )
        {
            continue;
        }
        member_names(m, out)?;
        if recursive {
            if let Some(body) = member_body(m) {
                user_member_names(body, true, import_all, out)?;
            }
        }
    }
    Some(())
}

fn effective_ref_name(
    d: &FeatureDeclaration,
    reference_chain: bool,
    variant: bool,
) -> Option<String> {
    let named_reference = (reference_chain || variant)
        && d.specializations
            .iter()
            .any(|s| matches!(s, FeatureSpecialization::References(_)));
    for s in &d.specializations {
        if named_reference && !matches!(s, FeatureSpecialization::References(_)) {
            continue;
        }
        let target = match s {
            FeatureSpecialization::References(t) => Some(t),
            FeatureSpecialization::Redefines(ts) => ts.first(),
            _ => None,
        };
        if let Some(t) = target {
            let qn = match t {
                TargetRef::Name(qn) => qn,
                TargetRef::Chain(links)
                    if reference_chain && matches!(s, FeatureSpecialization::References(_)) =>
                {
                    links.last()?
                }
                TargetRef::Chain(_) => return None,
            };
            return qn.segments.last().map(|n| n.value.clone());
        }
    }
    None
}

/// A connector-end target as one flat qualified name (chain links
/// concatenated): member steps resolve through each element's scope like
/// chain steps do, so the flattening preserves the target element.
fn flat_target_qn(target: &TargetRef) -> Option<QualifiedName> {
    match target {
        TargetRef::Name(qn) => Some(qn.clone()),
        TargetRef::Chain(links) => {
            let first = links.first()?;
            Some(QualifiedName {
                is_global: first.is_global,
                segments: links
                    .iter()
                    .flat_map(|l| l.segments.iter().cloned())
                    .collect(),
                span: first.span,
            })
        }
    }
}

/// The feature reference inside a SemanticMetadata `baseType` value.
/// Cast-like classification operators preserve their operand (`f meta
/// SysML::Usage`, `f as SysML::Usage`, `f @@ M`); boolean classification
/// tests (`istype`/`hastype`/`@`) are not baseType shapes.
fn semantic_base_ref(kind: &ExprKind) -> Option<&QualifiedName> {
    match kind {
        ExprKind::Classification {
            op: ClassificationOp::Meta | ClassificationOp::As | ClassificationOp::MetaAtType,
            operand: Some(operand),
            ..
        } => semantic_base_ref(&operand.kind),
        ExprKind::Ref(qn) => Some(qn),
        _ => None,
    }
}

pub(crate) fn lib_qn(path: &str) -> QualifiedName {
    // `$::`-rooted: an implied library base must reach the library even
    // when a user package shadows the library package's name lexically
    // (a nested `package Actions` must not hide `Actions::actions`).
    QualifiedName {
        is_global: true,
        segments: path
            .split("::")
            .map(|s| Name {
                value: s.to_string(),
                span: sysmlv2_syntax::span::Span::default(),
            })
            .collect(),
        span: sysmlv2_syntax::span::Span::default(),
    }
}

/// Implied specialization bases per definition kind (SysML 8.4.2 Table 31 /
/// KerML Table 10). Used for *name resolution only* — the compact form never
/// serializes implied relationships.
pub(crate) fn implicit_def_bases(kind: DefKind) -> &'static [&'static str] {
    match kind {
        DefKind::Attribute | DefKind::Enum => &["Attributes::AttributeValue"],
        DefKind::Occurrence | DefKind::Individual => &["Occurrences::Occurrence"],
        DefKind::Item => &["Items::Item"],
        DefKind::Metadata => &["Metadata::MetadataItem"],
        DefKind::Part => &["Parts::Part"],
        DefKind::Port => &["Ports::Port"],
        DefKind::Connection => &["Connections::Connection"],
        DefKind::Interface => &["Interfaces::Interface"],
        DefKind::Allocation => &["Allocations::Allocation"],
        DefKind::Flow => &["Flows::MessageAction"],
        DefKind::Action => &["Actions::Action"],
        DefKind::State => &["States::StateAction"],
        DefKind::Calc => &["Calculations::Calculation"],
        DefKind::Constraint => &["Constraints::ConstraintCheck"],
        DefKind::Requirement => &["Requirements::RequirementCheck"],
        DefKind::Concern => &["Requirements::ConcernCheck"],
        DefKind::Case => &["Cases::Case"],
        DefKind::Analysis => &["AnalysisCases::AnalysisCase"],
        DefKind::Verification => &["VerificationCases::VerificationCase"],
        DefKind::UseCase => &["UseCases::UseCase"],
        DefKind::View => &["Views::View"],
        DefKind::Viewpoint => &["Views::ViewpointCheck"],
        DefKind::Rendering => &["Views::Rendering"],
        // KerML kinds (kernel semantic library).
        DefKind::Class => &["Occurrences::Occurrence"],
        DefKind::Struct => &["Objects::Object"],
        DefKind::Assoc | DefKind::AssocStruct => &["Links::Link"],
        DefKind::Behavior => &["Performances::Performance"],
        DefKind::Function => &["Performances::Evaluation"],
        DefKind::Predicate => &["Performances::BooleanEvaluation"],
        DefKind::Interaction => &["Transfers::Transfer"],
        DefKind::DataType => &["Base::DataValue"],
        DefKind::Type | DefKind::Classifier => &["Base::Anything"],
        DefKind::Metaclass => &["Metaobjects::Metaobject"],
        DefKind::Extended => &[],
    }
}

/// Implied subsetting bases per usage kind (SysML 8.4.2 Table 32).
pub(crate) fn implicit_usage_bases(kind: UsageKind) -> &'static [&'static str] {
    match kind {
        UsageKind::Attribute | UsageKind::Enum => &["Attributes::attributeValues"],
        UsageKind::Occurrence | UsageKind::Event => &["Occurrences::occurrences"],
        UsageKind::Item => &["Items::items"],
        UsageKind::Metadata => &["Metadata::metadataItems"],
        UsageKind::Part => &["Parts::parts"],
        UsageKind::Port => &["Ports::ports"],
        UsageKind::Connection => &["Connections::connections"],
        UsageKind::Interface => &["Interfaces::interfaces"],
        UsageKind::Allocation => &["Allocations::allocations"],
        UsageKind::Flow | UsageKind::Message => &["Flows::messages"],
        UsageKind::SuccessionFlow => &["Flows::successionFlows"],
        UsageKind::Action | UsageKind::Perform => &["Actions::actions"],
        UsageKind::Accept => &["Actions::acceptActions"],
        UsageKind::Send => &["Actions::sendActions"],
        UsageKind::Assign => &["Actions::assignmentActions"],
        UsageKind::Terminate => &["Actions::terminateActions"],
        UsageKind::IfNode => &["Actions::ifThenActions"],
        UsageKind::WhileLoop => &["Actions::whileLoops"],
        UsageKind::ForLoop => &["Actions::forLoopActions"],
        UsageKind::Merge | UsageKind::Decide | UsageKind::Join | UsageKind::Fork => {
            &["Actions::controls"]
        }
        UsageKind::State | UsageKind::Exhibit => &["States::stateActions"],
        UsageKind::Transition => &["Actions::transitionActions", "States::stateTransitions"],
        UsageKind::Calc => &["Calculations::calculations"],
        UsageKind::Constraint | UsageKind::AssertConstraint => &["Constraints::constraintChecks"],
        UsageKind::Requirement | UsageKind::Satisfy => &["Requirements::requirementChecks"],
        UsageKind::Concern => &["Requirements::concernChecks"],
        UsageKind::Case => &["Cases::cases"],
        UsageKind::Analysis => &["AnalysisCases::analysisCases"],
        UsageKind::Verification => &["VerificationCases::verificationCases"],
        UsageKind::UseCase | UsageKind::Include => &["UseCases::useCases"],
        UsageKind::View => &["Views::views"],
        UsageKind::Rendering => &["Views::renderings"],
        _ => &[],
    }
}

/// Metaclass and source/target property names for KerML standalone
/// relationship declarations.
fn relationship_decl_props(
    kind: RelationshipDeclKind,
) -> (&'static str, &'static str, &'static str) {
    use RelationshipDeclKind::*;
    match kind {
        Specialization => ("Specialization", "specific", "general"),
        Subclassification => ("Subclassification", "subclassifier", "superclassifier"),
        FeatureTyping => ("FeatureTyping", "typedFeature", "type"),
        Subsetting => ("Subsetting", "subsettingFeature", "subsettedFeature"),
        Redefinition => ("Redefinition", "redefiningFeature", "redefinedFeature"),
        Conjugation => ("Conjugation", "conjugatedType", "originalType"),
        Disjoining => ("Disjoining", "typeDisjoined", "disjoiningType"),
        FeatureInverting => ("FeatureInverting", "featureInverted", "invertingFeature"),
        TypeFeaturing => ("TypeFeaturing", "featureOfType", "featuringType"),
    }
}

fn def_metaclass(kind: DefKind) -> &'static str {
    match kind {
        DefKind::Extended => "Definition",
        DefKind::Type => "Type",
        DefKind::Classifier => "Classifier",
        DefKind::Class => "Class",
        DefKind::Struct => "Structure",
        DefKind::DataType => "DataType",
        DefKind::Assoc => "Association",
        DefKind::AssocStruct => "AssociationStructure",
        DefKind::Behavior => "Behavior",
        DefKind::Interaction => "Interaction",
        DefKind::Function => "Function",
        DefKind::Predicate => "Predicate",
        DefKind::Metaclass => "Metaclass",
        DefKind::Attribute => "AttributeDefinition",
        DefKind::Enum => "EnumerationDefinition",
        DefKind::Occurrence | DefKind::Individual => "OccurrenceDefinition",
        DefKind::Item => "ItemDefinition",
        DefKind::Metadata => "MetadataDefinition",
        DefKind::Part => "PartDefinition",
        DefKind::Port => "PortDefinition",
        DefKind::Connection => "ConnectionDefinition",
        DefKind::Interface => "InterfaceDefinition",
        DefKind::Allocation => "AllocationDefinition",
        DefKind::Flow => "FlowDefinition",
        DefKind::Action => "ActionDefinition",
        DefKind::State => "StateDefinition",
        DefKind::Calc => "CalculationDefinition",
        DefKind::Constraint => "ConstraintDefinition",
        DefKind::Requirement => "RequirementDefinition",
        DefKind::Concern => "ConcernDefinition",
        DefKind::Case => "CaseDefinition",
        DefKind::Analysis => "AnalysisCaseDefinition",
        DefKind::Verification => "VerificationCaseDefinition",
        DefKind::UseCase => "UseCaseDefinition",
        DefKind::View => "ViewDefinition",
        DefKind::Viewpoint => "ViewpointDefinition",
        DefKind::Rendering => "RenderingDefinition",
    }
}

/// Whether the concrete metaclass declares `isVariation` in its XMI
/// property closure. The SysML definition/usage families do; the KerML
/// metaclasses the shared definition/usage lowering can produce do not,
/// and their schemas (`additionalProperties: false`) reject the key.
fn declares_variation(ty: &str) -> bool {
    !matches!(
        ty,
        // def_metaclass KerML kinds
        "Type"
            | "Classifier"
            | "Class"
            | "Structure"
            | "DataType"
            | "Association"
            | "AssociationStructure"
            | "Behavior"
            | "Interaction"
            | "Function"
            | "Predicate"
            | "Metaclass"
            // usage_metaclass KerML kinds
            | "Feature"
            | "Step"
            | "Expression"
            | "BooleanExpression"
            | "Invariant"
            | "Connector"
            | "BindingConnector"
            | "Succession"
            | "Flow"
            | "SuccessionFlow"
            | "MetadataFeature"
    )
}

fn usage_metaclass(kind: UsageKind, dialect: Dialect) -> &'static str {
    let kerml = dialect == Dialect::Kerml;
    match kind {
        // Kinds whose metaclass differs between dialects.
        UsageKind::Default if kerml => return "Feature",
        UsageKind::Succession if kerml => return "Succession",
        UsageKind::SuccessionFlow if kerml => return "SuccessionFlow",
        UsageKind::Flow if kerml => return "Flow",
        UsageKind::Binding if kerml => return "BindingConnector",
        UsageKind::Metadata if kerml => return "MetadataFeature",
        // KerML-only kinds.
        UsageKind::Feature => return "Feature",
        UsageKind::Step => return "Step",
        UsageKind::Expr => return "Expression",
        UsageKind::BoolExpr => return "BooleanExpression",
        UsageKind::Invariant => return "Invariant",
        UsageKind::Connector => return "Connector",
        _ => {}
    }
    match kind {
        UsageKind::Attribute => "AttributeUsage",
        UsageKind::Enum => "EnumerationUsage",
        UsageKind::Occurrence => "OccurrenceUsage",
        UsageKind::Item => "ItemUsage",
        UsageKind::Metadata => "MetadataUsage",
        UsageKind::Part => "PartUsage",
        UsageKind::Port => "PortUsage",
        UsageKind::Connection => "ConnectionUsage",
        UsageKind::Interface => "InterfaceUsage",
        UsageKind::Allocation => "AllocationUsage",
        UsageKind::Flow => "FlowUsage",
        UsageKind::Action => "ActionUsage",
        UsageKind::State => "StateUsage",
        UsageKind::Calc => "CalculationUsage",
        UsageKind::Constraint => "ConstraintUsage",
        UsageKind::Requirement => "RequirementUsage",
        UsageKind::Concern => "ConcernUsage",
        UsageKind::Case => "CaseUsage",
        UsageKind::Analysis => "AnalysisCaseUsage",
        UsageKind::Verification => "VerificationCaseUsage",
        UsageKind::UseCase => "UseCaseUsage",
        UsageKind::View => "ViewUsage",
        UsageKind::Viewpoint => "ViewpointUsage",
        UsageKind::Rendering => "RenderingUsage",
        UsageKind::Ref | UsageKind::Default => "ReferenceUsage",
        UsageKind::Extended => "Usage",
        UsageKind::Perform => "PerformActionUsage",
        UsageKind::Exhibit => "ExhibitStateUsage",
        UsageKind::Include => "IncludeUseCaseUsage",
        UsageKind::Event => "EventOccurrenceUsage",
        UsageKind::Satisfy => "SatisfyRequirementUsage",
        UsageKind::AssertConstraint => "AssertConstraintUsage",
        UsageKind::Succession => "SuccessionAsUsage",
        UsageKind::SuccessionFlow => "SuccessionFlowUsage",
        UsageKind::Binding => "BindingConnectorAsUsage",
        UsageKind::Message => "FlowUsage",
        UsageKind::Transition => "TransitionUsage",
        UsageKind::Merge => "MergeNode",
        UsageKind::Decide => "DecisionNode",
        UsageKind::Join => "JoinNode",
        UsageKind::Fork => "ForkNode",
        UsageKind::Accept => "AcceptActionUsage",
        UsageKind::Send => "SendActionUsage",
        UsageKind::Assign => "AssignmentActionUsage",
        UsageKind::Terminate => "TerminateActionUsage",
        UsageKind::IfNode => "IfActionUsage",
        UsageKind::WhileLoop => "WhileLoopActionUsage",
        UsageKind::ForLoop => "ForLoopActionUsage",
        // Handled by the dialect match above.
        UsageKind::Feature
        | UsageKind::Step
        | UsageKind::Expr
        | UsageKind::BoolExpr
        | UsageKind::Invariant
        | UsageKind::Connector => unreachable!(),
    }
}

fn binary_op_str(op: BinaryOp) -> &'static str {
    match op {
        BinaryOp::NullCoalescing => "??",
        BinaryOp::Implies => "implies",
        BinaryOp::OrBar => "|",
        BinaryOp::CondOr => "or",
        BinaryOp::Xor => "xor",
        BinaryOp::AndAmp => "&",
        BinaryOp::CondAnd => "and",
        BinaryOp::Eq => "==",
        BinaryOp::NotEq => "!=",
        BinaryOp::Same => "===",
        BinaryOp::NotSame => "!==",
        BinaryOp::Lt => "<",
        BinaryOp::Gt => ">",
        BinaryOp::LtEq => "<=",
        BinaryOp::GtEq => ">=",
        BinaryOp::Range => "..",
        BinaryOp::Add => "+",
        BinaryOp::Sub => "-",
        BinaryOp::Mul => "*",
        BinaryOp::Div => "/",
        BinaryOp::Rem => "%",
        BinaryOp::Pow => "**",
        BinaryOp::Caret => "^",
    }
}

// ---------------------------------------------------------------------------
// Resolved-model API (for the evaluator and other semantic consumers)
// ---------------------------------------------------------------------------

/// Is `ty` a FeatureMembership-subtype metaclass? Decided from the
/// generated schema catalog: `ownedMemberFeature` is a
/// FeatureMembership-only property, so its presence marks every concrete
/// subtype without a hand-kept list. This is what keeps `ownedFeature`
/// exactly KerML's `Type::ownedFeature`: a usage owned by a *package*
/// rides an OwningMembership (membership metaclass follows the owner),
/// so it is an owned member but not an owned feature.
pub(crate) fn is_feature_membership(ty: &str) -> bool {
    static KINDS: std::sync::OnceLock<HashSet<&'static str>> = std::sync::OnceLock::new();
    KINDS
        .get_or_init(|| {
            crate::schema_props::METACLASS_PROPS
                .iter()
                .filter(|(_, props)| props.iter().any(|(p, _)| *p == "ownedMemberFeature"))
                .map(|(n, _)| *n)
                .collect()
        })
        .contains(ty)
}

/// An opaque handle to one element of a resolved model. Ordering follows
/// element creation order — document/declaration order within a unit.
#[derive(
    Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug, serde::Serialize, serde::Deserialize,
)]
pub struct ElementRef(pub(crate) usize);

/// An opaque handle to one name-resolution scope of a resolved model (a
/// namespace body an expression's references resolve from).
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, serde::Serialize, serde::Deserialize)]
pub struct ScopeRef(pub(crate) usize);

/// One resolved reference site: a qualified name written in a user unit
/// and the element it resolved to (see [`ResolvedModel::references_to`]).
/// The enabling record for find-usages and rename — a rename must respell
/// the `name_span` text at every site of its element.
#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub struct RefSite {
    /// Index into [`crate::model::Model::units`] of the unit the
    /// reference was written in.
    pub unit: usize,
    /// Span of the whole qualified name (`Definitions::Wheel`).
    pub span: Span,
    /// Span of the last segment — the text that names the target
    /// (`Wheel`; equals `span` for a simple name).
    pub name_span: Span,
    /// The element the name denotes. For a membership import this is the
    /// imported member (the serialized `importedMembership` value is its
    /// owning Membership); for a `~P` typing it is `P` (the serialized
    /// type is the implicit ConjugatedPortDefinition).
    pub target: ElementRef,
    /// The serialized property the resolution feeds (`type`, `general`,
    /// `redefinedFeature`, `importedNamespace`, …), array-index suffixes
    /// stripped.
    pub kind: String,
    /// The name-resolution scope the site resolved from.
    pub scope: ScopeRef,
    /// The element excluded from resolution at this site, if any (a
    /// feature's own specialization targets and value expression must
    /// not capture the feature itself through its registered name).
    pub exclude: Option<ElementRef>,
    /// Whether the resolution ran under *plain* lexical rules — no chain
    /// context, no declared-only mode, not an import target — so
    /// [`ResolvedModel::resolve_in_excluding`] from `scope` with
    /// `exclude` reproduces it. Respelling passes only touch
    /// plain sites.
    pub plain: bool,
    /// The element whose serialized property carries the reference — the
    /// declaration or relationship the spelling was written on (source
    /// provenance: relocation edits classify sites by where they live).
    pub owner: ElementRef,
    /// For sites resolved under a feature-chain context (`engine.mass` —
    /// the member step resolves in the chain target's scope): the element
    /// the chain's first link denotes (`engine`). `None` for plain
    /// lexical sites. A site whose chain root is a usage is reached
    /// *through* that usage, not through its definition — the distinction
    /// relocation eligibility runs on.
    pub chain_root: Option<ElementRef>,
    /// The import relationships the resolution walked through — the
    /// imports this site depends on — each with the most restrictive
    /// access any walk of it ran under. Sorted by import; empty for
    /// `qualifier` sites and for sites replayed from a cache.
    #[serde(default)]
    pub via_imports: Vec<(ElementRef, AccessMode)>,
}

/// One reference that failed to resolve, with enough source provenance
/// for relocation edits to distinguish a pre-existing unresolved site
/// from a newly-created site that happens to use the same spelling.
#[derive(Clone, Debug)]
pub struct UnresolvedReference {
    /// The relationship/element whose serialized property carries the
    /// unresolved reference.
    pub owner: ElementRef,
    /// The qualified name as written.
    pub spelling: String,
    /// Model-unit index in which it was written.
    pub unit: usize,
    /// Span of the whole qualified name.
    pub span: Span,
}

/// One constraint-family element carrying its own trailing result
/// expression, as enumerated by [`ResolvedModel::constraints`] — the input
/// to both verdict checking ([`crate::check::check_constraints`]) and SMT
/// solving (the `sysmlv2-solve` crate).
#[derive(Clone, Debug)]
pub struct ConstraintInfo {
    /// The constraint/requirement/invariant element itself.
    pub element: ElementRef,
    /// Index into [`crate::model::Model::units`].
    pub unit: usize,
    /// Span of the result expression.
    pub span: sysmlv2_syntax::span::Span,
    /// Declared name of the owning element, if any.
    pub name: Option<String>,
    /// Metaclass of the owning element (e.g. `AssertConstraintUsage`).
    pub element_type: &'static str,
    /// Whether the constraint is asserted to hold (assert usages and KerML
    /// invariants).
    pub asserted: bool,
    /// `assert not` / negated invariant — the expression is expected false.
    pub negated: bool,
    /// Scope the expression's references resolve from.
    pub scope: ScopeRef,
    /// The result expression.
    pub expr: Expr,
}

/// A body member in declaration order, for flow-order-sensitive
/// consumers (the behavior views): either an owned member element, or a
/// `first X;` initial-node marker carrying the referenced node and/or
/// its written spelling.
pub enum BodyFlowMember {
    /// An owned member element.
    Member(ElementRef),
    /// A `first X;` marker: resolved target and/or written spelling.
    Initial(Option<ElementRef>, Option<String>),
}

/// How a constraint or a nested requirement bears on the requirement
/// check that composes it. A requirement check holds when its assumed
/// constraints imply its required ones (the library `RequirementCheck`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SatisfactionRole {
    /// Must hold: a `require` member, a nested requirement, an assertion.
    Required,
    /// An `assume` member: when it is false, the check holds vacuously.
    Assumed,
}

/// One requirement check within a satisfaction claim: the satisfied
/// requirement itself (the first of [`SatisfactionInfo::nodes`]) or a
/// requirement it composes (`require r;`, a nested requirement usage).
#[derive(Clone, Debug, Default)]
pub struct SatisfactionNode {
    /// The check's own constraints, as indices into
    /// [`SatisfactionInfo::constraints`].
    pub constraints: Vec<(usize, SatisfactionRole)>,
    /// The checks it composes, as indices into [`SatisfactionInfo::nodes`].
    pub children: Vec<(usize, SatisfactionRole)>,
}

/// One `satisfy R by x;` claim expanded to the constraint verdicts it
/// implies: every constraint reachable through R's requirement
/// composition, evaluated with R's subjects bound to the satisfaction
/// target (see [`ResolvedModel::satisfactions`]).
pub struct SatisfactionInfo {
    /// The SatisfyRequirementUsage element.
    pub satisfy: ElementRef,
    /// Index into [`crate::model::Model::units`] of the `satisfy`
    /// statement.
    pub unit: usize,
    /// Source extent of the `satisfy` statement, keyword through its `;`
    /// or body.
    pub span: Span,
    /// The satisfying feature as written after `by`.
    pub by: String,
    /// `not satisfy R by x;`: the claim is that `x` does not satisfy `R`.
    pub negated: bool,
    /// Qualified name of the satisfied requirement — the context label
    /// verdict reports carry. An unnamed claim that declares its own
    /// requirement (`satisfy requirement : R by x;`) is labelled by `R`.
    pub context: Option<String>,
    /// The constraints the claim implies, ready for verdict evaluation
    /// with [`ResolvedModel::evaluate_in_with`], in source order.
    pub constraints: Vec<ConstraintInfo>,
    /// The requirement checks the constraints belong to, the satisfied
    /// requirement first: how their verdicts combine into the claim's.
    pub nodes: Vec<SatisfactionNode>,
    /// Subject bindings: every subject parameter in the satisfied
    /// requirement's explicit closure → the satisfaction target.
    pub overrides: std::collections::HashMap<usize, crate::eval::Value>,
}

/// A model lowered to the element graph with all names resolved — the
/// entry point for semantic queries and expression evaluation.
pub struct ResolvedModel {
    pub(crate) b: Builder,
    /// Last publication observed by the derived-reader cache group.
    semantic_publication_seen: publication::Revision,
    /// Relationship index → owning element, built lazily by
    /// [`Self::element_qualified_name`] (empty until first use).
    rel_owner: crate::layered::LayeredVec<Option<usize>>,
    /// Membership index → owned member element, built lazily by
    /// [`Self::membership_member`] (empty until first use).
    rel_member: Vec<Option<usize>>,
    /// Interchange `@id` → element index, built lazily by the connector /
    /// transition accessors (empty until first use): the builder's own index
    /// while no two rows share an id.
    by_id: Arc<crate::layered::IdMap<Uuid, usize>>,
    /// Element count `by_id` was built for. Compared instead of the map's
    /// own length: duplicate ids (an id-scheme collision between
    /// same-named units) make the map smaller than the element list, and
    /// a length comparison would then rebuild it on every lookup.
    by_id_built_for: usize,
    /// Per-unit (name, line index), aligned with the model's unit list —
    /// span-to-line conversion for declaration sites (diagram links).
    unit_meta: Vec<(String, sysmlv2_syntax::span::LineIndex)>,
    /// Library scalar-quantity type lookups (by dimension key and by
    /// `mRef` unit definition), built lazily by
    /// [`Self::quantity_type_candidates`] (`None` until first use).
    pub(crate) quantity_index: Option<QuantityIndex>,
    /// Element index → its effective name (`Element::effectiveName()`),
    /// memoized by `naming.rs` (empty until first use).
    name_memo: Vec<Option<Option<String>>>,
    /// Names of elements outside the model, by id — a library name table
    /// the caller supplied ([`Self::set_library_names`]) for a model built
    /// without its library. The naming rule reads it for a naming feature
    /// it has no element for; the implied-relationship synthesis reads
    /// the inverse.
    external_names: HashMap<Uuid, String>,
    /// The same table inverted: qualified name → id.
    external_by_name: HashMap<String, Uuid>,
    /// Qualified names with conflicting external identity or provenance
    /// evidence. The compatibility lookup index remains available, but these
    /// names cannot prove a designated model-level function identity.
    external_ambiguous_names: HashSet<String>,
    /// Each external id's root package (the first segment of its
    /// qualified name) — which library package a function belongs to.
    external_package: HashMap<Uuid, String>,
    /// How the inheritance-aware families answer (`json/closures.rs`).
    closure_policy: ClosurePolicy,
    /// Scope → whether its import walk was truncated, per implied flag
    /// (`json/closures.rs`; `inherited_bindings` memoizes the heritage
    /// side itself).
    import_truncated: HashMap<(usize, bool), bool>,
    /// [`derives`] per metaclass over every derived name of the catalog,
    /// filled as metaclasses are met (`json/derived.rs`).
    derives_memo: HashMap<&'static str, Box<[Derives]>>,
    /// The names the layer computes per metaclass, in `computed_names()`
    /// order ([`Self::computable_names`]).
    plan_memo: HashMap<&'static str, Arc<[&'static str]>>,
    /// User features by the elements their explicit redefinitions
    /// target, built lazily by [`Self::redefiners`] (`None` until first
    /// use).
    pub(crate) redefiner_index: Option<HashMap<usize, Vec<usize>>>,
}

/// The enumeration and variation entries of `pairs` (element, body scope):
/// an `EnumerationDefinition`, or any element whose body binds variants, with
/// the variants it binds (enum literals and variation variants are both owned
/// through a `VariantMembership`), sorted and deduplicated. Unordered.
fn enum_entries<'a>(
    b: &Builder,
    pairs: impl Iterator<Item = (&'a usize, &'a usize)>,
) -> Vec<(usize, Vec<usize>)> {
    let is_variant = |e: usize| {
        b.elements[e]
            .owning_relationship
            .map(|r| b.elements[r].ty == "VariantMembership")
            .unwrap_or(false)
    };
    let mut out = Vec::new();
    for (&elem, &scope) in pairs {
        let enum_def = b.elements[elem].ty == "EnumerationDefinition";
        let mut lits: Vec<usize> = b.scopes[scope]
            .names
            .values()
            .flatten()
            .map(|binding| binding.elem)
            .filter(|&e| is_variant(e))
            .collect();
        lits.sort_unstable();
        lits.dedup();
        if enum_def || !lits.is_empty() {
            out.push((elem, lits));
        }
    }
    out
}

/// The lazily-built quantity-type index of a resolved model (see
/// `crate::quantity`): scalar quantity types keyed by their dimension
/// and by the unit definitions their `mRef`s name.
pub(crate) struct QuantityIndex {
    pub(crate) by_dims: HashMap<crate::quantity::QuantityDims, Vec<usize>>,
    pub(crate) by_unit_def: HashMap<usize, Vec<usize>>,
}

impl ResolvedModel {
    /// Build the element graph for `model` (libraries included) and resolve
    /// all names.
    pub fn build(model: &crate::model::Model) -> ResolvedModel {
        let mut b = Builder::default();
        b.build_model(model);
        Self::from_builder(b, model)
    }

    pub(crate) fn source_compact_json(&self) -> Value {
        self.b
            .finish_range(self.b.lib_boundary, self.b.explicit_len())
    }

    /// Payload units retain their supplied flags even though their syntax was
    /// reconstructed by the loader. Prepared library prefixes are textual.
    pub(crate) fn canonical_text_end(&self, e: ElementRef) -> bool {
        self.b.graph_format == crate::model::GraphFormat::CanonicalV3
            && e.0 < self.b.explicit_len()
            && self.b.elements.get(e.0).is_some_and(|row| {
                metaclass_conforms(row.ty, "Usage")
                    && row.props.get("isEnd").and_then(|v| v.as_bool()) == Some(true)
                    && !self
                        .b
                        .payload_source_units
                        .contains(&self.b.unit_of_elem(e.0))
            })
    }

    /// Compatibility compact emission completes only proven textual defaults.
    /// Unknown evidence remains syntax data; checked reads and strict export
    /// expose the qualification instead of certifying that retained value.
    fn completed_compact_range(&mut self, start: usize, end: usize) -> Value {
        let mut compact = self.b.finish_range(start, end);
        for (offset, row) in compact
            .as_array_mut()
            .expect("element array")
            .iter_mut()
            .enumerate()
        {
            if let Some(report) =
                self.canonical_end_constant_with_budget(ElementRef(start + offset), 0)
            {
                if let Ok(value) = report.value {
                    row["isConstant"] = json!(value);
                }
            }
        }
        compact
    }

    pub(crate) fn payload_owned_flag_anchor(&self, e: ElementRef) -> Option<(usize, String)> {
        let row = self.b.elements.get(e.0)?;
        let unit = self.b.unit_of_elem(e.0);
        (e.0 >= self.b.lib_boundary
            && e.0 < self.b.explicit_len()
            && self.b.payload_source_units.contains(&unit)
            && (row.path_parent.is_some() || !row.path.is_empty()))
        .then(|| (unit, whole_path(&self.b.elements, e.0)))
    }

    pub(crate) fn from_builder(mut b: Builder, model: &crate::model::Model) -> Self {
        // A user relationship can specialize a library feature without adding
        // a root name. Such a graph cannot reuse derived library quantities.
        if let Some(facts) = &b.library_facts {
            let changed = b.elements.iter().skip(b.lib_boundary).any(|e| {
                let source = match e.ty {
                    "FeatureTyping" | "ConjugatedPortTyping" => Some("typedFeature"),
                    "Subclassification" => Some("subclassifier"),
                    "Subsetting" | "ReferenceSubsetting" => Some("subsettingFeature"),
                    "Redefinition" => Some("redefiningFeature"),
                    "Specialization" => Some("specific"),
                    "Conjugation" => Some("conjugatedType"),
                    "TypeFeaturing" => Some("featureOfType"),
                    "FeatureInverting" => Some("featureInverted"),
                    _ => None,
                };
                source
                    .and_then(|key| e.props.get(key))
                    .and_then(|v| v.as_reference())
                    .is_some_and(|id| facts.contains_id(&id))
                    || e.props.get("annotatedElement").is_some_and(|v| {
                        v.as_reference().is_some_and(|id| facts.contains_id(&id))
                            || v.as_array().is_some_and(|a| {
                                a.iter()
                                    .filter_map(|v| v.as_reference())
                                    .any(|id| facts.contains_id(&id))
                            })
                    })
            });
            if changed {
                b.semantic_memo = Default::default();
            }
        }
        b.semantic_ready = true;
        b.publication.enable();
        b.recorded_lookup_ready = b.recorded_lookup_candidate && !b.recorded_lookup_incomplete;
        let semantic_publication_seen = b.publication.revision();
        ResolvedModel {
            b,
            semantic_publication_seen,
            rel_owner: Default::default(),
            rel_member: Vec::new(),
            by_id: Arc::default(),
            by_id_built_for: usize::MAX,
            unit_meta: (0..model.unit_count())
                .map(|i| {
                    let (name, lines) = model.unit_meta(i);
                    (name.to_owned(), lines.clone())
                })
                .collect(),
            quantity_index: None,
            name_memo: Vec::new(),
            external_names: HashMap::new(),
            external_by_name: HashMap::new(),
            external_ambiguous_names: HashSet::new(),
            external_package: HashMap::new(),
            closure_policy: ClosurePolicy::default(),
            import_truncated: HashMap::new(),
            derives_memo: HashMap::new(),
            plan_memo: HashMap::new(),
            redefiner_index: None,
        }
    }

    /// Supply the names of library elements this model was built
    /// without: `id → qualified-name segments`, as
    /// [`library_element_name_map`] produces them for a model that has
    /// the library. The specification's naming rule then names an unnamed
    /// feature after a library feature it redefines or references
    /// (`attribute :>> mass;` → `mass`) exactly as it would with the
    /// library loaded, and the implied library specializations can be
    /// synthesized. A model that has its library loaded needs none of
    /// this. Call it before the first derived query: the naming memo is
    /// reset, and the implied relationships are re-synthesized only if
    /// none were materialized yet (materialized ones stay).
    pub fn set_library_names(&mut self, names: &HashMap<String, Vec<String>>) {
        let dynamic_was_current = self
            .b
            .dynamic_graph
            .as_ref()
            .is_some_and(|s| s.current(&self.b));
        self.external_names.clear();
        self.external_by_name.clear();
        self.external_ambiguous_names.clear();
        self.external_package.clear();
        if self
            .b
            .implied
            .as_ref()
            .is_some_and(|t| t.from == self.b.elements.len())
        {
            self.b.implied = None;
            self.b.implied_from = None;
            self.b.semantic_ownership = None;
        }
        let mut qualified_by_id: HashMap<Uuid, &Vec<String>> = HashMap::new();
        for (id, segments) in names {
            let Ok(id) = Uuid::parse_str(id) else {
                continue;
            };
            let qualified = segments.join("::");
            // Alternate textual UUID representations can occur as separate
            // input keys. Contradictory names for the same parsed identity
            // must not make function admission depend on map iteration order.
            if let Some(previous) = qualified_by_id.insert(id, segments) {
                if previous != segments {
                    self.external_ambiguous_names.insert(previous.join("::"));
                    self.external_ambiguous_names.insert(qualified.clone());
                }
            }
            if let Some(previous) = self.external_by_name.get(&qualified) {
                if *previous != id {
                    self.external_ambiguous_names.insert(qualified.clone());
                }
            }
            if let Some(last) = segments.last() {
                self.external_names.insert(id, last.clone());
            }
            if let Some(first) = segments.first() {
                self.external_package.insert(id, first.clone());
            }
            self.external_by_name.insert(qualified, id);
        }
        if self.b.implied.is_none() {
            self.b.external_implied_names = self.external_by_name.clone();
            self.b.recorded_lookup_graph = None;
            self.b.recorded_lookup_prefix = None;
            self.b.positional_redefinitions = None;
            self.b.supported_implied = None;
            self.b.inherited_cache.clear();
            self.b.inherited_by_heritage.clear();
            self.import_truncated.clear();
        }
        self.b
            .library_names_changed(self.b.implied.is_some(), dynamic_was_current);
        self.name_memo.clear();
    }

    /// Resolve a `::`-separated qualified name (quoted segments allowed)
    /// from the model's root namespace. This compatibility lookup also accepts
    /// anonymous reference locators used by interchange replay; finding an
    /// element does not imply it has a semantic `name` or `qualifiedName`.
    /// Use [`Self::resolve_semantic_qualified`] to exclude those locators.
    pub fn resolve_qualified(&mut self, name: &str) -> Option<ElementRef> {
        self.resolve_segments(&split_qualified(name))
    }

    /// Resolve a root-qualified name without accepting compatibility locators
    /// as semantic names. Alias Memberships remain named independently of
    /// their target. This uses the same supported lookup rules as
    /// [`Self::resolve_qualified`]; it is not a completeness certificate for
    /// namespace resolution in unsupported inheritance/import contexts.
    pub fn resolve_semantic_qualified(&mut self, name: &str) -> Option<ElementRef> {
        let mut scope = Some(0);
        let mut result = None;
        // Check every qualifier as well: a named child of an anonymous
        // reference must not become accessible through its parent's locator.
        for (depth, name) in split_qualified(name).iter().enumerate() {
            let stamp = self.b.next_stamp();
            let LookupResult::Found(target, next_scope, membership) =
                self.b
                    .lookup_at_with_names(scope?, name, depth, stamp, LookupAccess::All, true)
            else {
                return None;
            };
            let target = ElementRef(target);
            let alias = membership.is_some_and(|m| {
                ["memberName", "memberShortName"].iter().any(|key| {
                    self.b.elements[m].props.get(key).and_then(|v| v.as_str()) == Some(name)
                })
            });
            if !alias
                && self.element_effective_name(target).as_ref() != Some(name)
                && self.element_short_name(target).as_ref() != Some(name)
            {
                return None;
            }
            result = Some(target);
            scope = next_scope;
        }
        result
    }

    /// Resolve a named built-in function for expression translation using
    /// the evaluator's admission rules. Resolved targets must have a known
    /// standard-library identity. Bare missing names retain standalone intrinsic
    /// support; ambiguous names and user declarations never select a built-in.
    /// Callers with a local argument environment must check those bindings first.
    /// The returned name identifies an implementation, not its supported arities.
    pub fn intrinsic_function_name(
        &mut self,
        scope: ScopeRef,
        name: &QualifiedName,
    ) -> Option<String> {
        self.b.intrinsic_function_name(scope.0, name)
    }

    /// Look up an interchange UUID independently of an element's name.
    /// Includes anonymous and library elements. Malformed or absent IDs
    /// return `None`; the ID belongs to this resolved model state.
    pub fn element_by_id(&mut self, id: &str) -> Option<ElementRef> {
        let id = Uuid::parse_str(id).ok()?;
        self.ensure_by_id();
        self.by_id.get(&id).copied().map(ElementRef)
    }

    fn resolve_segments(&mut self, segments: &[String]) -> Option<ElementRef> {
        if segments.is_empty() {
            return None;
        }
        let qn = QualifiedName {
            is_global: false,
            segments: segments
                .iter()
                .map(|value| Name {
                    value: value.clone(),
                    span: sysmlv2_syntax::span::Span::default(),
                })
                .collect(),
            span: sysmlv2_syntax::span::Span::default(),
        };
        // Scope 0 is the shared root namespace.
        match self.b.resolve_unrestricted(0, &qn) {
            LookupResult::Found(elem, _, _) => Some(ElementRef(elem)),
            LookupResult::Missing | LookupResult::Ambiguous => None,
        }
    }

    /// Resolve and evaluate a `::`-qualified name, with the last
    /// segment evaluated as a chain step off the path prefix: in
    /// `P::t::volume` the usage `t` establishes the featuring context
    /// exactly as the chain form `t.volume` would, so redefinitions
    /// under `t` shadow the values inherited from its definition. When
    /// the chain shape does not apply (a single segment, a prefix that
    /// evaluates to a scalar, or a member only qualified lookup can
    /// reach), the element evaluates in its own scope as
    /// [`Self::evaluate`] does.
    ///
    /// # Panics
    ///
    /// Never in practice: the qualified name is split before it is read
    /// back, so its last segment is always present.
    pub fn evaluate_qualified(
        &mut self,
        name: &str,
    ) -> Result<crate::eval::Value, crate::eval::EvalError> {
        let segments = split_qualified(name);
        if segments.len() >= 2 {
            if let Some(receiver) = self.resolve_segments(&segments[..segments.len() - 1]) {
                let member = QualifiedName {
                    is_global: false,
                    segments: vec![Name {
                        value: segments.last().expect("nonempty").clone(),
                        span: sysmlv2_syntax::span::Span::default(),
                    }],
                    span: sysmlv2_syntax::span::Span::default(),
                };
                if let Some(out) = crate::eval::evaluate_member_of(self, receiver, &member) {
                    return out;
                }
            }
        }
        match self.resolve_segments(&segments) {
            Some(e) => crate::eval::evaluate_feature(self, e),
            None => Err(crate::eval::EvalError::Unresolved(name.to_string())),
        }
    }

    /// The value of the feature chain `root.m1.m2…` off an
    /// already-resolved root element: each member evaluates as a chain
    /// step over the value so far, so every receiver establishes the
    /// featuring context and redefinitions shadow inherited values —
    /// the textual chain semantics for hosts that hold the pieces of a
    /// chain (a hover site, a navigation target) rather than its text.
    pub fn evaluate_chain(
        &mut self,
        root: ElementRef,
        members: &[&QualifiedName],
    ) -> Result<crate::eval::Value, crate::eval::EvalError> {
        crate::eval::evaluate_chain_of(self, root, members)
    }

    /// The element's own body scope — where its members' simple names
    /// resolve from (the site scope for spelling decisions inside its
    /// body). `None` for elements without a body of their own.
    pub fn element_scope(&self, e: ElementRef) -> Option<ScopeRef> {
        self.b.elem_scope.get(&e.0).copied().map(ScopeRef)
    }

    /// The element's abstract-syntax metaclass name (e.g. `AttributeUsage`).
    /// The serialized `isComposite` of `e`, when the metaclass carries
    /// one (`None` otherwise) — referential usages (`ref part r : P;`)
    /// say `false`.
    pub fn is_composite(&self, e: ElementRef) -> Option<bool> {
        self.b.elements[e.0]
            .props
            .get("isComposite")
            .and_then(|v| v.as_bool())
    }

    pub fn element_type(&self, e: ElementRef) -> &'static str {
        self.b.elements[e.0].ty
    }

    /// The element's declared name, if any.
    pub fn element_name(&self, e: ElementRef) -> Option<&str> {
        self.b.elements[e.0]
            .props
            .get("declaredName")
            .and_then(|v| v.as_str())
    }

    /// The element's declared short name (`<shortName>`), when it has one.
    pub fn element_declared_short_name(&self, e: ElementRef) -> Option<&str> {
        self.b.elements[e.0]
            .props
            .get("declaredShortName")
            .and_then(|v| v.as_str())
    }

    /// The specification's `Element::shortName` — `effectiveShortName()`:
    /// the declared short name, or — for a Feature that declares neither
    /// name — the effective short name of the feature that names it (see
    /// [`Self::element_effective_name`]).
    pub fn element_short_name(&mut self, e: ElementRef) -> Option<String> {
        self.effective_short_name_of(e.0)
    }

    /// The name lookup keys the element under: the declared name, else the
    /// declared short name, else the syntactic effective name recorded at
    /// lowering — the last segment of the first redefined or referenced
    /// feature's written path (`attribute :>> mass` → `mass`), whether or
    /// not that reference resolved. Structural projections that must
    /// re-resolve the names they spell use this
    /// ([`Self::element_reference_spelling`] joins it); the
    /// specification's `name` is [`Self::element_effective_name`].
    pub fn element_lookup_name(&self, e: ElementRef) -> Option<String> {
        self.b
            .effective_name(e.0)
            .or_else(|| self.b.effective_hint.get(&e.0).cloned())
    }

    /// The specification's `Element::name` — `effectiveName()` (KerML
    /// 8.2.3.5): the declared name, else — for a Feature that declares
    /// neither a name nor a short name — the effective name of its
    /// naming feature: the feature it explicitly redefines,
    /// else a positional redefinition target in the owner's heritage, else
    /// the positional name of the library feature its membership
    /// kind implicitly redefines (a binary connector's ends `source` /
    /// `target`, a return parameter `result`, a subject `subj`, an
    /// invocation's positional argument the callee's parameter name, …),
    /// else the feature selected by its SysML reference naming rule.
    /// An anonymous feature chain does not inherit its last link's name.
    /// A naming feature that did not resolve names nothing, so an
    /// unresolved `:>> mass` is unnamed here where
    /// [`Self::element_lookup_name`] still answers `mass`. Never falls
    /// back to the short name (`qualifiedName` does).
    pub fn element_effective_name(&mut self, e: ElementRef) -> Option<String> {
        self.effective_name_of(e.0)
    }

    /// Whether the element carries a feature-value expression (`= …`).
    pub fn has_value(&self, e: ElementRef) -> bool {
        self.b.values.contains_key(&e.0)
    }

    /// All elements carrying feature-value expressions.
    pub fn features_with_values(&self) -> Vec<ElementRef> {
        let mut v: Vec<ElementRef> = self.b.values.keys().map(|&e| ElementRef(e)).collect();
        v.sort_by_key(|e| e.0);
        v
    }

    /// Evaluate the element's feature value (see [`crate::eval`]).
    pub fn evaluate(
        &mut self,
        e: ElementRef,
    ) -> Result<crate::eval::Value, crate::eval::EvalError> {
        crate::eval::evaluate_feature(self, e)
    }

    /// Evaluate a feature value and retain failures hidden by inherited-default
    /// fallback. The result matches [`Self::evaluate`]; reporting has separate
    /// bounded storage. Use [`crate::eval::EvaluationReport::into_checked_result`]
    /// to reject hidden failures or truncated diagnostics.
    pub fn evaluate_report(&mut self, e: ElementRef) -> crate::eval::EvaluationReport {
        crate::eval::evaluate_feature_report(self, e)
    }

    /// Integer cardinality bounds under the evaluator's supported rules.
    /// Local explicit bounds and eligible implicit SysML singleton declarations
    /// take precedence. The implicit `[1]` applies to attribute/item/port usages
    /// owned by definitions/usages without explicit owned subsettings; connection
    /// usages and their subtypes are excluded. Otherwise, bounds intersect across
    /// explicit subsettings/redefinitions and supported positional parameter/end
    /// redefinitions. With no applicable inherited bounds, the default is `[0..*]`.
    ///
    /// Exactness refers to integer representation, not complete normative
    /// multiplicity semantics. Other specialization kinds and implied constraint
    /// families are not implemented. Body ranges and named multiplicity subsets
    /// support exact literals and stored feature references. Inherited reference
    /// valuations select a unique effective feature by referent identity and
    /// supported Redefinition edges, independent of reference spelling. Incomplete
    /// or ambiguous selection and nonliteral bounds during calculation calls
    /// remain unknown. Receiver provider proofs admit complete nonrecursive,
    /// unfiltered namespace/member imports. Exact member imports do not require
    /// unrelated imports in their declaring namespace to be complete. Missing
    /// providers, recursive/filtered imports, chain bases, attached metadata and
    /// cycles remain unknown. This is a receiver/inherited-provider proof, not
    /// a certification of lexical lookup completeness or whole-model validity.
    /// Reference resolution retains its existing identity contract. Selected
    /// feature values support contextual scalar formulas, resolving each dependency
    /// lexically before identity-based selection in the receiver. Contextual calls,
    /// member navigation, cycles and exhausted budgets remain unknown. Broader
    /// local formula evaluation is retained before rebasing. Package references
    /// retain lexical identity while their scalar dependencies keep the receiver.
    /// Unknown receiver defaults stay unknown.
    /// Local bounds take precedence; this is not a conformance check against
    /// every inherited restriction or an implementation of `Type::multiplicities`.
    ///
    /// Without local bounds establishing the result, unresolved/unsupported
    /// owned subsettings and inheritance cycles return `None`. Also returns
    /// `None` for multiple local multiplicities, invalid evaluated ranges or
    /// unevaluable bounds; the inner `None` denotes an unbounded upper
    /// limit. Counts outside
    /// `i128` are unevaluable. This does not instantiate collection members.
    pub fn effective_cardinality(&mut self, e: ElementRef) -> Option<(i128, Option<i128>)> {
        crate::eval::effective_cardinality(self, e)
    }

    /// Whether `e` is a collection by the implicit default alone: an
    /// attribute, item or port usage that a package or another non-type
    /// namespace owns, with no multiplicity, subsetting or redefinition of
    /// its own. Such a usage evaluates as `[0..*]`, and declaring `[1]`
    /// makes it one value; a parameter, connector end, reference usage or
    /// explicitly open multiplicity is never reported here.
    pub fn implicit_open_multiplicity(&mut self, e: ElementRef) -> bool {
        crate::eval::implicit_open_multiplicity(self, e)
    }

    /// Render an evaluated value for display with model context:
    /// element results (enum literals, referenced features) show their
    /// declared (or short) name instead of `Display`'s opaque
    /// `<element>`, recursively through quantities, instances, and
    /// sequences. Everything else matches the value's own `Display`.
    pub fn render_value(&self, v: &crate::eval::Value) -> String {
        self.render_value_with(v, false)
    }

    /// [`Self::render_value`] for glanceable surfaces (editor hints and
    /// hovers): a rational without a terminating decimal expansion shows
    /// as an approximate decimal (`≈0.3333333333333333`) rather than the
    /// exact fraction.
    pub fn render_value_approx(&self, v: &crate::eval::Value) -> String {
        self.render_value_with(v, true)
    }

    fn render_value_with(&self, v: &crate::eval::Value, approx: bool) -> String {
        use crate::eval::Value;
        let leaf = |v: &Value| {
            if approx {
                v.to_approx_string()
            } else {
                v.to_string()
            }
        };
        match v {
            Value::Element(e) | Value::Unbound(e) | Value::UnboundMember(e) => {
                let el = &self.b.elements[e.0];
                el.props
                    .get("declaredName")
                    .or_else(|| el.props.get("declaredShortName"))
                    .and_then(|n| n.as_str())
                    .map(str::to_string)
                    .unwrap_or_else(|| v.to_string())
            }
            Value::Quantity(n, u) => {
                format!("{} [{}]", self.render_value_with(n, approx), u.display())
            }
            Value::Instance {
                ty_name, fields, ..
            } => {
                let fields = fields
                    .iter()
                    .map(|(name, v)| format!("{name} = {}", self.render_value_with(v, approx)))
                    .collect::<Vec<_>>()
                    .join(", ");
                format!("{ty_name}({fields})")
            }
            Value::Sequence(s) if s.is_empty() => v.to_string(),
            Value::Sequence(s) => {
                let items = s
                    .iter()
                    .map(|v| self.render_value_with(v, approx))
                    .collect::<Vec<_>>()
                    .join(", ");
                format!("({items})")
            }
            _ => leaf(v),
        }
    }

    /// Evaluate an arbitrary expression with its references resolving from
    /// `scope` (see [`crate::eval`]).
    pub fn evaluate_in(
        &mut self,
        scope: ScopeRef,
        expr: &Expr,
    ) -> Result<crate::eval::Value, crate::eval::EvalError> {
        crate::eval::evaluate_expr_in(&mut self.b, scope.0, expr)
    }

    /// As [`Self::evaluate_in`], retaining bounded diagnostic causes hidden by
    /// inherited-default fallback. Source identity follows the same contract;
    /// use [`Self::with_source`] for syntax from a particular declaration.
    /// A clean report does not certify that a returned value is concrete.
    pub fn evaluate_in_report(
        &mut self,
        scope: ScopeRef,
        expr: &Expr,
    ) -> crate::eval::EvaluationReport {
        crate::eval::evaluate_expr_report(&mut self.b, scope.0, expr)
    }

    /// Run model queries using the source identity of an expression's declaration.
    /// This selects source-site identity bindings only; lexical and receiver scopes
    /// remain the explicit arguments of each query. `owner` must belong to this model.
    /// Nested calls and unwinding restore the caller's source identity. The callback
    /// should query the model rather than replace it or its source declarations.
    pub fn with_source<T>(&mut self, owner: ElementRef, read: impl FnOnce(&mut Self) -> T) -> T {
        struct Restore<'a> {
            model: &'a mut ResolvedModel,
            previous: Option<usize>,
        }
        impl Drop for Restore<'_> {
            fn drop(&mut self) {
                self.model.b.identity_origin_unit = self.previous;
            }
        }
        let previous = self.b.set_identity_origin(owner.0);
        let guard = Restore {
            model: self,
            previous,
        };
        read(&mut *guard.model)
    }

    /// Evaluate a chain of member names on an already evaluated receiver value.
    /// All member names are read under the current source context (see
    /// [`Self::with_source`]); the receiver retains the identity it already has.
    /// The links share one evaluation budget and use ordinary chain semantics.
    pub fn evaluate_value_chain(
        &mut self,
        target: crate::eval::Value,
        members: &[&QualifiedName],
    ) -> Result<crate::eval::Value, crate::eval::EvalError> {
        crate::eval::evaluate_value_chain(self, target, members)
    }

    /// The measurement unit denoted by a bracket's unit expression
    /// (`[mm]`, `[km/h]`), with references resolving from `scope`. Unlike
    /// [`Self::evaluate_in`] on the whole bracket, this reads *only* the
    /// unit part — the magnitude may be unbound. Used by the solver to
    /// tag quantity terms it cannot constant-fold.
    pub fn unit_of_in(
        &mut self,
        scope: ScopeRef,
        expr: &Expr,
    ) -> Result<crate::eval::Unit, crate::eval::EvalError> {
        crate::eval::unit_of_expr_in(&mut self.b, scope.0, expr)
    }

    /// The model's root namespace scope — every document root shares it,
    /// so qualified names starting at any file's top-level packages
    /// resolve from here. The natural `scope` for [`Self::query`].
    pub fn root_scope(&self) -> ScopeRef {
        ScopeRef(0)
    }

    /// Evaluate an ad-hoc *query* expression (e.g. one parsed with
    /// `sysmlv2_syntax::parser::parse_expression`) with its references
    /// resolving from `scope`. Like [`Self::evaluate_in`], plus the
    /// query-mode extensions: `istype`/`as` on a model element classify
    /// the declaration itself closed-world (a miss against a user-defined
    /// type is `false`, not undecided), and the reflection intrinsics
    /// `ownedMember(x)` / `ownedFeature(x)` enumerate an element's owned
    /// members as sequences. Feature-value evaluation semantics
    /// ([`Self::evaluate`]) are unaffected.
    pub fn query(
        &mut self,
        scope: ScopeRef,
        expr: &Expr,
    ) -> Result<crate::eval::Value, crate::eval::EvalError> {
        crate::eval::evaluate_query_in(&mut self.b, scope.0, expr)
    }

    /// Build the relationship → owning-element map on first use. An
    /// implied relationship is owned through the side table, not its
    /// owner's row.
    fn ensure_rel_owner(&mut self) {
        self.sync_semantic_publication();
        let n = self.b.elements.len();
        if self.rel_owner.len() != n {
            // A build whose rows below its own are its prepared library's
            // frozen rows reads their relationships' owners from the
            // library's table.
            let library = self.b.prepared_from.as_ref().filter(|prepared| {
                self.b.elements.base_untouched()
                    && Arc::ptr_eq(
                        self.b.elements.base_arc(),
                        prepared.builder.elements.base_arc(),
                    )
            });
            let (mut map, from) = match library {
                Some(prepared) => {
                    let owners = Arc::clone(prepared.library_rel_owners());
                    let from = owners.len();
                    (crate::layered::LayeredVec::over(owners), from)
                }
                None => (crate::layered::LayeredVec::default(), 0),
            };
            map.resize(n, None);
            for i in from..n {
                for &r in &self.b.elements[i].owned_relationships {
                    map[r] = Some(i);
                }
            }
            if let Some(view) = &self.b.semantic_ownership {
                for (relationship, owner) in view.relationship_owners() {
                    map[relationship] = Some(owner);
                }
            }
            self.rel_owner = map;
        }
    }

    /// Build the membership → owned-member map on first use.
    fn ensure_rel_member(&mut self) {
        self.sync_semantic_publication();
        if self.rel_member.len() != self.b.elements.len() {
            let mut map = vec![None; self.b.elements.len()];
            for (i, el) in self.b.elements.iter().enumerate() {
                if let Some(r) = el.owning_relationship {
                    map[r] = Some(i);
                }
            }
            self.rel_member = map;
        }
    }

    /// The element's lookup names ([`Self::element_lookup_name`]) from its
    /// document root, raw (unescaped) and root first — the segments a
    /// re-resolvable reference spelling joins. `None` when the element or
    /// an ancestor has no lookup name.
    fn lookup_name_segments(&mut self, e: ElementRef) -> Option<Vec<String>> {
        self.ensure_rel_owner();
        let mut segs: Vec<String> = Vec::new();
        let mut cur = e.0;
        loop {
            let el = &self.b.elements[cur];
            // The document root namespace is unnamed; reaching it (or any
            // unowned element) ends the walk.
            let Some(rel) = el.owning_relationship else {
                break;
            };
            segs.push(self.element_lookup_name(ElementRef(cur))?);
            cur = self.rel_owner[rel]?;
        }
        if segs.is_empty() {
            return None;
        }
        segs.reverse();
        Some(segs)
    }

    /// The specification's `Element::qualifiedName`: the owning
    /// namespace's qualified name and the element's `escapedName()` — its
    /// [effective name](Self::element_effective_name), else its effective
    /// short name — joined with `::` from the document root, non-basic
    /// names quoted. `None` when the element or an ancestor is unnamed or
    /// is owned other than through a membership (it then has no
    /// `owningNamespace`).
    ///
    /// KerML 8.3.2.1 `escapedName`: a name with the *form* of a basic
    /// name is returned as-is — the spelling the pilot implementation
    /// derives and the normative library ids hash — so a reserved word
    /// used as a name stays bare here (`ControlFunctions::if`). It is a
    /// model property, not parseable text: splice
    /// [`Self::element_reference_spelling`] into source instead.
    pub fn element_qualified_name(&mut self, e: ElementRef) -> Option<String> {
        let segs = self.qualified_name_segments(e)?;
        Some(
            segs.iter()
                .map(|s| sysmlv2_syntax::ast::escape_name(s))
                .collect::<Vec<_>>()
                .join("::"),
        )
    }

    /// The element's lookup-name path spelled as reference text that
    /// re-parses in either dialect and re-resolves to the element: every
    /// segment that is a reserved word of SysML or KerML, or not a basic
    /// name, is quoted (`'part'::'view'` for the element whose qualified
    /// name is `part::view`). Joins [`Self::element_lookup_name`] rather
    /// than the specification's name, so an unnamed feature is spelled by
    /// the name it was written under — the segment name resolution finds
    /// it by — even where the specification's `qualifiedName` would give
    /// another (an implied positional name) or none (an unresolved naming
    /// reference). Text going into a known unit can use its own table
    /// instead: [`Self::unit_dialect`] with
    /// [`sysmlv2_syntax::name::spell_path`].
    pub fn element_reference_spelling(&mut self, e: ElementRef) -> Option<String> {
        let segs = self.lookup_name_segments(e)?;
        Some(sysmlv2_syntax::name::spell_path(None, &segs))
    }

    /// The dialect of a unit, by its name (`.kerml` is KerML, anything
    /// else SysML): the reserved-word table that governs text spliced
    /// into it. `None` for an unknown unit index.
    pub fn unit_dialect(&self, unit: usize) -> Option<Dialect> {
        self.unit_meta
            .get(unit)
            .map(|(name, _)| crate::model::Model::dialect_for(name))
    }

    // ---- typed navigation (the transformation SDK's read side) ----

    /// Every resolved reference site in the user units, in resolution
    /// order (library-internal sites are not recorded).
    pub fn reference_sites(&self) -> &[RefSite] {
        &self.b.ref_sites
    }

    /// The reference sites that resolve to `e` — find-usages. A rename of
    /// `e` must respell each site's `name_span` text (plus the
    /// declaration site).
    pub fn references_to(&self, e: ElementRef) -> Vec<RefSite> {
        self.b
            .ref_sites
            .iter()
            .filter(|s| s.target == e)
            .cloned()
            .collect()
    }

    /// The written `: T` typing clauses of `e`'s declaration, in source
    /// order: (unit index, span of the qualified name as written; a
    /// conjugated `~P` typing's span covers `P` only). Empty for untyped
    /// features and typings not written as names. The enabling record
    /// for in-place declared-type edits.
    pub fn typing_spans(&self, e: ElementRef) -> Vec<(usize, Span)> {
        let unit = self.b.unit_of_elem(e.0);
        self.b
            .spec_targets
            .iter()
            .filter(|(owner, kind, _, _)| *owner == e.0 && *kind == "FeatureTyping")
            .map(|(_, _, _, qn)| (unit, qn.span))
            .collect()
    }

    /// The written specialization clauses of `e`'s declaration (typing,
    /// subsetting, redefinition — any kind), in source order: (unit
    /// index, span of the qualified name as written).
    pub fn specialization_spans(&self, e: ElementRef) -> Vec<(usize, Span)> {
        let unit = self.b.unit_of_elem(e.0);
        self.b
            .spec_targets
            .iter()
            .filter(|(owner, _, _, _)| *owner == e.0)
            .map(|(_, _, _, qn)| (unit, qn.span))
            .collect()
    }

    /// Where `e`'s name is declared: (unit index, span of the name
    /// token). `None` for anonymous elements and everything synthesized
    /// (memberships, implied features, expression scaffolding).
    pub fn declaration_site(&self, e: ElementRef) -> Option<(usize, Span)> {
        let span = *self.b.decl_spans.get(&e.0)?;
        Some((self.b.unit_of_elem(e.0), span))
    }

    /// 1-based lines of a span's endpoints in `unit` — layout
    /// questions (is this construct written on one line?).
    pub fn span_lines(&self, unit: usize, span: Span) -> Option<(u32, u32)> {
        let (_, index) = self.unit_meta.get(unit)?;
        Some((
            index.line_col(span.start).line,
            index.line_col(span.end).line,
        ))
    }

    /// Textual `private import` members that provably feed nothing in
    /// their unit: (import relationship, unit index, span of the whole
    /// import member — the removal span). Two conditions, both required:
    ///
    /// 1. No lookup resolved a name through the import in this build
    ///    (recorded at the admitted-hit sites of the resolver walk).
    /// 2. Nothing the unit references lives under the imported namespace
    ///    (owner-chain check). Condition 1 alone is resolver-*order*
    ///    truth, not semantic truth — a name can resolve through an
    ///    implied library base's own import before the unit's import is
    ///    consulted, yet removing the import would still break the file
    ///    in tools with a different search order.
    ///
    /// Callers filter to their user units: under a sealed library
    /// snapshot, library-internal resolution replays without lookups, so
    /// library imports always fail condition 1. Public (and KerML
    /// default-visibility) imports are never reported — they re-export.
    pub fn unused_private_imports(&mut self) -> Vec<(ElementRef, ElementRef, usize, Span)> {
        self.unused_private_imports_in(None)
    }

    /// User-unit imports declared without a visibility keyword, in
    /// declaration order: (import relationship, unit, member span).
    /// The unit and span of a user-unit import declaration (the element
    /// a [`RefSite::via_imports`] entry names). `None` for library
    /// imports and for elements that are not imports.
    pub fn import_extent(&self, import: ElementRef) -> Option<(usize, Span)> {
        self.b
            .user_imports
            .iter()
            .find(|i| i.rel == import.0)
            .map(|i| (self.b.unit_of_elem(i.rel), i.span))
    }

    pub fn imports_without_visibility(&self) -> Vec<(ElementRef, usize, Span)> {
        self.b
            .user_imports
            .iter()
            .filter(|i| i.visibility.is_none())
            .map(|i| (ElementRef(i.rel), self.b.unit_of_elem(i.rel), i.span))
            .collect()
    }

    /// The visibility an import's dependents require, judged from the
    /// access each reference site walked it under — the check the
    /// resolver itself applied: `private` when every walk ran with full
    /// access (lexically from inside the importing namespace, nested
    /// namespaces included), `protected` when the most restrictive walk
    /// came through a specialization of the importing type, `public`
    /// when any walk came from outside. `None` when `import` is not a
    /// user-unit import or its own target does not resolve (the import
    /// is diagnosed on its own; no advice is meaningful).
    pub fn import_visibility_advice(
        &mut self,
        import: ElementRef,
    ) -> Option<ImportVisibilityAdvice> {
        let imp = self
            .b
            .user_imports
            .iter()
            .find(|i| i.rel == import.0)?
            .clone();
        let target = self.b.elements[imp.rel]
            .props
            .get("importedNamespace")
            .or_else(|| self.b.elements[imp.rel].props.get("importedMembership"))?;
        if target.get("@ref").is_some() {
            return None;
        }
        let mut outside_sites = Vec::new();
        let mut most_restrictive = AccessMode::Any;
        for site in &self.b.ref_sites {
            let Some((_, access)) = site.via_imports.iter().find(|(i, _)| *i == import) else {
                continue;
            };
            most_restrictive = most_restrictive.min(*access);
            if *access != AccessMode::Any {
                outside_sites.push((site.unit, site.span));
            }
        }
        outside_sites.sort_unstable_by_key(|(unit, span)| (*unit, span.start, span.end));
        outside_sites.dedup();
        let recommended = match most_restrictive {
            AccessMode::Any => "private",
            AccessMode::Protected => "protected",
            AccessMode::Public => "public",
        };
        let owner = self.b.scopes[imp.scope].owner;
        let namespace = owner.and_then(|o| self.element_qualified_name(ElementRef(o)));
        Some(ImportVisibilityAdvice {
            import,
            unit: self.b.unit_of_elem(imp.rel),
            span: imp.span,
            declared: imp.visibility.map(|v| match v {
                Visibility::Public => "public",
                Visibility::Private => "private",
                Visibility::Protected => "protected",
            }),
            recommended,
            outside_sites,
            namespace,
        })
    }

    /// The conservative unused-import check restricted to the supplied model
    /// units. Filtering happens before candidate/reference analysis; passing an
    /// empty slice performs no analysis. The result keeps declaration order.
    pub fn unused_private_imports_for_units(
        &mut self,
        units: &[usize],
    ) -> Vec<(ElementRef, ElementRef, usize, Span)> {
        self.unused_private_imports_in(Some(&units.iter().copied().collect()))
    }

    fn unused_private_imports_in(
        &mut self,
        units: Option<&HashSet<usize>>,
    ) -> Vec<(ElementRef, ElementRef, usize, Span)> {
        let candidates: Vec<(usize, Span, usize)> = self
            .b
            .user_imports
            .iter()
            .filter(|imp| {
                imp.visibility == Some(Visibility::Private)
                    && !self.b.used_imports.contains(&imp.rel)
                    && units.is_none_or(|us| us.contains(&self.b.unit_of_elem(imp.rel)))
            })
            .map(|imp| (imp.rel, imp.span, self.b.unit_of_elem(imp.rel)))
            .collect();
        if candidates.is_empty() {
            return Vec::new();
        }
        let candidate_units: HashSet<_> = candidates.iter().map(|(_, _, unit)| *unit).collect();
        let sites: Vec<_> = self
            .b
            .ref_sites
            .iter()
            .filter(|s| candidate_units.contains(&s.unit))
            .map(|s| {
                (
                    s.unit,
                    s.span,
                    s.target,
                    s.kind == "importedNamespace" || s.kind == "importedMembership",
                )
            })
            .collect();
        // Source-range lookup retains the original reference-site ordering for
        // the rare case of several targets contained in one import member.
        let mut imports =
            std::collections::BTreeMap::<(usize, u32), Vec<(u32, ElementRef, usize)>>::new();
        let mut ancestry = HashMap::<ElementRef, Vec<ElementRef>>::new();
        let mut extents = HashMap::<(usize, ElementRef), (u32, u32)>::new();
        for (order, (unit, span, target, import)) in sites.into_iter().enumerate() {
            if import {
                imports
                    .entry((unit, span.start))
                    .or_default()
                    .push((span.end, target, order));
            }
            let ancestors = ancestry.entry(target).or_insert_with(|| {
                let mut chain = vec![target];
                let mut e = target;
                // Match the original conservative owner walk exactly: the
                // target itself plus at most 64 owning elements.
                for _ in 0..64 {
                    let Some(owner) = self.owner(e) else {
                        break;
                    };
                    chain.push(owner);
                    e = owner;
                }
                chain
            });
            for &ancestor in ancestors.iter() {
                extents
                    .entry((unit, ancestor))
                    .and_modify(|(start, end)| {
                        *start = (*start).min(span.start);
                        *end = (*end).max(span.end);
                    })
                    .or_insert((span.start, span.end));
            }
        }
        let mut out = Vec::new();
        for (rel, span, unit) in candidates {
            let target = imports
                .range((unit, span.start)..=(unit, span.end))
                .flat_map(|(_, sites)| sites.iter())
                .filter(|(end, _, _)| *end <= span.end)
                .min_by_key(|(_, _, order)| *order)
                .map(|(_, target, _)| *target);
            let Some(target) = target else {
                continue;
            };
            // There is a feeding reference outside the candidate precisely
            // when the span envelope extends beyond its removal range.
            let feeds = extents
                .get(&(unit, target))
                .is_some_and(|(start, end)| *start < span.start || *end > span.end);
            if !feeds {
                out.push((ElementRef(rel), target, unit, span));
            }
        }
        out
    }

    /// The declared names of `e` and everything under it (owned members,
    /// transitively to a small depth) — the textual surface an import of
    /// `e` can supply. Conservative by design: used by the unused-import
    /// check's textual condition, where over-listing only suppresses a
    /// finding.
    pub fn namespace_member_names(&mut self, e: ElementRef) -> Vec<String> {
        self.namespace_member_names_many(&[e])
            .remove(&e)
            .unwrap_or_default()
    }

    /// Enumerate several imported namespaces using one owned-members index.
    /// Each name vector is identical to `namespace_member_names`, including
    /// traversal order and its conservative depth/name limits. The index is
    /// local to this call, so model edits cannot leave stale entries.
    pub fn namespace_member_names_many(
        &mut self,
        targets: &[ElementRef],
    ) -> HashMap<ElementRef, Vec<String>> {
        if targets.is_empty() {
            return HashMap::new();
        }
        self.ensure_rel_owner();
        let mut members = vec![Vec::new(); self.b.elements.len()];
        for (i, element) in self.b.elements.iter().enumerate() {
            if let Some(rel) = element.owning_relationship {
                if self.b.elements[rel].ty.ends_with("Membership") {
                    if let Some(owner) = self.rel_owner[rel] {
                        members[owner].push(i);
                    }
                }
            }
        }
        let mut names = HashMap::new();
        for &target in targets {
            names.entry(target).or_insert_with(|| {
                let mut out = Vec::new();
                let mut frontier = vec![(target.0, 0usize)];
                while let Some((cur, depth)) = frontier.pop() {
                    for key in ["declaredName", "declaredShortName"] {
                        if let Some(name) =
                            self.b.elements[cur].props.get(key).and_then(|v| v.as_str())
                        {
                            out.push(name.to_string());
                        }
                    }
                    if depth < 8 && out.len() < 4096 {
                        frontier.extend(members[cur].iter().map(|&m| (m, depth + 1)));
                    }
                }
                out
            });
        }
        names
    }

    /// The element whose declared-name span contains `offset` in `unit` —
    /// the position→element inverse of [`Self::declaration_site`] (IDE
    /// "what is under the cursor" on a declaration). The narrowest
    /// matching span wins (a short name nested in another's range).
    pub fn declaration_at(&self, unit: usize, offset: u32) -> Option<ElementRef> {
        self.b
            .decl_spans
            .iter()
            .filter(|(&e, s)| s.start <= offset && offset < s.end && self.b.unit_of_elem(e) == unit)
            .min_by_key(|(_, s)| s.len())
            .map(|(&e, _)| ElementRef(e))
    }

    /// The element that owns `e` (through its owning relationship);
    /// `None` for document roots. A relationship element (Membership,
    /// FeatureTyping, …) answers the element whose owned-relationship
    /// list carries it, so owner chains climb out of [`RefSite::owner`]
    /// property carriers to the declaration they were written in.
    pub fn owner(&mut self, e: ElementRef) -> Option<ElementRef> {
        self.ensure_rel_owner();
        match self.b.elements[e.0].owning_relationship {
            Some(rel) => self.rel_owner[rel].map(ElementRef),
            None => self.rel_owner[e.0].map(ElementRef),
        }
    }

    /// The relationships `e` owns directly (`Element::ownedRelationship`:
    /// its memberships, imports, specializations, typings, annotations,
    /// …), in declaration order — the explicit ones. The implied
    /// specializations are listed by [`Self::implied_relationships`] and
    /// included by the relationship families of [`Self::derived`]
    /// (`ownedSpecialization`, `ownedSubsetting`, …).
    pub fn owned_relationships(&self, e: ElementRef) -> Vec<ElementRef> {
        self.b.elements[e.0]
            .owned_relationships
            .iter()
            .copied()
            .map(ElementRef)
            .collect()
    }

    /// The already-materialized semantic ownership view. Mutable entry points
    /// establish readiness; immutable source navigation deliberately stays raw.
    pub(super) fn projected_owned_relationships(&self, e: ElementRef) -> Vec<ElementRef> {
        match self.b.semantic_ownership.as_ref() {
            Some(view) => view
                .relationships(&self.b, e.0)
                .map(|rows| rows.iter().map(ElementRef).collect())
                .unwrap_or_default(),
            None => self.owned_relationships(e),
        }
    }

    /// Serialize a generated node with its real kind and reciprocal ownership.
    /// Source rows are never emitted through this path.
    pub(crate) fn generated_node_record(&self, e: ElementRef) -> Option<Map<String, Value>> {
        let view = self.b.semantic_ownership.as_ref()?;
        if !view.contains(e.0) {
            return None;
        }
        let node = &self.b.elements[e.0];
        let id = |index: usize| json!({"@id":self.b.elements[index].id.to_string()});
        let mut record = self.element_properties(e);
        if crate::metaclass::conforms(node.ty, "Feature") {
            generated_defaults::fill_owned_defaults(node.ty, &node.props, &mut record);
        }
        record.insert("@type".into(), json!(node.ty));
        record.insert("@id".into(), json!(node.id.to_string()));
        record.insert("elementId".into(), json!(node.id.to_string()));
        record.insert("isImpliedIncluded".into(), json!(true));
        record.insert(
            "ownedRelationship".into(),
            Value::Array(view.relationships(&self.b, e.0)?.iter().map(id).collect()),
        );
        record.insert(
            "owningRelationship".into(),
            node.owning_relationship.map(id).unwrap_or(Value::Null),
        );
        if crate::metaclass::conforms(node.ty, "Relationship") {
            record.insert(
                "ownedRelatedElement".into(),
                Value::Array(node.children.iter().copied().map(id).collect()),
            );
            record.insert(
                "owningRelatedElement".into(),
                view.generated_relationship_owner(e.0)
                    .map(id)
                    .unwrap_or(Value::Null),
            );
        }
        record.entry("aliasIds").or_insert_with(|| json!([]));
        record.entry("declaredName").or_insert(Value::Null);
        record.entry("declaredShortName").or_insert(Value::Null);
        Some(record)
    }

    /// Generated direct descendants, in relationship then child order. The
    /// full emitter follows this closure atomically from each source owner.
    pub(crate) fn generated_node_children(&self, e: ElementRef) -> Vec<ElementRef> {
        let Some(view) = self.b.semantic_ownership.as_ref() else {
            return Vec::new();
        };
        let Some(rows) = view.relationships(&self.b, e.0) else {
            return Vec::new();
        };
        rows.iter()
            .chain(self.b.elements[e.0].children.iter().copied())
            .filter(|&index| view.contains(index))
            .map(ElementRef)
            .collect()
    }

    /// The elements owned by `e` through its owned memberships, in
    /// declaration order — KerML `Namespace::ownedMember`.
    pub fn owned_members(&self, e: ElementRef) -> Vec<ElementRef> {
        self.b
            .owned_member_elems(e.0, false)
            .into_iter()
            .map(ElementRef)
            .collect()
    }

    /// The members owned by `e` via FeatureMembership kinds, in
    /// declaration order — KerML `Type::ownedFeature` (a package answers
    /// none; membership metaclass follows the owner).
    pub fn owned_features(&self, e: ElementRef) -> Vec<ElementRef> {
        self.b
            .owned_member_elems(e.0, true)
            .into_iter()
            .map(ElementRef)
            .collect()
    }

    /// The members `e` inherits through its specialization heritage —
    /// KerML `Type::inheritedMemberships`, answered by the resolver's own
    /// inheritance walk (the one name lookup uses). Private memberships
    /// do not inherit; **public and protected imported memberships re-export** through
    /// heritage (membership and namespace imports, `::**` and re-export
    /// chains included, filters applied). Removal is redefinition-driven,
    /// not name-driven, per KerML `removeRedefinedFeatures`: a member is
    /// dropped when another inherited candidate (transitively) redefines
    /// it (including a distinct Membership of the same Feature), when its
    /// own redefinition closure meets a feature **directly**
    /// redefined by one of `e`'s owned features (the normative
    /// `ownedFeature.redefinition.redefinedFeature` set is one hop), or
    /// under SysML's implicit same-name usage redefinition; same-name
    /// members of *unrelated* branches are all retained (lookup answers
    /// ambiguous — the memberships still inherit). Handles come in
    /// direct-base heritage order (each base's ancestors before the next
    /// base), preserving
    /// each base's public-before-protected membership order.
    ///
    /// Returns **Membership relationship handles**, per the normative
    /// operation: owning memberships for ordinary members, the imported
    /// member's home membership for imports, and **alias Memberships**
    /// of the heritage scopes (non-private). Navigate them with
    /// [`Self::membership_member`] / [`Self::membership_member_name`] /
    /// [`Self::membership_is_alias`]; the declaring namespace is the
    /// membership's [`Self::owner`].
    ///
    /// `include_implied` extends the walk over implied heritage —
    /// the SysML Tables 31/32 library bases (every `action` inherits
    /// `Actions::Action`'s members), binary connector bases, and
    /// semantic-metadata bases — at every level; `false` walks written
    /// specializations/typings only.
    ///
    /// The normative `excluded` namespace/type parameters are not taken
    /// (they are the OCL recursion's cycle-guard plumbing; the guard here
    /// is internal — [`Self::inheritance_walk_truncated`] reports when it
    /// cut the walk). Supported literal, null and metadata-access leaves without a body scope
    /// read their library heritage by element identity. Other elements without a
    /// body scope answer empty.
    pub fn inherited_memberships(
        &mut self,
        e: ElementRef,
        include_implied: bool,
    ) -> Vec<ElementRef> {
        let Some(&s) = self.b.elem_scope.get(&e.0) else {
            return self
                .b
                .literal_inherited_memberships(e.0, include_implied)
                .membership_order
                .into_iter()
                .map(ElementRef)
                .collect();
        };
        let bindings = self.b.inherited_bindings(s, include_implied);
        bindings
            .membership_order
            .iter()
            .copied()
            .map(ElementRef)
            .collect()
    }

    /// Whether the inheritance/import enumeration reached its depth budget.
    /// Scoped acyclic inheritance itself has no depth cap; supported scope-less
    /// expression heritage and contextual import operations have bounded traversal budgets.
    /// This does not report unsupported semantic dependencies; see
    /// [`Self::inheritance_incomplete`].
    pub fn inheritance_walk_truncated(&mut self, e: ElementRef, include_implied: bool) -> bool {
        let Some(&s) = self.b.elem_scope.get(&e.0) else {
            return self
                .b
                .literal_inherited_memberships(e.0, include_implied)
                .truncated;
        };
        self.b.inherited_bindings(s, include_implied).truncated
    }

    /// Whether this inheritance query has a known cyclic or unsupported
    /// positional dependency, hit an import-walk depth budget, or restored
    /// bootstrap lookup after selection exceeded its stabilization budget. `false`
    /// does not certify complete specification conformance: the fidelity of
    /// inheritance-dependent properties remains qualified. Compatibility
    /// exports permit unsupported semantics but refuse actual depth cuts.
    pub fn inheritance_incomplete(&mut self, e: ElementRef, include_implied: bool) -> bool {
        let Some(&s) = self.b.elem_scope.get(&e.0) else {
            let result = self.b.literal_inherited_memberships(e.0, include_implied);
            return result.incomplete || result.truncated;
        };
        let result = self.b.inherited_bindings(s, include_implied);
        result.incomplete || result.truncated || self.b.recorded_lookup_incomplete
    }

    /// [`Self::inherited_memberships`] projected to feature member
    /// *elements*, selected by the **member's** metaclass — the view a
    /// compartment or an object API wants, in which a package-owned part
    /// arriving through an imported membership counts as a feature.
    /// KerML `Type::inheritedFeature` selects by the *membership* kind
    /// (`inheritedMembership->selectByKind(FeatureMembership).memberFeature`),
    /// which the derived-property read API answers under that name
    /// (`derived(e, "inheritedFeature")`); this accessor deliberately
    /// keeps the wider view.
    pub fn inherited_features(&mut self, e: ElementRef, include_implied: bool) -> Vec<ElementRef> {
        let Some(&s) = self.b.elem_scope.get(&e.0) else {
            let inherited = self.b.literal_inherited_memberships(e.0, include_implied);
            let mut seen = HashSet::new();
            return inherited
                .membership_order
                .into_iter()
                .filter_map(|membership| {
                    let member = self.b.stored_membership_member(membership)?;
                    (crate::metaclass::conforms(self.b.elements[member].ty, "Feature")
                        && seen.insert(member))
                    .then_some(member)
                })
                .map(ElementRef)
                .collect();
        };
        let bindings = self.b.inherited_bindings(s, include_implied);
        bindings
            .members
            .iter()
            .map(|&(elem, _)| ElementRef(elem))
            .filter(|m| crate::metaclass::conforms(self.b.elements[m.0].ty, "Feature"))
            .collect()
    }

    /// The member a Membership binds: the owned element for owning
    /// membership kinds, the referenced `memberElement` for
    /// non-owning Memberships (aliases, `first X;` markers, transition
    /// sources). `None` when the reference did not resolve or `m` is
    /// not a membership.
    pub fn membership_member(&mut self, m: ElementRef) -> Option<ElementRef> {
        if !crate::metaclass::conforms(self.b.elements[m.0].ty, "Membership") {
            return None; // a FeatureValue is an OwningMembership too
        }
        self.ensure_rel_member();
        if let Some(Some(member)) = self.rel_member.get(m.0) {
            return Some(ElementRef(*member));
        }
        self.ensure_by_id();
        self.prop_target(m.0, "memberElement").map(ElementRef)
    }

    /// The name a Membership binds its member under: the membership's
    /// declared `memberName` (an alias's own name), else the member's
    /// effective name.
    pub fn membership_member_name(&mut self, m: ElementRef) -> Option<String> {
        if let Some(n) = self.b.elements[m.0]
            .props
            .get("memberName")
            .and_then(|a| a.as_str())
        {
            return Some(n.to_string());
        }
        let member = self.membership_member(m)?;
        self.element_lookup_name(member)
    }

    /// Whether `m` is an alias Membership: a plain `Membership` carrying
    /// its own member name and owning no element.
    pub fn membership_is_alias(&self, m: ElementRef) -> bool {
        self.b.elements[m.0].ty == "Membership"
            && (self.b.elements[m.0]
                .props
                .get("memberName")
                .is_some_and(|v| !v.is_null())
                || self.b.elements[m.0]
                    .props
                    .get("memberShortName")
                    .is_some_and(|v| !v.is_null()))
    }

    /// `e`'s owned features followed by everything it inherits,
    /// shadowing already applied — the "effective members" view a
    /// rendering compartment or an object-API `features` accessor wants.
    /// `include_implied` as for [`Self::inherited_features`]: `true`
    /// adds the members of the implied library bases (every part's
    /// generic library ports, every action's `start`/`done`), `false`
    /// stops at the written heritage.
    pub fn effective_features(&mut self, e: ElementRef, include_implied: bool) -> Vec<ElementRef> {
        let mut out = self.owned_features(e);
        let mut seen: HashSet<ElementRef> = out.iter().copied().collect();
        for m in self.inherited_features(e, include_implied) {
            if seen.insert(m) {
                out.push(m);
            }
        }
        out
    }

    /// Every element of the given abstract-syntax metaclass (library
    /// elements included — filter with [`Self::is_library_element`];
    /// implied relationships excluded as in [`Self::elements`]), in
    /// creation (document) order.
    pub fn elements_of_metaclass(&self, ty: &str) -> Vec<ElementRef> {
        (0..self.b.explicit_len())
            .filter(|&i| self.b.elements[i].ty == ty)
            .map(ElementRef)
            .collect()
    }

    /// Whether `e` belongs to a loaded library unit (resolution target
    /// only — never serialized, never a transformation target).
    pub fn is_library_element(&self, e: ElementRef) -> bool {
        self.b
            .semantic_ownership
            .as_ref()
            .map_or(e.0, |view| view.source_anchor(e.0))
            < self.b.lib_boundary
    }

    /// `Type::isAbstract` as declared: the `abstract` keyword, or a
    /// variation or enumeration definition or a variation usage, which the
    /// lowering marks abstract.
    pub fn is_abstract(&self, e: ElementRef) -> bool {
        self.b.elements[e.0]
            .props
            .get("isAbstract")
            .and_then(|v| v.as_bool())
            .unwrap_or(false)
    }

    /// Evaluated numeric bounds of `e`'s *explicitly declared*
    /// header multiplicity: `[l..u]` → `(l, u)`, `[u]` → `(u, u)` except `[*]`
    /// → `(0, ∞)`. This compatibility accessor returns approximate `f64`
    /// values; semantic validation retains exact values. Body/named numeric
    /// domains do not become a declaration of their own Feature cardinality.
    /// `None` when `e` declares no multiplicity of its own (inherited
    /// ones are not walked) or a bound does not evaluate to a number.
    pub fn declared_multiplicity(&mut self, e: ElementRef) -> Option<(f64, f64)> {
        // Evaluating the bounds needs the builder mutably, so the clause
        // is copied out of the table first; the table itself is not walked.
        let (scope, m) = self
            .b
            .declared_multiplicity_of(e.0)
            .map(|(s, m)| (s, m.clone()))?;
        let as_num = |v: crate::eval::Value| match v {
            crate::eval::Value::Integer(i) => Some(i as f64),
            crate::eval::Value::Rational(r) => Some(r.to_f64()),
            crate::eval::Value::Real(f) => Some(f),
            _ => None,
        };
        let origin = self.b.set_identity_origin(e.0);
        let result = (|| {
            let hi = as_num(crate::eval::evaluate_expr_in(&mut self.b, scope, &m.upper).ok()?)?;
            let lo = match &m.lower {
                Some(l) => as_num(crate::eval::evaluate_expr_in(&mut self.b, scope, l).ok()?)?,
                None if hi.is_infinite() => 0.0,
                None => hi,
            };
            Some((lo, hi))
        })();
        self.b.identity_origin_unit = origin;
        result
    }

    /// `e`'s explicit FeatureTyping targets (`: T`), resolved — a subset
    /// of [`Self::explicit_supertypes`] restricted to typings.
    pub fn typings(&mut self, e: ElementRef) -> Vec<ElementRef> {
        self.b
            .explicit_specialization_elems(e.0)
            .into_iter()
            .filter_map(|(kind, target)| (kind == "FeatureTyping").then_some(ElementRef(target)))
            .collect()
    }

    /// Does `e` reach `ancestor` through the explicit specialization
    /// closure (typing, subclassification, subsetting, redefinition) or
    /// a semantic-metadata implied specialization? Implied library bases
    /// are not walked — a `false` against a library type is open-world
    /// (see the query-mode `istype` notes).
    pub fn conforms(&mut self, e: ElementRef, ancestor: ElementRef) -> bool {
        self.b.conforms_upward_semantic(e.0, ancestor.0)
    }

    /// How many references failed to resolve (serialized as `@ref`
    /// spellings), including ambiguous references. A transformation gate: an
    /// edit that was supposed to be semantics-preserving must not change this.
    pub fn unresolved_count(&self) -> usize {
        self.b.unresolved.len() + self.b.ambiguous.len()
    }

    /// Unresolved user references that name a member visible only under
    /// a wider visibility — see [`BlockedReference`]. Unlike the
    /// resolution report, reading this does not drain anything.
    pub fn blocked_references(&self) -> Vec<BlockedReference> {
        self.b
            .blocked
            .iter()
            .filter(|site| site.owner >= self.b.lib_boundary)
            .map(|site| BlockedReference {
                unit: self.b.unit_of_elem(site.owner),
                name: site.name.clone(),
                spelling: site.spelling.clone(),
                member: ElementRef(site.member),
                visibility: site.visibility,
                protected_suffices: site.protected_suffices,
            })
            .collect()
    }

    /// Every reference that failed to resolve, including ambiguous references:
    /// the element whose property
    /// carries it, the spelling as written, and the unit it was written
    /// in. Relocation edits (which must not create unresolved references)
    /// diff this list pre/post to name exactly what they broke.
    pub fn unresolved_references(&self) -> Vec<UnresolvedReference> {
        self.b
            .unresolved
            .iter()
            .chain(self.b.ambiguous.iter())
            .map(|(elem, qn)| UnresolvedReference {
                owner: ElementRef(*elem),
                spelling: qn.to_ref_string(),
                unit: self.b.unit_of_elem(*elem),
                span: qn.span,
            })
            .collect()
    }

    /// The visibility serialized on `e`'s owning membership (`private` /
    /// `protected` / `public`); `None` when the element has no owning
    /// relationship or the membership spells none (public by default).
    pub fn member_visibility(&self, e: ElementRef) -> Option<&str> {
        let rel = self.b.elements[e.0].owning_relationship?;
        self.b.elements[rel]
            .props
            .get("visibility")
            .and_then(|v| v.as_str())
    }

    /// The full source extent of the member declaration that created `e`
    /// (keyword through body or terminator): (unit index, span). `None`
    /// for synthesized elements, document roots, and aliases/imports
    /// (which own no element).
    pub fn member_extent(&self, e: ElementRef) -> Option<(usize, Span)> {
        let span = *self.b.member_spans.get(&e.0)?;
        Some((self.b.unit_of_elem(e.0), span))
    }

    /// Replace element ids: every element whose current id is a key of
    /// `map` takes the mapped id, and every reference to it follows. The
    /// entry point for **explicit ids** — a document loaded from another
    /// producer keeps the ids it came with instead of this toolkit's
    /// graph-derived ones (IDS.md). Returns the entries actually applied
    /// — `(derived id, given id, the element's metaclass)` — so a caller
    /// can retire entries whose element no longer exists. Indexes keyed
    /// by id are rebuilt lazily.
    pub fn override_ids(&mut self, map: &HashMap<Uuid, Uuid>) -> Vec<(Uuid, Uuid, &'static str)> {
        if map.is_empty() {
            return Vec::new();
        }
        let dynamic_was_current =
            self.b.dynamic_graph.as_ref().is_some_and(|s| {
                s.current(&self.b) && s.outcome == dynamic_graph::Outcome::Accepted
            });
        let local_was_current = self
            .b
            .dynamic_graph
            .as_ref()
            .is_some_and(|s| s.local_current(&self.b));
        let result_was_current = self
            .b
            .dynamic_graph
            .as_ref()
            .is_some_and(|snapshot| snapshot.result_redefinition_current(&self.b));
        let mut applied: Vec<(Uuid, Uuid, &'static str)> = Vec::new();
        let mut remap: HashMap<Uuid, Uuid> = HashMap::new();
        let n = self.b.elements.len();
        for i in 0..n {
            let old = self.b.elements[i].id;
            if let Some(&new) = map.get(&old) {
                if new != old {
                    self.b.elements[i].id = new;
                    remap.insert(old, new);
                    applied.push((old, new, self.b.elements[i].ty));
                }
            }
        }
        if applied.is_empty() {
            return applied;
        }
        self.b.recorded_lookup_prefix = None;
        for i in 0..n {
            for atom in self.b.elements[i].props.values_mut() {
                atom.remap(&remap);
            }
        }
        for (_, target) in self.b.id_spelled_targets.values_mut() {
            if let Some(&replacement) = remap.get(target) {
                *target = replacement;
            }
        }
        // Name tables are reference-bearing indexes too: a later implied
        // materialization must never recreate an edge to a retired identity.
        for names in [&mut self.b.lib_qnames, &mut self.b.lib_mem_qnames] {
            for i in 0..names.len() {
                if let Some(&id) = remap.get(&names[i].0) {
                    names[i].0 = id;
                }
            }
        }
        for names in [
            &mut self.external_by_name,
            &mut self.b.external_implied_names,
        ] {
            for id in names.values_mut() {
                if let Some(&replacement) = remap.get(id) {
                    *id = replacement;
                }
            }
        }
        // ID replacement can collapse external bindings. Keep conflicting
        // name provenance qualified even when the compatibility indexes merge.
        let mut external_names_by_id: HashMap<Uuid, String> = HashMap::new();
        for (name, &id) in &self.external_by_name {
            if let Some(previous) = external_names_by_id.insert(id, name.clone()) {
                if previous != *name {
                    self.external_ambiguous_names.insert(previous);
                    self.external_ambiguous_names.insert(name.clone());
                }
            }
        }
        for names in [&mut self.external_names, &mut self.external_package] {
            *names = std::mem::take(names)
                .into_iter()
                .map(|(id, name)| (remap.get(&id).copied().unwrap_or(id), name))
                .collect();
        }
        if self
            .b
            .implied
            .as_ref()
            .is_none_or(|t| t.from == self.b.elements.len())
        {
            self.b.implied = None;
            self.b.implied_from = None;
            self.b.semantic_ownership = None;
            self.b.positional_redefinitions = None;
            self.b.inherited_cache.clear();
            self.b.inherited_by_heritage.clear();
            self.import_truncated.clear();
        }
        self.by_id_built_for = usize::MAX;
        self.b.id_index = None;
        self.b.supported_implied = None;
        let metadata_changed = self.b.refresh_metadata_associations();
        if metadata_changed {
            self.quantity_index = None;
            self.name_memo.clear();
            self.redefiner_index = None;
            self.import_truncated.clear();
        }
        self.refresh_implied_specializations();
        self.b.remap_dynamic_graph(
            &remap,
            dynamic_was_current && !metadata_changed,
            local_was_current,
            result_was_current && !metadata_changed,
        );
        applied
    }

    /// Bind references spelled as a bare id — a `{"@ref": "<uuid>"}`
    /// placeholder left by a reference to an element that has no name
    /// (the textual notation cannot spell it, so the lift carried the
    /// id as a quoted name) — to that id: a reference to an element of
    /// this model, or a dangling reference to an id outside it (a library
    /// element when no library is loaded), which the emitters carry as
    /// spelled. Returns the ids bound. In-model references participate in
    /// typing, specialization, inherited lookup, evaluation and reference
    /// navigation. User references are resolved again after the identities
    /// become available, including references depending on the newly bound
    /// heritage or imports. Call after restoring explicit ids and before
    /// derived/implied queries. Payload loaders should use
    /// [`Self::bind_id_spelled_references_with`] to disambiguate lexical
    /// names that happen to spell an identity.
    ///
    /// Generated owned-result handles must be reacquired after this call;
    /// see [`Self::bind_id_spelled_references_with`] for the invalidation rule.
    pub fn bind_id_spelled_references(&mut self) -> HashSet<Uuid> {
        self.bind_id_spelled_references_with(&mut HashMap::new())
    }

    /// Bind identity spellings with the original payload's reference hints.
    ///
    /// This call invalidates handles for newly generated owned-result nodes;
    /// reacquire those nodes through their source expression afterward. Source
    /// and pre-existing generic implied relationship handles remain valid.
    /// Invalidated Rust handles are not generation-checked: do not reuse them.
    /// This also repairs spellings that accidentally resolved as a lexical
    /// UUID-looking name. The hints are pruned to actual identity spellings
    /// and should be retained across rebuilds of the lifted text. Call this
    /// after restoring explicit ids and before derived/implied queries.
    ///
    /// Unresolved UUID-shaped spellings without a preserved payload holder
    /// retain the compatibility interpretation as identity references. The
    /// lift cannot always distinguish an authored UUID-shaped `@ref` from
    /// an unnamed-target fallback when it regenerates relationship identity.
    pub fn bind_id_spelled_references_with(
        &mut self,
        hints: &mut crate::loader::IdReferenceBindings,
    ) -> HashSet<Uuid> {
        self.bind_id_spelled_references_impl(hints, false)
    }

    /// Bind only payload-proven reference sites. Unlike the compatibility
    /// binder, unrelated authored UUID-shaped names keep lexical meaning.
    /// The same generated-handle invalidation rules apply as for
    /// [`Self::bind_id_spelled_references_with`].
    pub fn bind_payload_id_references(
        &mut self,
        hints: &mut crate::loader::IdReferenceBindings,
    ) -> HashSet<Uuid> {
        self.bind_id_spelled_references_impl(hints, true)
    }

    /// Source positions of references currently bound by identity. Transform
    /// callers may map these through their exact text splices and then call
    /// [`Self::rekey_id_reference_bindings`] on a rebuilt model. This preserves
    /// site evidence when an enclosing declaration changes identity.
    pub fn bound_id_reference_sites(&self) -> Vec<(usize, Span, Uuid)> {
        self.b
            .id_spelled_targets
            .iter()
            .map(|(&(unit, start, end), &(_, id))| (unit, Span { start, end }, id))
            .collect()
    }

    /// Recover holder/property keys only at explicitly carried source sites
    /// whose rebuilt single-segment spelling still equals the given UUID.
    /// A changed reference spelling is deliberately not carried forward.
    pub fn rekey_id_reference_bindings(
        &self,
        sites: &[(usize, Span, Uuid)],
    ) -> crate::loader::IdReferenceBindings {
        let sites: HashMap<_, _> = sites
            .iter()
            .map(|(u, s, id)| ((*u, s.start, s.end), *id))
            .collect();
        self.b
            .id_binding_pending
            .iter()
            .filter_map(|p| {
                let [name] = p.qn.segments.as_slice() else {
                    return None;
                };
                if p.qn.is_global {
                    return None;
                }
                let id =
                    *sites.get(&(self.b.unit_of_elem(p.elem), name.span.start, name.span.end))?;
                (Uuid::parse_str(&name.value).ok() == Some(id))
                    .then(|| ((self.b.elem_id(p.elem), p.key.clone()), id))
            })
            .collect()
    }

    /// Current serialized endpoint values for retained payload spelling hints.
    /// Keep this separate from the spelling map: an imported member's spelling
    /// denotes a Membership-valued serialized endpoint after resolution.
    pub fn payload_id_reference_values(
        &mut self,
        hints: &crate::loader::IdReferenceBindings,
    ) -> crate::loader::IdReferenceBindings {
        hints
            .keys()
            .filter_map(|(owner, key)| {
                let element = self.b.element_index_of_uuid(*owner)?;
                let (base, index) = key
                    .split_once('#')
                    .map_or((key.as_str(), None), |(b, i)| (b, i.parse::<usize>().ok()));
                let mut value = self.b.elements[element].props.get(base)?;
                if let Some(index) = index {
                    let crate::properties::Atom::Array(items) = value else {
                        return None;
                    };
                    value = items.get(index)?;
                }
                let target = value
                    .get("@id")
                    .and_then(|v| v.as_str())
                    .and_then(|s| Uuid::parse_str(s).ok())?;
                Some(((*owner, key.clone()), target))
            })
            .collect()
    }

    fn bind_id_spelled_references_impl(
        &mut self,
        hints: &mut crate::loader::IdReferenceBindings,
        strict: bool,
    ) -> HashSet<Uuid> {
        if self.b.id_binding_pending.is_empty() && !self.b.id_spelled_targets.is_empty() {
            return HashSet::new();
        }
        self.discard_owned_result_tail();
        let mut bound: HashSet<Uuid> = HashSet::new();
        let n = self.b.elements.len();
        if !strict {
            for i in self.b.lib_boundary..n {
                let row = &mut self.b.elements[i];
                for (key, atom) in row.props.entries.make_mut() {
                    if !crate::model::is_payload_usage_flag(row.ty, key.name()) {
                        bind_atom(atom, &mut bound);
                    }
                }
            }
        }
        let mut hinted_sites = HashSet::new();
        let pending_ids: HashMap<_, _> = self
            .b
            .id_binding_pending
            .iter()
            .filter_map(|p| {
                let [name] = p.qn.segments.as_slice() else {
                    return None;
                };
                let id = Uuid::parse_str(&name.value).ok()?;
                Some(((self.b.elements[p.elem].id, p.key.clone()), (p, id)))
            })
            .collect();
        hints.retain(|key, target| {
            let matching = pending_ids
                .get(key)
                .filter(|(_, id)| id == target)
                .map(|(p, _)| *p);
            if let Some(p) = matching {
                hinted_sites.insert((p.elem, p.qn.span.start, p.qn.span.end));
                bound.insert(*target);
                true
            } else {
                false
            }
        });
        let strict_slots: Vec<_> = if strict {
            self.b
                .id_binding_pending
                .iter()
                .filter_map(|p| {
                    let id = hints.get(&(self.b.elem_id(p.elem), p.key.clone()))?;
                    Some((p.elem, p.key.clone(), *id))
                })
                .collect()
        } else {
            Vec::new()
        };
        if !bound.is_empty() {
            if self
                .b
                .implied
                .as_ref()
                .is_some_and(|t| t.from == self.b.elements.len())
            {
                self.b.implied = None;
                self.b.implied_from = None;
                self.b.semantic_ownership = None;
            }
            let unresolved: HashSet<_> = self
                .b
                .unresolved
                .iter()
                .map(|(owner, qn)| (*owner, qn.span.start, qn.span.end))
                .collect();
            let mut bound_sites = HashSet::new();
            for pending in &self.b.id_binding_pending {
                let site = (pending.elem, pending.qn.span.start, pending.qn.span.end);
                if hinted_sites.contains(&site) || (!strict && unresolved.contains(&site)) {
                    if let [name] = pending.qn.segments.as_slice() {
                        if let Ok(id) = Uuid::parse_str(&name.value) {
                            if bound.contains(&id) {
                                bound_sites.insert(site);
                                self.b.id_spelled_targets.insert(
                                    (
                                        self.b.unit_of_elem(pending.elem),
                                        name.span.start,
                                        name.span.end,
                                    ),
                                    (id, id),
                                );
                            }
                        }
                    }
                }
            }
            self.b.recorded_lookup_prefix = None;
            self.b.reset_lookup_caches();
            self.b.semantic_memo = Default::default();
            self.quantity_index = None;
            self.name_memo.clear();
            self.redefiner_index = None;
            self.import_truncated.clear();
            let pending = std::mem::take(&mut self.b.id_binding_pending);
            if !pending.is_empty() {
                // Array-valued references append during resolution; replay
                // replaces their values instead of duplicating them.
                for p in &pending {
                    if let Some((base, _)) = p.key.split_once('#') {
                        self.b.elements[p.elem].props.insert(base, json!([]));
                    }
                    if let Some(si) = p.spec_idx {
                        self.b.spec_resolved[si] = None;
                    }
                }
                self.b.unresolved.retain(|(e, _)| *e < self.b.lib_boundary);
                self.b.ambiguous.retain(|(e, _)| *e < self.b.lib_boundary);
                self.b.blocked.clear();
                self.b.ref_sites.clear();
                self.b.used_imports.clear();
                self.b.pending = pending;
                self.b.semantic_ready = false;
                self.b.resolve_pending();
                self.b.semantic_ready = true;
                self.b.positional_redefinitions = None;
                self.b.supported_implied = None;
                self.b.inherited_cache.clear();
                self.b.inherited_by_heritage.clear();
                // External targets stay references by identity even though
                // no in-model element can supply a semantic outcome.
                if strict {
                    // External targets stay identity references only at the
                    // exact retained payload-proven slots. Resolved imports
                    // retain their Membership-valued resolution outcome.
                    for (elem, key, target) in &strict_slots {
                        let (base, index) = key
                            .split_once('#')
                            .map_or((key.as_str(), None), |(base, i)| {
                                (base, i.parse::<usize>().ok())
                            });
                        let entries = self.b.elements[*elem].props.entries.make_mut();
                        let Some((_, atom)) = entries.iter_mut().find(|(k, _)| k.name() == base)
                        else {
                            continue;
                        };
                        let atom = if let Some(index) = index {
                            let crate::properties::Atom::Array(items) = atom else {
                                continue;
                            };
                            let Some(atom) = items.get_mut(index) else {
                                continue;
                            };
                            atom
                        } else {
                            atom
                        };
                        if atom
                            .get("@ref")
                            .and_then(|v| v.as_str())
                            .and_then(|s| Uuid::parse_str(s.trim_matches('\'')).ok())
                            == Some(*target)
                        {
                            bind_atom(atom, &mut bound);
                        }
                    }
                } else {
                    for i in self.b.lib_boundary..n {
                        let row = &mut self.b.elements[i];
                        for (key, atom) in row.props.entries.make_mut() {
                            if !crate::model::is_payload_usage_flag(row.ty, key.name()) {
                                bind_atom(atom, &mut bound);
                            }
                        }
                    }
                }
            }
            self.b
                .unresolved
                .retain(|(owner, qn)| !bound_sites.contains(&(*owner, qn.span.start, qn.span.end)));
            self.b.refresh_metadata_associations();
            // Refresh known adjacency only; binding still precedes semantic queries.
            self.refresh_implied_specializations();
        }
        bound
    }

    /// Every element of the model, library elements first, in creation
    /// order. The implied relationships the derivation layer materializes
    /// are reached through [`Self::implied_relationships`] and the
    /// relationship families of [`Self::derived`], not listed here.
    pub fn elements(&self) -> impl Iterator<Item = ElementRef> + '_ {
        (0..self.b.explicit_len()).map(ElementRef)
    }

    /// Every element built from the user units (libraries excluded), in
    /// creation (document) order; implied relationships excluded as in
    /// [`Self::elements`].
    pub fn user_elements(&self) -> impl Iterator<Item = ElementRef> + '_ {
        (self.b.lib_boundary..self.b.explicit_len()).map(ElementRef)
    }

    /// The element's owned (non-derived) properties as the compact form
    /// spells them: `declaredName`, `isAbstract`, a relationship's ends
    /// (`subclassifier`, `superclassifier`, …) as `{"@id"}` references,
    /// an unresolved reference as its `{"@ref"}` spelling. Structure
    /// (`ownedRelationship`, `owningRelationship`, `ownedRelatedElement`)
    /// is not among them — read it with the navigation accessors.
    pub fn element_properties(&self, e: ElementRef) -> Map<String, Value> {
        self.b.elements[e.0].props.to_json()
    }

    /// The element's interchange `@id` (deterministic UUIDv5 — ownership
    /// path, or the normative KerML 9.1 id for library elements).
    pub fn element_id(&self, e: ElementRef) -> uuid::Uuid {
        self.b.elem_id(e.0)
    }

    /// Every constraint/requirement/invariant element carrying its own
    /// trailing result expression, in (unit, source-position) order.
    pub fn constraints(&mut self) -> Vec<ConstraintInfo> {
        self.constraints_where(|_| true)
    }

    /// [`Self::constraints`] whose [`ConstraintInfo::unit`] `keep` admits, in
    /// the same order, without building the others: a caller that reads only
    /// the user units' constraints leaves the library's alone.
    pub fn constraints_where(&mut self, keep: impl Fn(usize) -> bool) -> Vec<ConstraintInfo> {
        let mut out = Vec::new();
        for (owner, scope, expr) in &self.b.result_exprs {
            let ty = self.b.elements[*owner].ty;
            if !matches!(
                ty,
                "ConstraintUsage"
                    | "AssertConstraintUsage"
                    | "ConstraintDefinition"
                    | "RequirementUsage"
                    | "SatisfyRequirementUsage"
                    | "RequirementDefinition"
                    | "Invariant"
            ) {
                continue;
            }
            let unit = self.b.unit_of_elem(*owner);
            if !keep(unit) {
                continue;
            }
            let negated = self.b.elements[*owner]
                .props
                .get("isNegated")
                .and_then(|v| v.as_bool())
                .unwrap_or(false);
            let asserted = matches!(
                ty,
                "AssertConstraintUsage" | "SatisfyRequirementUsage" | "Invariant"
            );
            let name = self.b.elements[*owner]
                .props
                .get("declaredName")
                .and_then(|v| v.as_str())
                .map(str::to_string);
            out.push(ConstraintInfo {
                element: ElementRef(*owner),
                unit,
                span: expr.span,
                name,
                element_type: ty,
                asserted,
                negated,
                scope: ScopeRef(*scope),
                expr: expr.clone(),
            });
        }
        // Inherited bodies: an *asserted* constraint without its own result
        // expression (`assert c : Def;`, `assert not c :> other;`) takes
        // the nearest expression from its explicit typing/specialization
        // closure, evaluated in its own body scope — the featuring context
        // where the definition's parameters resolve to the assert's
        // redefining features.
        // Each owner's last result expression, by position: an expression is
        // copied only once an assert takes it.
        let bodies: HashMap<usize, usize> = self
            .b
            .result_exprs
            .iter()
            .enumerate()
            .map(|(i, (o, _, _))| (*o, i))
            .collect();
        let asserts: Vec<usize> = (self.b.lib_boundary..self.b.elements.len())
            .filter(|&e| {
                matches!(
                    self.b.elements[e].ty,
                    "AssertConstraintUsage" | "SatisfyRequirementUsage" | "Invariant"
                ) && !bodies.contains_key(&e)
            })
            .collect();
        for a in asserts {
            let Some(&scope) = self.b.elem_scope.get(&a) else {
                continue;
            };
            // Breadth-first over the explicit closure: the nearest body wins.
            let mut queue: std::collections::VecDeque<usize> =
                self.b.explicit_supertype_elems(a).into();
            let mut seen: std::collections::HashSet<usize> = queue.iter().copied().collect();
            let mut found: Option<(usize, usize)> = None;
            let mut steps = 0;
            while let Some(t) = queue.pop_front() {
                steps += 1;
                if steps > 256 {
                    break;
                }
                if let Some(&i) = bodies.get(&t) {
                    found = Some((t, i));
                    break;
                }
                for s in self.b.explicit_supertype_elems(t) {
                    if seen.insert(s) {
                        queue.push_back(s);
                    }
                }
            }
            let Some((def, i)) = found else { continue };
            let unit = self.b.unit_of_elem(def);
            if !keep(unit) {
                continue;
            }
            let expr = self.b.result_exprs[i].2.clone();
            let negated = self.b.elements[a]
                .props
                .get("isNegated")
                .and_then(|v| v.as_bool())
                .unwrap_or(false);
            let name = self.b.elements[a]
                .props
                .get("declaredName")
                .and_then(|v| v.as_str())
                .map(str::to_string);
            out.push(ConstraintInfo {
                element: ElementRef(a),
                // Attribution follows the body's text (the definition's
                // unit and span); the verdict's featuring context is the
                // assert's.
                unit,
                span: expr.span,
                name,
                element_type: self.b.elements[a].ty,
                asserted: true,
                negated,
                scope: ScopeRef(scope),
                expr,
            });
        }
        out.sort_by_key(|c| (c.unit, c.span.start));
        out
    }

    /// Satisfaction claims (`satisfy R by x;`) expanded to evaluable
    /// constraints: for each claim, the satisfied requirement's subjects
    /// (across its explicit closure) bind to the resolved `by` target,
    /// and every constraint reachable through the requirement's
    /// composition — own `require`/`assume` members, their inherited
    /// bodies, and nested requirement members incl. reference-subsetted
    /// requirements — is collected for verdict evaluation. Each
    /// constraint evaluates in the body scope of the requirement usage
    /// the walk entered it through, so nested parameter bindings
    /// (`in p = subj;`) and redefinitions apply; the subject override is
    /// the only seeded value — everything else flows through ordinary
    /// feature-value evaluation (unbound stays honestly undecided).
    pub fn satisfactions(&mut self) -> Vec<SatisfactionInfo> {
        self.ensure_by_id();
        // Only user claims are evaluated; the library rows stay untouched
        // behind their shared prefix.
        let claims: Vec<_> = self
            .b
            .satisfy_by
            .iter()
            .filter(|(sat, _, _)| *sat >= self.b.lib_boundary)
            .cloned()
            .collect();
        let mut out = Vec::new();
        for (sat, scope, by) in claims {
            // `satisfy R by x;` references the requirement it satisfies. A
            // claim that declares its own requirement instead
            // (`satisfy requirement : R by x;`) has no reference and is
            // itself the satisfied requirement (SysML `assertedConstraint`).
            // A reference that did not resolve leaves nothing to evaluate.
            let references = self.b.elements[sat]
                .owned_relationships
                .iter()
                .any(|&r| self.b.elements[r].ty == "ReferenceSubsetting");
            let req = if references {
                match self.rel_prop_target(sat, "ReferenceSubsetting", "referencedFeature") {
                    Some(req) => req,
                    None => continue,
                }
            } else {
                sat
            };
            let bound = match &by {
                TargetRef::Name(qn) => self.b.resolve(scope, qn, 0),
                TargetRef::Chain(links) if !links.is_empty() => {
                    let empty = QualifiedName {
                        is_global: false,
                        segments: Vec::new(),
                        span: Span::default(),
                    };
                    self.b.resolve_chain_member(scope, Some(links), &empty)
                }
                TargetRef::Chain(_) => None,
            };
            let Some(bound) = bound else { continue };
            let mut overrides = std::collections::HashMap::new();
            for t in self.explicit_closure(req) {
                for subj in self.members_under(t, "SubjectMembership") {
                    overrides.insert(subj, crate::eval::Value::Element(ElementRef(bound)));
                }
            }
            let mut constraints = Vec::new();
            let mut nodes = vec![SatisfactionNode::default()];
            let mut seen: std::collections::HashSet<(usize, usize)> =
                std::collections::HashSet::new();
            let entry_scope = self.b.elem_scope.get(&req).copied().unwrap_or(scope);
            self.collect_satisfaction_constraints(
                req,
                entry_scope,
                &mut seen,
                (&mut constraints, &mut nodes, 0),
                0,
            );
            // Source order, with the nodes' indices following the moves.
            let mut order: Vec<usize> = (0..constraints.len()).collect();
            order.sort_by_key(|&i| (constraints[i].unit, constraints[i].span.start));
            let mut moved = vec![0; order.len()];
            for (to, &from) in order.iter().enumerate() {
                moved[from] = to;
            }
            let mut slots: Vec<Option<ConstraintInfo>> =
                constraints.into_iter().map(Some).collect();
            let constraints: Vec<ConstraintInfo> =
                order.iter().filter_map(|&i| slots[i].take()).collect();
            for node in &mut nodes {
                for (i, _) in &mut node.constraints {
                    *i = moved[*i];
                }
            }
            // An unnamed declared claim is labelled by its requirement type.
            let context = self.element_qualified_name(ElementRef(req)).or_else(|| {
                self.rel_prop_target(req, "FeatureTyping", "type")
                    .and_then(|t| self.element_qualified_name(ElementRef(t)))
            });
            let by_span = match &by {
                TargetRef::Name(qn) => qn.span,
                TargetRef::Chain(links) => match (links.first(), links.last()) {
                    (Some(first), Some(last)) => Span {
                        start: first.span.start,
                        end: last.span.end,
                    },
                    _ => Span::default(),
                },
            };
            let by_spelling = match &by {
                TargetRef::Name(qn) => qn.to_display_string(),
                TargetRef::Chain(links) => links
                    .iter()
                    .map(|l| l.to_display_string())
                    .collect::<Vec<_>>()
                    .join("."),
            };
            let negated = self.b.elements[sat]
                .props
                .get("isNegated")
                .and_then(|v| v.as_bool())
                .unwrap_or(false);
            out.push(SatisfactionInfo {
                satisfy: ElementRef(sat),
                unit: self.b.unit_of_elem(sat),
                span: self.b.member_spans.get(&sat).copied().unwrap_or(by_span),
                by: by_spelling,
                negated,
                context,
                constraints,
                nodes,
                overrides,
            });
        }
        out
    }

    /// The element and its transitive explicit supertypes (typing,
    /// subclassification, subsetting, redefinition), user-owned only.
    fn explicit_closure(&mut self, start: usize) -> Vec<usize> {
        let mut seen = std::collections::HashSet::new();
        let mut stack = vec![start];
        let mut out = Vec::new();
        while let Some(t) = stack.pop() {
            if !seen.insert(t) || t < self.b.lib_boundary {
                continue;
            }
            out.push(t);
            stack.extend(self.b.explicit_supertype_elems(t));
        }
        out
    }

    /// Elements owned by `e` through memberships of the given metaclass,
    /// in element order. Reads the memberships' owned elements instead of
    /// every row; an element counts only when its own owning relationship
    /// is one of those memberships.
    fn members_under(&self, e: usize, rel_ty: &str) -> Vec<usize> {
        let rels: Vec<usize> = self.b.elements[e]
            .owned_relationships
            .iter()
            .copied()
            .filter(|&r| self.b.elements[r].ty == rel_ty)
            .collect();
        let mut members: Vec<usize> = rels
            .iter()
            .flat_map(|&r| self.b.elements[r].children.iter().copied())
            .filter(|&m| {
                self.b.elements[m]
                    .owning_relationship
                    .is_some_and(|r| rels.contains(&r))
            })
            .collect();
        members.sort_unstable();
        members.dedup();
        members
    }

    /// How requirement member `m` bears on its owner's check: `assume`
    /// members are assumptions; `require` members, assertions and nested
    /// requirements are required. A plain constraint member is not part of
    /// the check and answers `None`.
    fn satisfaction_role(&self, m: usize) -> Option<SatisfactionRole> {
        if let Some(rel) = self.b.elements[m].owning_relationship {
            let rel = &self.b.elements[rel];
            if crate::metaclass::conforms(rel.ty, "RequirementConstraintMembership") {
                return Some(match rel.props.get("kind").and_then(|v| v.as_str()) {
                    Some("assumption") => SatisfactionRole::Assumed,
                    _ => SatisfactionRole::Required,
                });
            }
        }
        matches!(
            self.b.elements[m].ty,
            "AssertConstraintUsage" | "RequirementUsage" | "SatisfyRequirementUsage"
        )
        .then_some(SatisfactionRole::Required)
    }

    /// Walk one requirement node for [`Self::satisfactions`]: constraints
    /// on the node and its explicit closure evaluate in `eval_scope` (the
    /// most-derived usage body on the path) and join the check `at`;
    /// nested requirement members and reference-subsetted requirements
    /// become checks of their own, walked with their own body scope.
    fn collect_satisfaction_constraints(
        &mut self,
        node: usize,
        eval_scope: usize,
        seen: &mut std::collections::HashSet<(usize, usize)>,
        (out, nodes, at): (&mut Vec<ConstraintInfo>, &mut Vec<SatisfactionNode>, usize),
        depth: usize,
    ) {
        // Keyed on (element, evaluation scope): the same definition-owned
        // constraint legitimately re-evaluates under each usage branch
        // that reaches it — only a true revisit (same context) prunes.
        if depth > 8 || !seen.insert((node, eval_scope)) {
            return;
        }
        for t in self.explicit_closure(node) {
            for m in self.owned_membership_members(t) {
                let ty = self.b.elements[m].ty;
                let Some(role) = self.satisfaction_role(m) else {
                    continue;
                };
                match ty {
                    "ConstraintUsage" | "AssertConstraintUsage" => {
                        // A constraint member owned by the entered node
                        // evaluates in its own body scope (its body's
                        // bindings and redefinitions apply, the node's
                        // body is one lexical step out); one found on a
                        // *closure* type keeps the entered usage's scope
                        // — the assert inherited-body rule, so the
                        // usage's redefinitions shadow the general
                        // parameters.
                        let m_scope = if t == node {
                            self.b.elem_scope.get(&m).copied().unwrap_or(eval_scope)
                        } else {
                            eval_scope
                        };
                        if !seen.insert((m, m_scope)) {
                            continue;
                        }
                        if let Some((def, expr)) = self.nearest_constraint_body(m) {
                            if def < self.b.lib_boundary {
                                continue;
                            }
                            let negated = self.b.elements[m]
                                .props
                                .get("isNegated")
                                .and_then(|v| v.as_bool())
                                .unwrap_or(false);
                            let name = self.b.elements[m]
                                .props
                                .get("declaredName")
                                .and_then(|v| v.as_str())
                                .map(str::to_string);
                            nodes[at].constraints.push((out.len(), role));
                            out.push(ConstraintInfo {
                                element: ElementRef(m),
                                unit: self.b.unit_of_elem(def),
                                span: expr.span,
                                name,
                                element_type: ty,
                                asserted: true,
                                negated,
                                scope: ScopeRef(m_scope),
                                expr,
                            });
                        } else if let Some(target) =
                            self.rel_prop_target(m, "ReferenceSubsetting", "referencedFeature")
                        {
                            // `require someRequirement { in p = expr; }` —
                            // a bodiless constraint member referencing a
                            // requirement: recurse into the target with
                            // the member's body as the evaluation context
                            // (its `in` bindings feed the target's
                            // parameters).
                            let child = nodes.len();
                            nodes.push(SatisfactionNode::default());
                            nodes[at].children.push((child, role));
                            self.collect_satisfaction_constraints(
                                target,
                                m_scope,
                                seen,
                                (&mut *out, &mut *nodes, child),
                                depth + 1,
                            );
                        }
                    }
                    "RequirementUsage" | "SatisfyRequirementUsage" => {
                        let m_scope = self.b.elem_scope.get(&m).copied().unwrap_or(eval_scope);
                        let child = nodes.len();
                        nodes.push(SatisfactionNode::default());
                        nodes[at].children.push((child, role));
                        // The nested member's own body (bindings,
                        // redefinitions) is the freshest context for
                        // everything reached through it.
                        self.collect_satisfaction_constraints(
                            m,
                            m_scope,
                            seen,
                            (&mut *out, &mut *nodes, child),
                            depth + 1,
                        );
                        if let Some(target) =
                            self.rel_prop_target(m, "ReferenceSubsetting", "referencedFeature")
                        {
                            self.collect_satisfaction_constraints(
                                target,
                                m_scope,
                                seen,
                                (&mut *out, &mut *nodes, child),
                                depth + 1,
                            );
                        }
                    }
                    _ => {}
                }
            }
        }
    }

    /// Elements owned by `e` through any `*Membership` relationship.
    fn owned_membership_members(&self, e: usize) -> Vec<usize> {
        self.b.owned_member_elems(e, false)
    }

    /// The constraint body of `m`: its own result expression, or the
    /// nearest one in its explicit closure (the assert inherited-body
    /// rule). Returns the body-owning element and the expression.
    fn nearest_constraint_body(&mut self, m: usize) -> Option<(usize, Expr)> {
        let own = self
            .b
            .result_exprs
            .iter()
            .find(|(o, _, _)| *o == m)
            .map(|(o, _, e)| (*o, e.clone()));
        if own.is_some() {
            return own;
        }
        let mut queue: std::collections::VecDeque<usize> =
            self.b.explicit_supertype_elems(m).into();
        let mut seen: std::collections::HashSet<usize> = queue.iter().copied().collect();
        let mut steps = 0;
        while let Some(t) = queue.pop_front() {
            steps += 1;
            if steps > 256 {
                break;
            }
            if let Some((_, _, expr)) = self.b.result_exprs.iter().find(|(o, _, _)| *o == t) {
                return Some((t, expr.clone()));
            }
            for n in self.b.explicit_supertype_elems(t) {
                if seen.insert(n) {
                    queue.push_back(n);
                }
            }
        }
        None
    }

    /// [`Self::evaluate_in`] with feature-value overrides (see
    /// [`Self::satisfactions`] — subjects bound to a satisfaction
    /// target).
    pub fn evaluate_in_with(
        &mut self,
        scope: ScopeRef,
        expr: &Expr,
        overrides: &std::collections::HashMap<usize, crate::eval::Value>,
    ) -> Result<crate::eval::Value, crate::eval::EvalError> {
        crate::eval::evaluate_expr_with(&mut self.b, scope.0, expr, overrides.clone())
    }

    /// One entry of [`Self::body_flow_members`]: an owned member in
    /// declaration order, or a `first X;` initial-node marker.
    #[allow(missing_docs)]
    pub fn body_flow_members(&mut self, e: ElementRef) -> Vec<BodyFlowMember> {
        self.ensure_by_id();
        let rels: Vec<usize> = self.b.elements[e.0].owned_relationships.to_vec();
        // Owned elements per relationship, one scan.
        let mut owned: std::collections::HashMap<usize, Vec<usize>> =
            std::collections::HashMap::new();
        for (i, el) in self.b.elements.iter().enumerate() {
            if let Some(r) = el.owning_relationship {
                owned.entry(r).or_default().push(i);
            }
        }
        let mut out = Vec::new();
        for r in rels {
            let rel = &self.b.elements[r];
            if !rel.ty.ends_with("Membership") {
                continue;
            }
            if let Some(kids) = owned.get(&r) {
                out.extend(kids.iter().map(|&k| BodyFlowMember::Member(ElementRef(k))));
                continue;
            }
            // A non-owning Membership: an alias, a transition source, or
            // an initial-node marker (`first X;` — the lowering names its
            // path `…first`). Only the marker matters for flow order.
            if rel.path.ends_with("first") {
                let target = self.prop_target(r, "memberElement").map(ElementRef);
                let spelling = self.b.elements[r]
                    .props
                    .get("memberElement")
                    .and_then(|v| v.get("@ref"))
                    .and_then(|v| v.as_str())
                    .map(str::to_string);
                out.push(BodyFlowMember::Initial(target, spelling));
            }
        }
        out
    }

    /// The declared name of the rendering a view requests
    /// (`render asInterconnectionDiagram;` → `asInterconnectionDiagram`):
    /// the referenced rendering of the first ViewRenderingMembership among
    /// the view's feature memberships, inherited ones included, as the
    /// specification derives `viewRendering`. The view's own `render`
    /// member comes first. A view without one takes the rendering it
    /// inherits through its typings and specializations (`view v : T;`
    /// over `view def T { render asElementTable; }` → `asElementTable`);
    /// of several, the first in heritage order wins — the first-declared
    /// typing or specialization, and a supertype's own `render` ahead of
    /// the ones it inherits in turn. A `render` member that references a
    /// rendering names it (through a feature chain, its last feature); one
    /// that declares a rendering in place (`render rendering outline;`) is
    /// that rendering. `None` when the view has no rendering, or when the
    /// one selected does not resolve to a rendering usage.
    pub fn view_rendering(&mut self, view: ElementRef) -> Option<String> {
        self.ensure_by_id();
        let membership = self.view_rendering_membership(view)?;
        let rendering = match self.d_referenced_member(membership, "RenderingUsage")? {
            Reference::Element(rendering) => rendering,
            Reference::Unresolved(_) => self.spelled_rendering(membership)?,
            Reference::External(_) => return None,
        };
        self.b.elements[rendering.0]
            .props
            .get("declaredName")
            .and_then(|v| v.as_str())
            .map(str::to_string)
    }

    /// The ViewRenderingMembership [`Self::view_rendering`] reads: the
    /// view's own, else the first it inherits. The inheritance walk keeps
    /// a supertype's rendering beside the rendering of a more specific
    /// type that replaces it, so the order decides: the walk lists each
    /// type's own memberships ahead of those it inherits.
    fn view_rendering_membership(&mut self, view: ElementRef) -> Option<ElementRef> {
        let own = self
            .owned_relationships_of_kind(view, "ViewRenderingMembership")
            .into_iter()
            .next();
        if own.is_some() {
            return own;
        }
        self.inherited_memberships(view, true)
            .into_iter()
            .find(|&m| self.is_kind(m, "ViewRenderingMembership"))
    }

    /// The rendering a `render` member names by a reference that did not
    /// resolve when the model was built, which holds its spelling as
    /// written: resolved from the namespace the member was declared in —
    /// the view's own body, or the body of the definition or view it
    /// inherits the member from. A chained reference is not re-resolved.
    fn spelled_rendering(&mut self, membership: ElementRef) -> Option<ElementRef> {
        let member = self.membership_member(membership)?;
        let subsetting = self
            .owned_relationships_of_kind(member, "ReferenceSubsetting")
            .into_iter()
            .next()?;
        let spelling = self.b.elements[subsetting.0]
            .props
            .get("referencedFeature")?
            .get("@ref")?
            .as_str()?
            .to_string();
        let owner = self.owner(membership)?;
        let scope = ScopeRef(*self.b.elem_scope.get(&owner.0)?);
        let qn = QualifiedName {
            is_global: false,
            segments: split_qualified(&spelling)
                .into_iter()
                .map(|value| Name {
                    value,
                    span: sysmlv2_syntax::span::Span::default(),
                })
                .collect(),
            span: sysmlv2_syntax::span::Span::default(),
        };
        let rendering = self.resolve_in_excluding(scope, &qn, Some(member))?;
        self.is_kind(rendering, "RenderingUsage")
            .then_some(rendering)
    }

    /// Resolve a qualified name with references resolving from `scope` —
    /// exactly how the expression evaluator resolves a [`ExprKind::Ref`].
    pub fn resolve_in(&mut self, scope: ScopeRef, qn: &QualifiedName) -> Option<ElementRef> {
        self.b.resolve(scope.0, qn, 0).map(ElementRef)
    }

    /// Whether a simple name is already visible from `scope`, including an
    /// ambiguous set of candidates. This is the prospective-declaration
    /// collision probe: owned/effective members, aliases, membership and
    /// namespace imports, inherited members, and enclosing scopes all count.
    /// Import-usage bookkeeping is restored after the probe, so a refused
    /// edit cannot make an otherwise-unused import appear used.
    pub fn name_is_bound_in(&mut self, scope: ScopeRef, name: &str) -> bool {
        let qn = QualifiedName {
            is_global: false,
            segments: vec![Name {
                value: name.to_string(),
                span: sysmlv2_syntax::Span::default(),
            }],
            span: sysmlv2_syntax::Span::default(),
        };
        let used_imports = self.b.used_imports.clone();
        let result = self.b.resolve_result(scope.0, &qn, 0, false);
        self.b.used_imports = used_imports;
        result != LookupResult::Missing
    }

    /// [`Self::resolve_in`] with `exclude` shielded from capture — the
    /// resolution mode a feature's own specialization targets and value
    /// expression run under (see [`RefSite::exclude`]). A verification
    /// probe: an import it walks is not recorded as used.
    pub fn resolve_in_excluding(
        &mut self,
        scope: ScopeRef,
        qn: &QualifiedName,
        exclude: Option<ElementRef>,
    ) -> Option<ElementRef> {
        let saved = self.b.exclude;
        let used_imports = self.b.used_imports.clone();
        self.b.exclude = exclude.map(|e| e.0);
        let out = self.b.resolve(scope.0, qn, 0);
        self.b.exclude = saved;
        self.b.used_imports = used_imports;
        out.map(ElementRef)
    }

    /// Resolve `member` within `target`'s own scope — exactly how the
    /// evaluator resolves a feature-chain step (`target.member`). Returns
    /// the hit together with the target's body scope (the *featuring
    /// context* the member's value expression re-resolves from).
    pub fn member_of(
        &mut self,
        target: ElementRef,
        member: &QualifiedName,
    ) -> Option<(ElementRef, Option<ScopeRef>)> {
        let sub = self.b.elem_scope.get(&target.0).copied();
        let hit = self.b.resolve_rest(target.0, sub, &member.segments, 0)?;
        Some((ElementRef(hit), sub.map(ScopeRef)))
    }

    /// Whether `e` is a directed parameter or a member of the
    /// ParameterMembership family (including subjects and actors).
    pub fn is_parameter(&self, e: ElementRef) -> bool {
        self.b.is_parameter(e.0)
    }

    /// Whether a featured, unvalued feature stands for a referenced instance.
    /// Package-owned usages are excluded even when noncomposite.
    pub fn is_reference_feature(&self, e: ElementRef) -> bool {
        self.b.is_reference_feature(e.0)
    }

    /// Whether `e` declares its own non-default value expression. The
    /// expression is fixed; its result may still depend on unknown inputs.
    pub fn has_own_fixed_value(&self, e: ElementRef) -> bool {
        self.b.has_own_fixed_value(e.0)
    }

    /// `e`'s explicit Redefinition targets (`:>> x`), resolved — the
    /// one-hop borrow the semantic checks use for characteristics an
    /// untyped/undeclared redefining feature inherits from its target.
    pub fn redefinition_targets(&mut self, e: ElementRef) -> Vec<ElementRef> {
        self.b
            .redefinition_target_elems(e.0)
            .into_iter()
            .map(ElementRef)
            .collect()
    }

    /// The user features whose explicit Redefinition targets include
    /// `e` (the reverse of [`Self::redefinition_targets`], one hop), in
    /// document order — the features that borrow `e`'s declared types
    /// when they declare none of their own. Library features are not
    /// indexed. Built lazily once per resolved model.
    pub fn redefiners(&mut self, e: ElementRef) -> Vec<ElementRef> {
        self.sync_semantic_publication();
        if self.redefiner_index.is_none() {
            let mut index: HashMap<usize, Vec<usize>> = HashMap::new();
            let users: Vec<usize> = (self.b.lib_boundary..self.b.elements.len()).collect();
            for r in users {
                for t in self.b.redefinition_target_elems(r) {
                    index.entry(t).or_default().push(r);
                }
            }
            self.redefiner_index = Some(index);
        }
        self.redefiner_index
            .as_ref()
            .and_then(|ix| ix.get(&e.0))
            .map(|v| v.iter().map(|&r| ElementRef(r)).collect())
            .unwrap_or_default()
    }

    /// The element's bound feature-value expression, with the scope the
    /// expression's references resolve from (its writing scope — chain-step
    /// consumers substitute their featuring context).
    pub fn value_expr(&self, e: ElementRef) -> Option<(ScopeRef, Expr)> {
        self.b
            .values
            .get(&e.0)
            .map(|(s, expr)| (ScopeRef(*s), expr.clone()))
    }

    /// A calculation's evaluable body: its trailing result expression,
    /// or — the `return x = expr;` spelling — its return parameter's
    /// bound value (the evaluator's exact lookup, for solver inlining).
    pub fn calc_body(&self, e: ElementRef) -> Option<(ScopeRef, Expr)> {
        if self.b.calculation_requires_execution(e.0) {
            return None;
        }
        if let Some((_, s, expr)) = self.b.result_exprs.iter().find(|(o, _, _)| *o == e.0) {
            return Some((ScopeRef(*s), expr.clone()));
        }
        let ret = self.b.return_params.get(&e.0)?;
        self.b
            .values
            .get(ret)
            .map(|(s, expr)| (ScopeRef(*s), expr.clone()))
    }

    /// The declared `return` parameter, when the calculation has one.
    pub fn calc_return_param(&self, e: ElementRef) -> Option<ElementRef> {
        self.b.return_params.get(&e.0).copied().map(ElementRef)
    }

    /// Resolve a simple member name in an element's own scope (the
    /// binding targets for calculation parameters).
    pub fn owned_member(&mut self, owner: ElementRef, name: &str) -> Option<ElementRef> {
        let scope = self.b.elem_scope.get(&owner.0).copied();
        let seg = [Name {
            value: name.to_string(),
            span: sysmlv2_syntax::Span::default(),
        }];
        self.b.resolve_rest(owner.0, scope, &seg, 0).map(ElementRef)
    }

    /// The resolved targets of the element's *explicit* typings and
    /// specializations (`FeatureTyping`, `Subclassification`, `Subsetting`,
    /// `Redefinition`) — the upward edges a declared-type walk follows.
    /// Implied library bases are not included.
    pub fn explicit_supertypes(&mut self, e: ElementRef) -> Vec<ElementRef> {
        self.b
            .explicit_supertype_elems(e.0)
            .into_iter()
            .map(ElementRef)
            .collect()
    }

    /// The element's explicit typing/specialization edges with their
    /// relationship metaclass (`FeatureTyping`, `Subclassification`,
    /// `Subsetting`, `Redefinition`) — the graphical notation renders
    /// each with a distinct arrow.
    pub fn explicit_specializations(&mut self, e: ElementRef) -> Vec<(&'static str, ElementRef)> {
        self.b
            .explicit_specialization_elems(e.0)
            .into_iter()
            .map(|(kind, t)| (kind, ElementRef(t)))
            .collect()
    }

    /// The element's declared prefix keywords in header order — the
    /// graphical notation's «prefix … kind» vocabulary. `variation`
    /// subsumes its implied `abstract`.
    pub fn prefix_keywords(&self, e: ElementRef) -> Vec<&'static str> {
        let flag = |key: &str| {
            self.b.elements[e.0]
                .props
                .get(key)
                .and_then(|v| v.as_bool())
                .unwrap_or(false)
        };
        let mut out = Vec::new();
        if flag("isVariation") {
            out.push("variation");
        } else if flag("isAbstract") {
            out.push("abstract");
        }
        if flag("isIndividual") {
            out.push("individual");
        }
        if flag("isConstant") {
            out.push("constant");
        }
        if flag("isDerived") {
            out.push("derived");
        }
        if flag("isEnd") {
            out.push("end");
        }
        out
    }

    /// Client and supplier ends of a `Dependency` element, in written
    /// order (unresolved names are skipped). The `client#n` pending
    /// spellings resolve into `client`/`supplier` array properties.
    pub fn dependency_ends(&mut self, e: ElementRef) -> (Vec<ElementRef>, Vec<ElementRef>) {
        self.ensure_by_id();
        let side = |r: &Self, key: &str| -> Vec<ElementRef> {
            let Some(crate::properties::Atom::Array(items)) = r.b.elements[e.0].props.get(key)
            else {
                return Vec::new();
            };
            items
                .iter()
                .filter_map(|v| v.as_reference())
                .filter_map(|id| r.by_id.get(&id).copied())
                .map(ElementRef)
                .collect()
        };
        (side(self, "client"), side(self, "supplier"))
    }

    /// Whether the usage was declared in a featuring context — where
    /// the composite-by-default rule applies, so `isComposite == false`
    /// reflects a declared `ref`/direction/`end` rather than the
    /// unfeatured default. `None` for definitions and KerML features.
    pub fn is_featured_usage(&self, e: ElementRef) -> Option<bool> {
        self.b.usage_featuring.get(&e.0).copied()
    }

    /// The declared portion kind of an occurrence-family usage
    /// (`timeslice` | `snapshot`), if any.
    pub fn portion_kind(&self, e: ElementRef) -> Option<&str> {
        self.b.elements[e.0]
            .props
            .get("portionKind")
            .and_then(|v| v.as_str())
    }

    /// Declared `ordered` on a feature (`false` when unrecorded).
    pub fn is_ordered(&self, e: ElementRef) -> bool {
        self.b.elements[e.0]
            .props
            .get("isOrdered")
            .and_then(|v| v.as_bool())
            .unwrap_or(false)
    }

    /// Declared uniqueness of a feature (`true` when unrecorded —
    /// `nonunique` is the marked case).
    pub fn is_unique(&self, e: ElementRef) -> bool {
        self.b.elements[e.0]
            .props
            .get("isUnique")
            .and_then(|v| v.as_bool())
            .unwrap_or(true)
    }

    /// Every user-unit `alias name for X` membership, resolved:
    /// (alias name, target element). Unresolved targets are skipped.
    pub fn alias_members(&mut self) -> Vec<(String, ElementRef)> {
        self.ensure_by_id();
        let users: Vec<ElementRef> = self.user_elements().collect();
        let mut out = Vec::new();
        for e in users {
            let rels: Vec<usize> = self.b.elements[e.0]
                .owned_relationships
                .iter()
                .copied()
                .filter(|&r| self.b.elements[r].ty == "Membership")
                .collect();
            for rel in rels {
                let Some(name) = self.b.elements[rel]
                    .props
                    .get("memberName")
                    .and_then(|v| v.as_str())
                    .map(str::to_string)
                else {
                    continue;
                };
                let Some(t) = self.prop_target(rel, "memberElement") else {
                    continue;
                };
                out.push((name, ElementRef(t)));
            }
        }
        out
    }

    /// Whether the element is an enumeration/variant literal — a value that
    /// compares by identity (the evaluator's equality rule).
    pub fn is_enum_value(&self, e: ElementRef) -> bool {
        let el = &self.b.elements[e.0];
        el.ty == "EnumerationUsage"
            || el
                .owning_relationship
                .map(|r| self.b.elements[r].ty == "VariantMembership")
                .unwrap_or(false)
    }

    /// Every element with identity-comparable literal members, together
    /// with those members, in deterministic (element-index) order:
    /// `EnumerationDefinition`s with their literals, and variation
    /// owners with their `variant` members (a variation's variants are
    /// its closed set of legal choices, so both solve as finite sorts).
    pub fn enum_types(&self) -> Vec<(ElementRef, Vec<ElementRef>)> {
        // A build on a prepared library takes the library's own entries from
        // it, while the library rows and the library's body scopes are as
        // the library left them, and computes its own body scopes' entries.
        let library = self.b.prepared_from.as_ref().filter(|prepared| {
            self.b.elements.base_untouched()
                && Arc::ptr_eq(
                    self.b.elements.base_arc(),
                    prepared.builder.elements.base_arc(),
                )
                && Arc::ptr_eq(
                    self.b.elem_scope.base_arc(),
                    prepared.builder.elem_scope.base_arc(),
                )
        });
        let mut out: Vec<(usize, Vec<usize>)> = match library.map(|p| p.library_enum_types()) {
            Some(library)
                if self
                    .b
                    .scopes
                    .written_rows()
                    .all(|scope| !library.scopes.contains(&scope)) =>
            {
                let mut out: Vec<_> = library
                    .entries
                    .iter()
                    .filter(|(elem, _)| !self.b.elem_scope.local_contains_key(elem))
                    .cloned()
                    .collect();
                out.extend(enum_entries(&self.b, self.b.elem_scope.local_iter()));
                out
            }
            _ => enum_entries(&self.b, self.b.elem_scope.iter()),
        };
        out.sort_by_key(|(e, _)| *e);
        out.into_iter()
            .map(|(e, lits)| (ElementRef(e), lits.into_iter().map(ElementRef).collect()))
            .collect()
    }

    /// The metaclass of `e`'s owning membership (`ActorMembership`,
    /// `SubjectMembership`, `ObjectiveMembership`, …) — how a member
    /// was introduced. `None` for document roots.
    pub fn owning_membership_type(&self, e: ElementRef) -> Option<&'static str> {
        self.b.elements[e.0]
            .owning_relationship
            .map(|r| self.b.elements[r].ty)
    }

    /// Members owned by `e` through memberships of one specific
    /// metaclass (`ActorMembership`, `SubjectMembership`,
    /// `ObjectiveMembership`, …), in declaration order.
    pub fn members_via(&self, e: ElementRef, rel_ty: &str) -> Vec<ElementRef> {
        self.b.elements[e.0]
            .owned_relationships
            .iter()
            .copied()
            .filter(|&r| self.b.elements[r].ty == rel_ty)
            .filter_map(|r| self.rel_children(r).first().copied())
            .map(ElementRef)
            .collect()
    }

    /// Every user-unit comment and documentation body, resolved to the
    /// element it annotates, in declaration order: a `Documentation`
    /// annotates its owner; a `Comment` annotates its written `about`
    /// targets, or its owning namespace when it names none.
    pub fn annotation_bodies(&mut self) -> Vec<(ElementRef, String)> {
        self.annotation_docs()
            .into_iter()
            .map(|(e, _, body)| (e, body))
            .collect()
    }

    /// Explicit `about` / Annotation targets owned by an annotating
    /// element. Unresolved targets are omitted.
    pub fn annotated_elements(&mut self, e: ElementRef) -> Vec<ElementRef> {
        self.ensure_by_id();
        self.b.elements[e.0]
            .owned_relationships
            .iter()
            .copied()
            .filter(|&r| self.b.elements[r].ty == "Annotation")
            .filter_map(|r| self.prop_target(r, "annotatedElement"))
            .map(ElementRef)
            .collect()
    }

    /// [`Self::annotation_bodies`] with the annotating element's own
    /// declared name — `doc Description /* … */` names its
    /// Documentation element, and renderers use it as a heading.
    pub fn annotation_docs(&mut self) -> Vec<(ElementRef, Option<String>, String)> {
        self.annotation_notes()
            .into_iter()
            .map(|(_, target, name, body)| (target, name, body))
            .collect()
    }

    /// [`Self::annotation_docs`] with the annotating Comment /
    /// Documentation element itself, first in each tuple — diagram
    /// notes carry its identity (selection, deletion, source
    /// navigation).
    pub fn annotation_notes(&mut self) -> Vec<(ElementRef, ElementRef, Option<String>, String)> {
        self.ensure_by_id();
        let all: Vec<ElementRef> = self.user_elements().collect();
        let mut out = Vec::new();
        for e in all {
            let ty = self.b.elements[e.0].ty;
            if ty != "Comment" && ty != "Documentation" {
                continue;
            }
            let Some(body) = self.b.elements[e.0]
                .props
                .get("body")
                .and_then(|v| v.as_str())
                .map(str::to_string)
            else {
                continue;
            };
            if body.trim().is_empty() {
                continue;
            }
            let name = self.b.elements[e.0]
                .props
                .get("declaredName")
                .and_then(|v| v.as_str())
                .map(str::to_string);
            let abouts: Vec<usize> = self.b.elements[e.0]
                .owned_relationships
                .iter()
                .copied()
                .filter(|&r| self.b.elements[r].ty == "Annotation")
                .filter_map(|r| self.prop_target(r, "annotatedElement"))
                .collect();
            if abouts.is_empty() {
                if let Some(owner) = self.owner(e) {
                    out.push((e, owner, name, body));
                }
            } else {
                for a in abouts {
                    out.push((e, ElementRef(a), name.clone(), body.clone()));
                }
            }
        }
        out
    }

    /// The documentation bodies annotating `e` itself: its owned
    /// Documentation/Comment children without an explicit `about` list
    /// (those annotate other elements), as `(declared name, body)` in
    /// declaration order. Unlike [`Self::annotation_docs`] — which
    /// enumerates user units only — this answers for any element,
    /// library elements included, so a reader can follow a usage's
    /// docs across the standard-library boundary.
    pub fn element_docs(&mut self, e: ElementRef) -> Vec<(Option<String>, String)> {
        self.ensure_by_id();
        let mut out = Vec::new();
        for m in self.b.owned_member_elems(e.0, false) {
            let ty = self.b.elements[m].ty;
            if ty != "Comment" && ty != "Documentation" {
                continue;
            }
            let has_abouts = self.b.elements[m]
                .owned_relationships
                .iter()
                .any(|&r| self.b.elements[r].ty == "Annotation");
            if has_abouts {
                continue;
            }
            let Some(body) = self.b.elements[m]
                .props
                .get("body")
                .and_then(|v| v.as_str())
                .map(str::to_string)
            else {
                continue;
            };
            if body.trim().is_empty() {
                continue;
            }
            let name = self.b.elements[m]
                .props
                .get("declaredName")
                .and_then(|v| v.as_str())
                .map(str::to_string);
            out.push((name, body));
        }
        out
    }

    /// Known metadata annotating `e`, including prefix/about-less metadata and
    /// identity-validated explicit `about` annotations, in declaration order.
    /// Unresolved or malformed annotation associations are omitted.
    pub fn metadata_of(&self, e: ElementRef) -> Vec<ElementRef> {
        self.b
            .metadata_of
            .get(&e.0)
            .map(|v| v.iter().copied().map(ElementRef).collect())
            .unwrap_or_default()
    }

    /// `e`'s import targets, resolved: one entry per owned import
    /// relationship, `(target element, is_namespace_import)`. A
    /// membership import's target is the imported member itself (the
    /// serialized value is its owning Membership — dereferenced here).
    pub fn import_targets(&mut self, e: ElementRef) -> Vec<(ElementRef, bool)> {
        self.ensure_by_id();
        let rels: Vec<(usize, bool)> = self.b.elements[e.0]
            .owned_relationships
            .iter()
            .copied()
            .filter_map(|r| match self.b.elements[r].ty {
                "NamespaceImport" | "NamespaceExpose" => Some((r, true)),
                "MembershipImport" | "MembershipExpose" => Some((r, false)),
                _ => None,
            })
            .collect();
        let mut out = Vec::new();
        for (rel, is_ns) in rels {
            let key = if is_ns {
                "importedNamespace"
            } else {
                "importedMembership"
            };
            let Some(mut t) = self.prop_target(rel, key) else {
                continue;
            };
            if self.b.elements[t].ty.ends_with("Membership") {
                t = match self.prop_target(t, "memberElement") {
                    Some(m) => m,
                    None => match self.rel_children(t).first() {
                        Some(&c) => c,
                        None => continue,
                    },
                };
            }
            out.push((ElementRef(t), is_ns));
        }
        out
    }

    /// [`Self::import_targets`] with the notation-relevant granularity:
    /// (target, namespace-import (`::*`), recursive (`::**`),
    /// visibility — the «private import» label spelling).
    pub fn import_details(&mut self, e: ElementRef) -> Vec<(ElementRef, bool, bool, String)> {
        self.ensure_by_id();
        let rels: Vec<(usize, bool)> = self.b.elements[e.0]
            .owned_relationships
            .iter()
            .copied()
            .filter_map(|r| match self.b.elements[r].ty {
                "NamespaceImport" | "NamespaceExpose" => Some((r, true)),
                "MembershipImport" | "MembershipExpose" => Some((r, false)),
                _ => None,
            })
            .collect();
        let mut out = Vec::new();
        for (rel, is_ns) in rels {
            let recursive = self.b.elements[rel]
                .props
                .get("isRecursive")
                .and_then(|v| v.as_bool())
                .unwrap_or(false);
            let visibility = self.b.elements[rel]
                .props
                .get("visibility")
                .and_then(|v| v.as_str())
                .unwrap_or("public")
                .to_string();
            let key = if is_ns {
                "importedNamespace"
            } else {
                "importedMembership"
            };
            let Some(mut t) = self.prop_target(rel, key) else {
                continue;
            };
            if self.b.elements[t].ty.ends_with("Membership") {
                t = match self.prop_target(t, "memberElement") {
                    Some(m) => m,
                    None => match self.rel_children(t).first() {
                        Some(&c) => c,
                        None => continue,
                    },
                };
            }
            out.push((ElementRef(t), is_ns, recursive, visibility));
        }
        out
    }

    /// The declaration site of `e` as (unit name, 1-based line, column)
    /// — hyperlink targets for diagrams. The declared-name span when
    /// one was recorded, else the member extent's start. `None` for
    /// synthesized elements.
    pub fn declaration_position(&self, e: ElementRef) -> Option<(&str, u32, u32)> {
        let offset = self
            .b
            .decl_spans
            .get(&e.0)
            .or_else(|| self.b.member_spans.get(&e.0))
            .map(|s| s.start)?;
        let unit = self.b.unit_of_elem(e.0);
        let (name, lines) = self.unit_meta.get(unit)?;
        let lc = lines.line_col(offset);
        Some((name.as_str(), lc.line, lc.col))
    }

    fn ensure_by_id(&mut self) {
        self.sync_semantic_publication();
        if self.by_id_built_for != self.b.elements.len() {
            self.by_id_built_for = self.b.elements.len();
            // While no two rows share an id the builder's index is this table,
            // made from the frozen rows' kept table and this build's own rows.
            let unique = self.b.literal_identities_unique(None) == Some(true);
            let n = self.b.elements.len();
            let index = self
                .b
                .id_index
                .as_ref()
                .filter(|_| unique && self.b.id_index_built_for == n);
            self.by_id = match index {
                Some(index) => Arc::clone(index),
                None => Arc::new(
                    self.b
                        .elements
                        .iter()
                        .enumerate()
                        .map(|(i, el)| (el.id, i))
                        .collect(),
                ),
            };
        }
    }

    /// Elements owned *by relationship* `rel` (its `ownedRelatedElement`
    /// children), in creation order.
    fn rel_children(&self, rel: usize) -> Vec<usize> {
        self.b.elements[rel].children.to_vec()
    }

    /// The element an `@id`-valued property of one of `e`'s owned
    /// `rel_ty` relationships points at (`None` when unresolved — an
    /// unresolved reference serializes an `@ref` spelling instead).
    fn rel_prop_target(&self, e: usize, rel_ty: &str, key: &str) -> Option<usize> {
        let rel = self.b.elements[e]
            .owned_relationships
            .iter()
            .find(|&&r| self.b.elements[r].ty == rel_ty)?;
        self.prop_target(*rel, key)
    }

    fn prop_target(&self, e: usize, key: &str) -> Option<usize> {
        let id = self.b.elements[e].props.get(key)?.as_reference()?;
        self.by_id.get(&id).copied()
    }

    /// Expand a `ReferenceSubsetting` target into its written feature
    /// chain: a synthesized chain feature (one `FeatureChaining` per
    /// link) yields its links first→last, stopping at the first
    /// unresolved link; anything else is a single-link chain.
    fn expand_chain(&self, target: usize) -> Vec<ElementRef> {
        let chainings: Vec<usize> = self.b.elements[target]
            .owned_relationships
            .iter()
            .copied()
            .filter(|&r| self.b.elements[r].ty == "FeatureChaining")
            .collect();
        if chainings.is_empty() {
            return vec![ElementRef(target)];
        }
        let mut links = Vec::new();
        for rel in chainings {
            match self.prop_target(rel, "chainingFeature") {
                Some(link) => links.push(ElementRef(link)),
                None => break,
            }
        }
        links
    }

    /// One `@ref`-spelled (unresolved) property value of one of `e`'s
    /// owned `rel_ty` relationships — the qualified name as written.
    fn rel_prop_spelling(&self, e: usize, rel_ty: &str, key: &str) -> Option<String> {
        let rel = self.b.elements[e]
            .owned_relationships
            .iter()
            .find(|&&r| self.b.elements[r].ty == rel_ty)?;
        self.b.elements[*rel]
            .props
            .get(key)?
            .get("@ref")?
            .as_str()
            .map(str::to_string)
    }

    /// The end targets of a connector-family element (connections,
    /// bindings, interfaces, successions, flows, KerML connectors): one
    /// entry per end feature in declaration order, each the feature
    /// chain as written first→last (`a.b` → `[a, b]`; a simple end
    /// names one link). An unspelled end — the implicit source of a
    /// succession — yields an empty chain and no spelling; an
    /// *unresolved* one yields its written spelling instead. End arity
    /// stays stable either way.
    pub fn connector_end_targets(&mut self, e: ElementRef) -> Vec<ConnectorEndTarget> {
        self.ensure_by_id();
        let end_rels: Vec<usize> = self.b.elements[e.0]
            .owned_relationships
            .iter()
            .copied()
            .filter(|&r| self.b.elements[r].ty == "EndFeatureMembership")
            .collect();
        let mut ends = Vec::new();
        for rel in end_rels {
            let Some(&f) = self.rel_children(rel).first() else {
                continue;
            };
            let mut end = ConnectorEndTarget {
                chain: Vec::new(),
                spelling: None,
                feature: ElementRef(f),
            };
            match self.rel_prop_target(f, "ReferenceSubsetting", "referencedFeature") {
                Some(t) => end.chain.extend(self.expand_chain(t)),
                None => {
                    end.spelling =
                        self.rel_prop_spelling(f, "ReferenceSubsetting", "referencedFeature");
                }
            }
            // Flow ends spell their last step as a Redefinition on an
            // owned reference feature (the RS above is the chain prefix,
            // present only when one was written).
            if self.b.elements[f].ty == "FlowEnd" {
                if let Some(ru) = self.b.elements[f]
                    .owned_relationships
                    .iter()
                    .find(|&&r| self.b.elements[r].ty == "FeatureMembership")
                    .copied()
                    .and_then(|fm| self.rel_children(fm).first().copied())
                {
                    match self.rel_prop_target(ru, "Redefinition", "redefinedFeature") {
                        Some(step) => end.chain.push(ElementRef(step)),
                        None => {
                            end.spelling = end.spelling.take().or_else(|| {
                                self.rel_prop_spelling(ru, "Redefinition", "redefinedFeature")
                            });
                        }
                    }
                }
            }
            ends.push(end);
        }
        ends
    }

    /// The written reference targets of `e`'s own `ReferenceSubsetting`
    /// relationships (a `perform a.b` / `exhibit s` reference), one
    /// feature chain per relationship, links first→last.
    pub fn referenced_features(&mut self, e: ElementRef) -> Vec<Vec<ElementRef>> {
        self.ensure_by_id();
        self.b.elements[e.0]
            .owned_relationships
            .iter()
            .copied()
            .filter(|&r| self.b.elements[r].ty == "ReferenceSubsetting")
            .filter_map(|r| self.prop_target(r, "referencedFeature"))
            .map(|t| self.expand_chain(t))
            .collect()
    }

    /// A transition's constituent parts (SysML 7.16 TransitionUsage
    /// lowering): resolved source state, trigger accept action, guard
    /// expression (as written), effect action, and the target state (the
    /// last link of its transition succession's target end).
    pub fn transition_parts(&mut self, e: ElementRef) -> TransitionParts {
        self.ensure_by_id();
        let rels: Vec<(usize, &'static str)> = self.b.elements[e.0]
            .owned_relationships
            .iter()
            .map(|&r| (r, self.b.elements[r].ty))
            .collect();
        let mut parts = TransitionParts {
            source: None,
            target: None,
            trigger: None,
            effect: None,
            guard: self
                .b
                .transition_guards
                .get(&e.0)
                .map(|(_, expr)| expr.clone()),
        };
        for (rel, ty) in rels {
            match ty {
                "Membership" if parts.source.is_none() => {
                    parts.source = self.prop_target(rel, "memberElement").map(ElementRef);
                }
                "TransitionFeatureMembership" => {
                    let kind = self.b.elements[rel]
                        .props
                        .get("kind")
                        .and_then(|v| v.as_str())
                        .unwrap_or("");
                    let child = self.rel_children(rel).first().copied().map(ElementRef);
                    match kind {
                        "trigger" => parts.trigger = child,
                        "effect" => parts.effect = child,
                        _ => {}
                    }
                }
                "OwningMembership" => {
                    if let Some(succ) = self.rel_children(rel).first().copied() {
                        // A chain source (`first a.b`): the membership owns
                        // the synthesized chain feature and names it.
                        if parts.source.is_none()
                            && self.b.elements[succ].ty == "Feature"
                            && self.b.elements[succ]
                                .owned_relationships
                                .iter()
                                .any(|&r| self.b.elements[r].ty == "FeatureChaining")
                        {
                            parts.source = self
                                .prop_target(rel, "memberElement")
                                .map(ElementRef)
                                .or(Some(ElementRef(succ)));
                            continue;
                        }
                        if self.b.elements[succ].ty.starts_with("Succession") {
                            parts.target = self
                                .connector_end_targets(ElementRef(succ))
                                .into_iter()
                                .rev()
                                .find(|end| !end.chain.is_empty())
                                .and_then(|end| end.chain.last().copied());
                        }
                    }
                }
                _ => {}
            }
        }
        parts
    }

    /// A state's entry/do/exit subactions in declaration order:
    /// (`"entry"` | `"do"` | `"exit"`, the action element).
    pub fn state_subactions(&mut self, e: ElementRef) -> Vec<(String, ElementRef)> {
        self.b.elements[e.0]
            .owned_relationships
            .iter()
            .copied()
            .filter(|&r| self.b.elements[r].ty == "StateSubactionMembership")
            .filter_map(|rel| {
                let kind = self.b.elements[rel]
                    .props
                    .get("kind")
                    .and_then(|v| v.as_str())?
                    .to_string();
                let child = self.rel_children(rel).first().copied()?;
                Some((kind, ElementRef(child)))
            })
            .collect()
    }

    /// `e`'s declared `direction` (`in`/`out`/`inout`), when spelled.
    pub fn declared_direction(&self, e: ElementRef) -> Option<&str> {
        self.b.elements[e.0]
            .props
            .get("direction")?
            .as_str()
            .filter(|s| !s.is_empty())
    }
}

/// One connector end's target (see
/// [`ResolvedModel::connector_end_targets`]).
#[derive(Clone, Debug)]
pub struct ConnectorEndTarget {
    /// The resolved feature chain as written, first→last (`a.b` →
    /// `[a, b]`); empty when the end was unspelled or unresolved.
    pub chain: Vec<ElementRef>,
    /// The written qualified name of an *unresolved* end (`None` when
    /// the end resolved or was never spelled).
    pub spelling: Option<String>,
    /// The connector's own end feature — carrier of the end's role
    /// name and multiplicity in the graphical notation.
    pub feature: ElementRef,
}

/// The constituent parts of one `TransitionUsage` (see
/// [`ResolvedModel::transition_parts`]).
#[derive(Clone, Debug)]
pub struct TransitionParts {
    /// The source state (`first S` / the leading shorthand name).
    pub source: Option<ElementRef>,
    /// The target state (the transition succession's target end).
    pub target: Option<ElementRef>,
    /// The trigger `AcceptActionUsage` (`accept X`).
    pub trigger: Option<ElementRef>,
    /// The effect action (`do action ...`).
    pub effect: Option<ElementRef>,
    /// The guard expression as written (`if expr`).
    pub guard: Option<Expr>,
}

/// A doc/comment body normalized for display: each line loses its
/// leading whitespace and the conventional block-comment `*` gutter;
/// blank edges are trimmed. Shared by every renderer that shows doc
/// text outside its source spelling (hover, completion, diagram notes).
pub fn doc_display_text(body: &str) -> String {
    let lines: Vec<&str> = body
        .lines()
        .map(|l| {
            let t = l.trim_start();
            let t = t
                .strip_prefix('*')
                .map(|rest| rest.strip_prefix(' ').unwrap_or(rest))
                .unwrap_or(t);
            t.trim_end()
        })
        .collect();
    lines.join("\n").trim().to_string()
}

/// Split `A::'two words'::b` into raw (unescaped) segments: the
/// inverse of `escape_name` per segment, so a name that spells as
/// `'a\\nb'` (a newline) resolves to the element the spelling came
/// from. Empty segments are dropped.
fn split_qualified(name: &str) -> Vec<String> {
    let mut out = sysmlv2_syntax::name::split_canonical(name);
    out.retain(|s| !s.is_empty());
    out
}

#[cfg(test)]
mod split_qualified_tests {
    use super::split_qualified;

    #[test]
    fn decodes_control_escapes_like_escape_name_spells_them() {
        let raw = "Optics Bench to Sensor-Hub Interface Point\nAlignment Error Analysis";
        let spelled = format!("P::{}", sysmlv2_syntax::ast::escape_name(raw));
        assert_eq!(
            spelled,
            "P::'Optics Bench to Sensor-Hub Interface Point\\nAlignment Error Analysis'"
        );
        assert_eq!(
            split_qualified(&spelled),
            vec!["P".to_string(), raw.to_string()]
        );
        for raw in [
            "a\tb",
            "a\rb",
            "a\u{0008}b",
            "a\u{000C}b",
            "it's",
            "back\\slash",
            "a::b",
        ] {
            let spelled = sysmlv2_syntax::ast::escape_name(raw);
            assert_eq!(
                split_qualified(&spelled),
                vec![raw.to_string()],
                "{spelled}"
            );
        }
    }

    #[test]
    fn spelled_qualified_name_resolves_back_to_its_element() {
        let mut model = crate::model::Model::new();
        let unit = model.add_source(
            "t.sysml".to_string(),
            "package P { part def 'Optics Bench to Sensor-Hub Interface Point\\nAlignment Error Analysis'; }",
        );
        assert!(unit.diagnostics.is_empty(), "{:?}", unit.diagnostics);
        let mut r = super::ResolvedModel::build(&model);
        let pkg = r.resolve_qualified("P").unwrap();
        let def = r.owned_members(pkg)[0];
        let spelled = r.element_qualified_name(def).unwrap();
        assert_eq!(
            spelled,
            "P::'Optics Bench to Sensor-Hub Interface Point\\nAlignment Error Analysis'"
        );
        assert_eq!(r.resolve_qualified(&spelled), Some(def));
    }

    #[test]
    fn keeps_bare_and_plain_quoted_segments() {
        assert_eq!(
            split_qualified("A::'two words'::b"),
            vec!["A".to_string(), "two words".to_string(), "b".to_string()]
        );
        assert_eq!(split_qualified("::A::"), vec!["A".to_string()]);
    }
}

#[cfg(test)]
mod unused_imports_tests;

#[cfg(test)]
mod replay_dependencies_tests;

#[cfg(test)]
mod identity_tables_tests;

#[cfg(test)]
mod indexed_reads_tests;

/// Persist element headers and their variable-length lists as separate tables.
/// A decoded library shares each table's contiguous backing storage.
mod element_table {
    use super::*;
    use crate::{
        flat::{self, Row},
        layered::LayeredVec,
        properties::{Atom, Key, Properties},
    };
    use serde::{Deserialize, Deserializer, Serialize, Serializer, ser::SerializeTuple};
    #[derive(Serialize)]
    struct HeaderRef<'a> {
        ty: &'a str,
        id: Uuid,
        path: std::borrow::Cow<'a, str>,
        present: u64,
        flags: u64,
        owner: Option<usize>,
    }
    #[derive(Deserialize)]
    struct Header {
        ty: Kind,
        id: Uuid,
        path: String,
        present: u64,
        flags: u64,
        owner: Option<usize>,
    }
    struct Kind(&'static str);
    impl<'de> Deserialize<'de> for Kind {
        fn deserialize<D: Deserializer<'de>>(d: D) -> Result<Self, D::Error> {
            struct Visitor;
            impl serde::de::Visitor<'_> for Visitor {
                type Value = Kind;
                fn expecting(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
                    f.write_str("a known metaclass")
                }
                fn visit_str<E: serde::de::Error>(self, s: &str) -> Result<Self::Value, E> {
                    crate::metaclass::canonical_name(s)
                        .map(Kind)
                        .ok_or_else(|| E::custom("unknown element metaclass"))
                }
            }
            d.deserialize_str(Visitor)
        }
    }
    pub fn serialize<S: Serializer>(elements: &LayeredVec<Elem>, s: S) -> Result<S::Ok, S::Error> {
        struct Headers<'a>(&'a LayeredVec<Elem>);
        impl Serialize for Headers<'_> {
            fn serialize<S: Serializer>(&self, s: S) -> Result<S::Ok, S::Error> {
                s.collect_seq(self.0.iter().enumerate().map(|(i, e)| HeaderRef {
                    ty: e.ty,
                    id: e.id,
                    // The table holds whole paths, which decode as such.
                    path: if e.path_parent.is_some() {
                        whole_path(self.0, i).into()
                    } else {
                        e.path.as_str().into()
                    },
                    present: e.props.present,
                    flags: e.props.flags,
                    owner: e.owning_relationship,
                }))
            }
        }
        let mut tuple = s.serialize_tuple(4)?;
        tuple.serialize_element(&Headers(elements))?;
        tuple.serialize_element(&flat::Slices(
            elements.iter().map(|e| &*e.props.entries).collect(),
        ))?;
        tuple.serialize_element(&flat::Slices(
            elements.iter().map(|e| &*e.owned_relationships).collect(),
        ))?;
        tuple.serialize_element(&flat::Slices(
            elements.iter().map(|e| &*e.children).collect(),
        ))?;
        tuple.end()
    }
    pub fn deserialize<'de, D: Deserializer<'de>>(d: D) -> Result<LayeredVec<Elem>, D::Error> {
        #[derive(Deserialize)]
        struct Wire {
            headers: Vec<Header>,
            #[serde(with = "flat::table")]
            props: Vec<Row<(Key, Atom)>>,
            #[serde(with = "flat::table")]
            owned: Vec<Row<usize>>,
            #[serde(with = "flat::table")]
            children: Vec<Row<usize>>,
        }
        let wire = Wire::deserialize(d)?;
        let n = wire.headers.len();
        if wire.props.len() != n
            || wire.owned.len() != n
            || wire.children.len() != n
            || wire
                .props
                .iter()
                .any(|r| r.windows(2).any(|p| p[0].0 >= p[1].0))
        {
            return Err(serde::de::Error::custom("invalid element table"));
        }
        Ok(wire
            .headers
            .into_iter()
            .zip(wire.props)
            .zip(wire.owned)
            .zip(wire.children)
            .map(|(((h, entries), owned_relationships), children)| Elem {
                ty: h.ty.0,
                id: h.id,
                path: h.path,
                path_parent: None,
                props: Properties {
                    present: h.present,
                    flags: h.flags,
                    entries,
                },
                owned_relationships,
                children,
                owning_relationship: h.owner,
            })
            .collect())
    }
}

#[cfg(test)]
mod element_table_tests {
    use super::*;
    use serde::{Deserialize, Serialize};
    #[derive(Serialize, Deserialize)]
    struct Table(#[serde(with = "super::element_table")] crate::layered::LayeredVec<Elem>);
    #[test]
    fn malformed_headers_and_unsorted_properties_are_rejected() {
        let mut model = crate::model::Model::new();
        model.add_library_source("l.sysml", "package L { attribute x = 1; }");
        let mut b = Builder::default();
        b.build_model(&model);
        let clean = Table(b.elements);
        let bytes = crate::cache_codec::encode(&clean).unwrap();
        assert!(crate::cache_codec::decode::<Table>(&bytes).is_ok());
        let mut bad = Table(clean.0.clone());
        bad.0[0].ty = "UnknownMetaclass";
        assert!(
            crate::cache_codec::decode::<Table>(&crate::cache_codec::encode(&bad).unwrap())
                .is_err()
        );
        let mut bad = Table(clean.0.clone());
        let row = (0..bad.0.len())
            .find(|&i| bad.0[i].props.entries.len() > 1)
            .unwrap();
        bad.0[row].props.entries.make_mut().reverse();
        assert!(
            crate::cache_codec::decode::<Table>(&crate::cache_codec::encode(&bad).unwrap())
                .is_err()
        );
        let mut bad = Table(clean.0);
        let duplicate = bad.0[row].props.entries[0].clone();
        bad.0[row].props.entries.make_mut().insert(0, duplicate);
        assert!(
            crate::cache_codec::decode::<Table>(&crate::cache_codec::encode(&bad).unwrap())
                .is_err()
        );
    }

    /// The table carries whole ownership paths, however the builder holds
    /// them, and decodes to the same paths and identities.
    #[test]
    fn whole_paths_survive_the_table() {
        let mut model = crate::model::Model::new();
        model.add_library_source(
            "l.sysml",
            "package L { part p { attribute x = 1 + 2 * 3; } }",
        );
        let mut b = Builder::default();
        b.build_model(&model);
        assert!(b.elements.iter().any(|e| e.path_parent.is_some()));
        let decoded: Table = crate::cache_codec::decode(
            &crate::cache_codec::encode(&Table(b.elements.clone())).unwrap(),
        )
        .unwrap();
        assert_eq!(decoded.0.len(), b.elements.len());
        for i in 0..b.elements.len() {
            assert_eq!(whole_path(&decoded.0, i), whole_path(&b.elements, i));
            assert_eq!(decoded.0[i].id, b.elements[i].id);
        }
    }
}

#[cfg(test)]
mod ownership_path_tests {
    use super::*;

    /// An identity derived from an ownership path is the version-5
    /// identity of the whole path, whether the parent's hash state was
    /// kept or the parent's path is read afresh — including for children
    /// of elements created before the states were kept or after they
    /// were dropped.
    #[test]
    fn identities_hash_the_whole_ownership_path() {
        for keep in [true, false] {
            let mut b = Builder::default();
            let mut paths = Vec::new();
            let root = b.new_element("Namespace", None, "$root/u.sysml".into());
            paths.push("$root/u.sysml".to_string());
            if keep {
                b.keep_path_hashes();
            }
            let mut parent = root;
            for level in 0..40 {
                let segment = format!("m{level}");
                let rel = b.new_relationship("OwningMembership", parent, &segment);
                paths.push(format!("{}/{segment}", paths[parent]));
                // Segments may be empty or hold separators of their own.
                let segment = ["", "x/y", "e", "first"][level % 4];
                let element = b.new_owned_element("PartUsage", rel, segment);
                paths.push(format!("{}/{segment}", paths[rel]));
                parent = element;
            }
            b.path_hashes = None;
            for owner in [root, parent, parent / 2] {
                b.new_relationship("Membership", owner, "late");
                paths.push(format!("{}/late", paths[owner]));
            }
            assert_eq!(paths.len(), b.elements.len());
            for (i, path) in paths.iter().enumerate() {
                assert_eq!(&whole_path(&b.elements, i), path);
                assert_eq!(
                    b.elements[i].id,
                    Uuid::new_v5(&ID_NAMESPACE, path.as_bytes()),
                    "{path}"
                );
            }
        }
    }

    /// Lowering stores and hashes a bounded number of path bytes per
    /// element, however deep the ownership nests. Measured in bytes rather
    /// than in wall-clock time: the counts are the work and the memory the
    /// paths take, and do not depend on the machine.
    ///
    /// The longest operator chain the parser admits nests its first operand
    /// over four thousand ownership levels deep. Holding and hashing each
    /// element's whole path took about 233 MB of each over its seventeen
    /// thousand elements, against about 100 KB with segments.
    #[test]
    fn path_cost_is_linear_in_the_ownership_depth() {
        // Lowering the chain recurses once per operator, so the probe runs
        // on a thread with room for it; the count is kept per thread, so
        // the build runs there too.
        std::thread::Builder::new()
            .stack_size(64 << 20)
            .spawn(|| {
                let terms = sysmlv2_syntax::parser::MAX_EXPR_OPERATORS as usize;
                let chain = (0..terms)
                    .map(|i| format!("a{i} > 0"))
                    .collect::<Vec<_>>()
                    .join(" and ");
                let mut model = crate::model::Model::new();
                model.add_source(
                    "chain.sysml",
                    &format!("package P {{ part x {{ attribute v = {chain}; }} }}"),
                );
                assert!(!model.has_errors());
                let before = path_bytes_hashed();
                let r = ResolvedModel::build(&model);
                let hashed = path_bytes_hashed() - before;
                let elements = r.b.elements.len();
                let stored: usize = r.b.elements.iter().map(|e| e.path.len()).sum();
                assert!(
                    stored <= 16 * elements,
                    "{stored} path bytes held for {elements} elements"
                );
                assert!(
                    hashed <= 32 * elements,
                    "{hashed} path bytes hashed for {elements} elements"
                );
            })
            .unwrap()
            .join()
            .unwrap();
    }
}

#[cfg(test)]
mod filter_origin_tests {
    use super::*;
    use crate::model::Model;

    #[test]
    fn prepared_filters_reject_invalid_source_scope_and_filter_indexes() {
        let mut model = Model::new();
        model.add_library_source("lib.sysml","package Items { part def X; } package P { filter true; import Items::*[true]; import Items::X[true]; }");
        assert!(!model.has_errors());
        let r = ResolvedModel::build(&model);
        assert!(r.b.valid_library(1));
        for field in [0, 1] {
            let mut b = r.b.clone();
            if field == 0 {
                b.filter_exprs[0].0 = b.elements.len();
            } else {
                b.filter_exprs[0].1 = b.scopes.len();
            }
            assert!(!b.valid_library(1));
        }
        for kind in [0, 1, 2] {
            let mut b = r.b.clone();
            let fid = b.filter_exprs.len();
            let scope = b.scopes.iter().position(|s| !s.filters.is_empty()).unwrap();
            match kind {
                0 => b.scopes[scope].filters.push(fid),
                1 => b.scopes[scope].imports[0].filters.push(fid),
                _ => b.scopes[scope].member_imports[0].filters.push(fid),
            }
            assert!(!b.valid_library(1));
        }
        let mut b = r.b.clone();
        b.filters_active.clear();
        assert!(!b.valid_library(1));
    }

    #[test]
    fn filter_execution_restores_source_and_reentrancy_state() {
        let id = "88888888-8888-4888-8888-888888888888";
        let mut model = Model::new();
        model.add_source("first.sysml", "package First;");
        model.add_source("filter.sysml",&format!("package P {{ metadata def Actual; metadata def '{id}'; package Items {{ #Actual part def X; }} package View {{ filter @'{id}'; filter false and @missing; filter true or @missing; filter @missing; public import Items::*; }} }}"));
        assert!(!model.has_errors());
        let mut r = ResolvedModel::build(&model);
        let actual = r.resolve_qualified("P::Actual").unwrap();
        let ordinary = r.resolve_qualified(&format!("P::'{id}'")).unwrap();
        let sites = r.references_to(ordinary);
        assert_eq!(sites.len(), 1);
        let id = id.parse().unwrap();
        r.override_ids(&HashMap::from([(r.element_id(actual), id)]));
        let mut hints =
            HashMap::from([((r.element_id(sites[0].owner), sites[0].kind.clone()), id)]);
        assert!(r.bind_id_spelled_references_with(&mut hints).contains(&id));
        let x = r.resolve_qualified("P::Items::X").unwrap();
        let view = r.resolve_qualified("P::View").unwrap();
        let scope = *r.b.elem_scope.get(&view.0).unwrap();
        let filters = r.b.scopes[scope].filters.clone();
        assert_eq!(filters.len(), 4);
        for origin in [None, Some(0)] {
            r.b.identity_origin_unit = origin;
            for (&fid, expected) in
                filters
                    .iter()
                    .zip([Tri::True, Tri::False, Tri::True, Tri::Unknown])
            {
                assert_eq!(r.b.filter_verdict(fid, x.0, 0), expected);
                assert!(!r.b.filters_active[fid]);
                assert_eq!(r.b.identity_origin_unit, origin);
                r.b.filters_active[fid] = true;
                assert_eq!(r.b.filter_verdict(fid, x.0, 0), Tri::Unknown);
                assert!(r.b.filters_active[fid]);
                assert_eq!(r.b.identity_origin_unit, origin);
                r.b.filters_active[fid] = false;
                assert_eq!(
                    r.b.filter_verdict(fid, x.0, MAX_RESOLUTION_DEPTH + 1),
                    Tri::Unknown
                );
                assert_eq!(r.b.identity_origin_unit, origin);
            }
        }
    }
}

#[cfg(test)]
mod source_query_tests {
    use super::*;
    use crate::{
        eval::{EvalError, Value},
        model::Model,
    };

    #[test]
    fn source_callbacks_restore_after_nesting_errors_and_panics() {
        let mut m = Model::new();
        m.add_source("a.sysml", "package A;");
        m.add_source("b.sysml", "package B;");
        let mut r = ResolvedModel::build(&m);
        let a = r.resolve_qualified("A").unwrap();
        let b = r.resolve_qualified("B").unwrap();
        for prior in [None, Some(0), Some(1)] {
            r.b.identity_origin_unit = prior;
            let result: Result<(), ()> = r.with_source(a, |r| {
                assert_eq!(r.b.identity_origin_unit, Some(0));
                r.with_source(b, |r| assert_eq!(r.b.identity_origin_unit, Some(1)));
                assert_eq!(r.b.identity_origin_unit, Some(0));
                Err(())
            });
            assert!(result.is_err());
            assert_eq!(r.b.identity_origin_unit, prior);
            assert!(
                std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                    r.with_source(a, |r| r.with_source(b, |_| panic!("test unwind")))
                }))
                .is_err()
            );
            assert_eq!(r.b.identity_origin_unit, prior);
        }
    }

    #[test]
    fn value_chain_preserves_uncertainty_and_bounds_recursive_work() {
        let mut m = Model::new();
        m.add_source("model.sysml", "package P { part def T; }");
        let mut r = ResolvedModel::build(&m);
        let ty = r.resolve_qualified("P::T").unwrap();
        let name = QualifiedName {
            is_global: false,
            segments: vec![Name {
                value: "x".into(),
                span: Default::default(),
            }],
            span: Default::default(),
        };
        let instance = |v| Value::Instance {
            ty,
            ty_name: "T".into(),
            fields: vec![("x".into(), v)],
        };
        assert_eq!(
            r.evaluate_value_chain(Value::Indeterminate, &[&name, &name]),
            Ok(Value::Indeterminate)
        );
        assert_eq!(
            r.evaluate_value_chain(instance(instance(Value::Integer(7))), &[&name, &name]),
            Ok(Value::Integer(7))
        );
        let repeated = Value::Sequence(vec![
            instance(Value::Integer(7)),
            instance(Value::Integer(7)),
        ]);
        assert_eq!(
            r.evaluate_value_chain(repeated, &[&name]),
            Ok(Value::Integer(7))
        );
        let mut empty = name.clone();
        empty.segments.clear();
        assert!(matches!(
            r.evaluate_value_chain(instance(Value::Integer(7)), &[&empty]),
            Err(EvalError::Unsupported(_))
        ));
        let many = Value::Sequence((0..4000).map(|i| instance(Value::Integer(i))).collect());
        assert!(matches!(
            r.evaluate_value_chain(many, &[&name]),
            Err(EvalError::Budget(_))
        ));
        let mut deep = Value::Integer(1);
        for _ in 0..=crate::eval::MAX_CALL_DEPTH {
            deep = Value::Quantity(Box::new(deep), crate::eval::Unit::from_dims(Vec::new()));
        }
        assert!(matches!(
            r.evaluate_value_chain(instance(deep.clone()), &[&name]),
            Err(EvalError::Budget(_))
        ));
        // An empty path performs no recursive work, even on a deep receiver.
        assert_eq!(r.evaluate_value_chain(deep.clone(), &[]), Ok(deep));
        assert_eq!(
            r.evaluate_value_chain(instance(Value::Integer(8)), &[&name]),
            Ok(Value::Integer(8))
        );
    }
}

#[cfg(test)]
mod positional_member_tests {
    use super::*;
    use crate::model::Model;

    fn resolved(name: &str, source: &str) -> ResolvedModel {
        let mut model = Model::new();
        model.add_source(name, source);
        assert!(!model.has_errors(), "{source}");
        ResolvedModel::build(&model)
    }

    /// A parameter takes members from what its position pairs it with, and
    /// from nothing else that shares its name: not an element of an
    /// enclosing namespace, not the parameter its owner inherits under the
    /// same name at another position.
    #[test]
    fn a_parameter_inherits_no_namesake() {
        for (name, source, parameter, namesake) in [
            (
                "functions.kerml",
                "package P { datatype R;
                     function rect { in re : R[1]; in im : R[1]; return : R[1]; }
                     function re { in x : R[1]; return : R[1]; } }",
                "P::rect::re",
                "P::re::x",
            ),
            (
                "parts.sysml",
                "package P { part engine { attribute rpm; } calc def power { in engine; } }",
                "P::power::engine",
                "P::engine::rpm",
            ),
            (
                "swapped.sysml",
                "package P { part def P2 { attribute m2; }
                     action def A { in p; in q : P2; }
                     action def Swapped :> A { in q; in p; } }",
                "P::Swapped::q",
                "P::P2::m2",
            ),
        ] {
            let mut r = resolved(name, source);
            let parameter_ref = r.resolve_qualified(parameter).unwrap();
            let namesake_ref = r.resolve_qualified(namesake).unwrap();
            assert!(
                !r.effective_features(parameter_ref, true)
                    .contains(&namesake_ref),
                "{parameter}"
            );
            let member = namesake.rsplit("::").next().unwrap();
            assert_eq!(
                r.resolve_qualified(&format!("{parameter}::{member}")),
                None,
                "{parameter}"
            );
        }
    }

    /// A parameter, a result and an end inherit the members of what their
    /// position pairs them with — through a general that declares its own,
    /// and through one that only inherits them.
    #[test]
    fn a_feature_inherits_the_members_of_what_it_redefines_by_position() {
        let mut r = resolved(
            "positions.sysml",
            "package P {
                 part def P1 { attribute m1; }
                 part def P2 { attribute m2; }
                 action def A { in p : P1; in q : P2; }
                 action def Swapped :> A { in q; in p; }
                 action def Renamed :> A { in x; in y; }
                 action swappedUse : A { in q; in p; }
                 action def Explicit :> A { in y :>> q; in x; }
                 calc def C1 { in i; return r : P1; }
                 calc def C2 :> C1 { return s; }
                 calc def C3 :> C2;
                 calc def C4 :> C3 { return t; }
                 connection def Conn { end e1 : P1; end e2 : P2; }
                 connection def Conn2 :> Conn { end f1; end f2; }
                 connection def Conn3 :> Conn2;
                 connection def Conn4 :> Conn3 { end g1; end g2; }
                 requirement def R { subject sub : P1; }
                 requirement def R2 :> R { subject t; in x; }
             }",
        );
        let m1 = r.resolve_qualified("P::P1::m1").unwrap();
        let m2 = r.resolve_qualified("P::P2::m2").unwrap();
        for (feature, expected) in [
            ("P::Swapped::q", m1),
            ("P::Swapped::p", m2),
            ("P::Renamed::x", m1),
            ("P::Renamed::y", m2),
            ("P::swappedUse::q", m1),
            ("P::swappedUse::p", m2),
            ("P::Explicit::x", m2),
            ("P::Explicit::y", m1),
            ("P::C2::s", m1),
            ("P::C4::t", m1),
            ("P::Conn2::f1", m1),
            ("P::Conn2::f2", m2),
            ("P::Conn4::g1", m1),
            ("P::Conn4::g2", m2),
            ("P::R2::t", m1),
        ] {
            let feature_ref = r.resolve_qualified(feature).unwrap();
            let member = r.element_qualified_name(expected).unwrap();
            let member = member.rsplit("::").next().unwrap();
            assert_eq!(
                r.resolve_qualified(&format!("{feature}::{member}")),
                Some(expected),
                "{feature}::{member}"
            );
            assert!(
                r.effective_features(feature_ref, true).contains(&expected),
                "{feature}"
            );
            assert!(
                !r.effective_features(feature_ref, false).contains(&expected),
                "{feature} inherits through an implied relationship"
            );
        }
        assert_eq!(r.resolve_qualified("P::Swapped::q::m2"), None);
        // A written redefinition keeps its members among the written
        // heritage; the position adds the general's at the same index.
        let y = r.resolve_qualified("P::Explicit::y").unwrap();
        assert!(r.effective_features(y, false).contains(&m2));
    }

    /// A parameter reusing an inherited name at another position shadows
    /// nothing, in lookup as in the inherited view: `Q::b` redefines `A::a`
    /// by position, so `A::b` is still inherited beside it, and a name that
    /// finds both is ambiguous.
    #[test]
    fn a_reused_parameter_name_shadows_nothing_in_lookup() {
        let mut r = resolved(
            "shadow.sysml",
            "package P {
                 action def A { in a; in b; }
                 action def Q :> A { in b; }
                 action def C :> Q, A;
             }",
        );
        let q_b = r.resolve_qualified("P::Q::b").unwrap();
        let a_b = r.resolve_qualified("P::A::b").unwrap();
        let c = r.resolve_qualified("P::C").unwrap();
        assert_eq!(r.resolve_qualified("P::C::b"), None);
        // Ambiguous, not missing: both `b`s are found from `C`'s body.
        let body = *r.b.elem_scope.get(&c.0).unwrap();
        let b = QualifiedName {
            is_global: false,
            segments: vec![Name {
                value: "b".to_string(),
                span: Span::default(),
            }],
            span: Span::default(),
        };
        assert!(matches!(
            r.b.resolve_result(body, &b, 0, false),
            LookupResult::Ambiguous
        ));
        let features = r.effective_features(c, true);
        assert!(features.contains(&q_b) && features.contains(&a_b));
        let names: Vec<String> = r
            .callable_parameters(c)
            .unwrap()
            .into_iter()
            .map(|p| p.name)
            .collect();
        assert_eq!(names, ["b", "b"]);
    }
}
