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

use serde_json::{Map, Value, json};
use std::collections::{HashMap, HashSet};
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
        .into_iter()
        .chain(b.lib_mem_qnames)
        .map(|(id, segments)| (id.to_string(), segments))
        .collect()
}

/// [`library_name_map`] restricted to library *elements* (memberships and
/// aliases excluded) — the safe basis for name→id inversions, where a
/// membership entry would collide with its member's qualified name.
pub fn library_element_name_map(model: &crate::model::Model) -> HashMap<String, Vec<String>> {
    let mut b = Builder::default();
    b.build_model(model);
    b.lib_qnames
        .into_iter()
        .map(|(id, segments)| (id.to_string(), segments))
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
        .map(|&(start, orig)| (start - boundary, model.units()[orig].name.clone()))
        .collect();
    (b.finish(boundary), units)
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
        .map(|&(start, orig)| (start, model.units()[orig].name.clone()))
        .collect();
    (b.finish_range(0, boundary), units)
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
    let units = model.units().iter().filter(|u| u.is_library).count();
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
}

/// Resolve a model and report referential findings instead of JSON.
/// True when any user unit declares a top-level name that also appears as
/// a top-level name of a library unit — the one situation where a library
/// reference's resolution could differ from the library-only world the
/// cache was recorded in. Conservative: any identification on a top-level
/// package, definition, usage, or alias counts.
fn top_level_shadowing(model: &crate::model::Model) -> bool {
    use std::collections::HashSet;
    use sysmlv2_syntax::ast::MemberKind;
    let names_of = |lib: bool| -> HashSet<String> {
        let mut names = HashSet::new();
        for mu in model.units().iter().filter(|u| u.is_library == lib) {
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
    };
    let lib = names_of(true);
    if lib.is_empty() {
        return false;
    }
    !lib.is_disjoint(&names_of(false))
}

pub fn model_resolution_report(model: &crate::model::Model) -> ResolutionReport {
    let mut b = Builder::default();
    b.build_model(model);
    resolution_report_from(&mut b)
}

/// [`model_resolution_report`] over an already-built graph (drains the
/// builder's unresolved list).
pub(crate) fn resolution_report_from(b: &mut Builder) -> ResolutionReport {
    let unresolved = std::mem::take(&mut b.unresolved)
        .into_iter()
        .map(|(elem, qn)| (b.unit_of_elem(elem), qn))
        .collect();
    let ambiguous = std::mem::take(&mut b.ambiguous)
        .into_iter()
        .map(|(elem, qn)| (b.unit_of_elem(elem), qn))
        .collect();
    ResolutionReport {
        unresolved,
        ambiguous,
        unresolved_aliases: b.check_aliases(),
        import_cycles: b.check_import_cycles(),
    }
}

/// Fixed UUIDv5 namespace for this library's deterministic element IDs.
fn id_namespace() -> Uuid {
    Uuid::new_v5(
        &Uuid::NAMESPACE_URL,
        b"https://crates.io/crates/sysmlv2-parser",
    )
}

#[derive(Default)]
pub(crate) struct Builder {
    dialect: Dialect,
    /// Flat element list in ownership (depth-first) order.
    pub(crate) elements: Vec<Elem>,
    scopes: Vec<Scope>,
    /// Element index → its body scope (for namespace-owning elements).
    pub(crate) elem_scope: HashMap<usize, usize>,
    /// Per-scope cache of resolved namespace-import target scopes (with the
    /// recursive flag and the import's bracket-filter indices).
    import_cache: Vec<Option<Vec<ImportedScope>>>,
    /// Import relationships a lookup actually resolved a name through
    /// (admitted hits only) — the unused-import check's evidence.
    pub(crate) used_imports: HashSet<usize>,
    /// Every textual `import` member lowered from a source unit:
    /// (relationship element, whole-member span, spelled `private`).
    pub(crate) user_imports: Vec<(usize, Span, bool)>,
    /// Per-scope cache of resolved specialization-base scopes.
    base_cache: Vec<Option<Vec<usize>>>,
    /// Per-scope visit marks and outcomes for the current name query
    /// ([`Self::lookup`]). `None` under the active stamp means the scope is
    /// currently being evaluated (a cyclic re-entry is a miss); `Some`
    /// memoizes the completed result so multiple import paths can apply
    /// their own filters without re-walking the graph.
    visit_stamp: Vec<[u64; 3]>,
    visit_result: Vec<[Option<LookupResult>; 3]>,
    /// The active lookup query number (one per (start scope, name) chase).
    query_stamp: u64,
    /// Per-import-entry resolution outcomes, keyed by (importing scope,
    /// target spelling): the element each namespace-import entry resolved
    /// to during [`Self::import_scopes`], consumed when the entry's own
    /// `importedNamespace` pending serializes so the reference and the
    /// resolution machinery can never disagree.
    import_targets: HashMap<(usize, String), Option<usize>>,
    /// Library element IDs → qualified-name segments (collected while
    /// assigning normative IDs).
    lib_qnames: Vec<(Uuid, Vec<String>)>,
    /// Library *membership* IDs (`…/owningMembership`, alias Memberships) →
    /// the member's qualified-name segments. Kept separate from
    /// [`Self::lib_qnames`] so name→id inversions (full-form implied
    /// relationships) never collide with the member element; merged into
    /// [`library_name_map`] for lift, which names import targets by id.
    lib_mem_qnames: Vec<(Uuid, Vec<String>)>,
    /// Syntactic effective names of unnamed features (KerML 8.2.3.5 — the
    /// last segment of the first redefined/referenced feature's spelling),
    /// recorded at lowering time so `assign_library_ids` can give
    /// effective-named library members their normative qualified-name IDs
    /// (`ShapeItems::PlanarSurface::shape`) before resolution runs.
    effective_hint: HashMap<usize, String>,
    /// Unresolved references to patch after all scopes exist. A property key
    /// of the form `base#n` appends to the array property `base`.
    pending: Vec<PendingRef>,
    /// Library-cache replay: recorded outcomes for library-origin pending
    /// refs, consumed positionally by `resolve_pending` (see
    /// [`crate::libcache`]).
    lib_hints: Option<std::vec::IntoIter<Option<Uuid>>>,
    /// Sealed-snapshot replay: final library element ids consumed
    /// positionally at element creation, skipping ownership-path
    /// construction and UUIDv5 hashing for the whole library prefix.
    lib_ids_in: Option<std::vec::IntoIter<Uuid>>,
    /// Library-cache recording: outcomes of library-origin pending refs,
    /// collected during `resolve_pending`.
    lib_record: Option<Vec<Option<Uuid>>>,
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
    pub(crate) values: HashMap<usize, (usize, Expr)>,
    /// Elements whose feature value is a `default` (KerML FeatureValue
    /// isDefault): a redefining feature with no value of its own inherits
    /// such an expression, re-evaluated in the redefining context.
    pub(crate) default_values: HashSet<usize>,
    /// Multiplicities for semantic checks: (owning element, scope, clause).
    pub(crate) multiplicities: Vec<(usize, usize, Multiplicity)>,
    /// Connector-family end features with reference targets, for the
    /// featuring-accessibility check: (connector, end feature, target span).
    pub(crate) connector_ends: Vec<(usize, usize, Span)>,
    /// Chain-written subsetting targets (`part m :> a.b;`): (subsetting
    /// feature, scope the chain resolves from, chain links, span) — for
    /// the featuring-accessibility semantic check.
    pub(crate) chain_subsettings: Vec<(usize, usize, Vec<QualifiedName>, Span)>,
    /// Satisfaction claims (`satisfy R by x;`): the SatisfyRequirementUsage
    /// element, the scope it was written in, and the `by` target — the
    /// satisfied requirement itself rides the element's
    /// ReferenceSubsetting. Consumed by [`ResolvedModel::satisfactions`].
    pub(crate) satisfy_by: Vec<(usize, usize, TargetRef)>,
    /// Transition guard expressions, kept as syntax for diagram labels
    /// (the built element tree has no source text): transition element →
    /// (scope, expression).
    pub(crate) transition_guards: HashMap<usize, (usize, Expr)>,
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
    pub(crate) decl_spans: HashMap<usize, Span>,
    /// Full member source extent (keyword through body or terminator) per
    /// member element — the transformation SDK's remove/insert anchor.
    pub(crate) member_spans: HashMap<usize, Span>,
    /// Explicit specialization targets for semantic checks:
    /// (owning element, relationship metaclass, scope, target as written).
    pub(crate) spec_targets: Vec<(usize, &'static str, usize, QualifiedName)>,
    /// Resolution outcome per `spec_targets` index, recorded as the pending
    /// refs resolve — consumers (redefinition conformance) read the target
    /// here instead of re-resolving (`:>>` names self-hit and fall through
    /// to full import scans, ~0.2 ms each on import-heavy scopes).
    pub(crate) spec_resolved: Vec<Option<usize>>,
    /// `spec_targets` index the next created pending ref reports into.
    pending_spec_idx: Option<usize>,
    /// Trailing result expressions for constraint verdicts and calculation
    /// invocation: (owning element, scope the expression resolves from,
    /// expression).
    pub(crate) result_exprs: Vec<(usize, usize, Expr)>,
    /// Named `in`/`inout` parameters per owning element, in declaration
    /// order — the binding targets for user-defined calculation invocation.
    pub(crate) in_params: HashMap<usize, Vec<String>>,
    /// Every named usage member per owning element, in declaration order
    /// with its element index — the binding targets for `new T(…)`
    /// constructor evaluation (filtered to data usages at use).
    pub(crate) ctor_fields: HashMap<usize, Vec<(String, usize)>>,
    /// Return-parameter element per owning element — a calculation written
    /// `return x = expr;` yields its return parameter's bound value (the
    /// evaluator's fallback when there is no trailing result expression).
    pub(crate) return_params: HashMap<usize, usize>,
    /// Direct usage members of enum-definition bodies (enum literals) —
    /// identity-comparable values for the evaluator. (Fidelity gap: these
    /// still lower as ReferenceUsage/FeatureMembership instead of
    /// EnumerationUsage/VariantMembership; tracked in the plan.)
    /// Lazily built element → `spec_targets` indices map (explicit
    /// typing/specialization edges, shared by [`ResolvedModel::
    /// explicit_supertypes`] and the evaluator's classification
    /// operators).
    pub(crate) spec_index: Option<HashMap<usize, Vec<usize>>>,
    /// Lazily built interchange-id → element index map (the inverse of
    /// id assignment) — resolves id-valued relationship properties like
    /// `referencedFeature` without a [`ResolvedModel`] at hand. Rebuilt
    /// when the element count moves (edit sessions append).
    id_index: Option<HashMap<Uuid, usize>>,
    /// First non-library element index (libraries build first) — the
    /// `boundary` of [`Self::build_model`], kept for library-ownership
    /// tests.
    pub(crate) lib_boundary: usize,
    /// Set while building an enum definition's direct body members.
    in_enum_body: bool,
    /// Usage elements with an expected featuring type (owned by a Type via
    /// a FeatureMembership, or a variant of such a variation usage) — the
    /// pilot's `UsageUtil.hasFeaturingType`, which drives `isComposite`
    /// for SysML usages.
    usage_featuring: HashMap<usize, bool>,
    /// Featuring flag for the usage element about to be created (set by
    /// `build_usage_with`/`build_usage_element_scoped`, read by
    /// `build_usage_element` immediately after — never across recursion).
    pending_featuring: bool,
    /// Membership-implied parameter direction for the usage element about
    /// to be created (same lifetime discipline as `pending_featuring`).
    pending_direction: Option<&'static str>,
    /// Metaclass of the owner of the usage element about to be created
    /// (same lifetime discipline) — drives the port-usage composite rule.
    pending_owner_ty: Option<&'static str>,
    /// Per-owner count of `prefixmeta{n}` segments handed out — prefix
    /// metadata and canonicalized bare `@M;` members share one sequence.
    prefix_meta_next: HashMap<usize, usize>,
    /// (first element index, original unit index) per built unit, in build
    /// order — attributes elements back to their source unit.
    unit_starts: Vec<(usize, usize)>,
    /// (first scope index, original unit index) per built unit.
    scope_starts: Vec<(usize, usize)>,
    /// References that stayed unresolved: (element, name as written).
    unresolved: Vec<(usize, QualifiedName)>,
    /// References whose lookup found multiple same-precedence targets.
    ambiguous: Vec<(usize, QualifiedName)>,
    /// Import filter conditions — `filter expr;` members and bracketed
    /// `import P::*[expr]` filters: (scope the expression's names resolve
    /// from, the syntax expression). Applied by [`Self::lookup`] to every
    /// hit that arrives through an import (see [`Self::filter_verdict`]).
    filter_exprs: Vec<(usize, Expr)>,
    /// Per-filter re-entrancy guard: resolving a filter's own metaclass
    /// names may walk back through the filtered import; a re-entered
    /// filter answers *undecided* (member stays visible).
    filters_active: Vec<bool>,
    /// Direct metadata annotations per annotated element: `#M` prefix
    /// metadata and about-less body `@M;` / `metadata m : M;` members
    /// (`@M about x;` annotates `x`, not its owner — not recorded).
    pub(crate) metadata_of: HashMap<usize, Vec<usize>>,
    /// Port definition element → its implicit ConjugatedPortDefinition
    /// (`~P` typings resolve through the original and substitute this).
    conjugated_defs: HashMap<usize, usize>,
    /// Memoized `Metaobjects::SemanticMetadata` element (`Some(None)` =
    /// resolved once, library absent — semantic-metadata implied bases
    /// stay inert).
    semantic_metadata: Option<Option<usize>>,
    /// Membership-import entries currently resolving their own target —
    /// `(scope, index into member_imports)`. A membership import must not
    /// resolve its target through itself (`import vehicle::**;` — the
    /// entry matches `vehicle` and would recurse to the depth guard,
    /// permanently caching an empty `import_scopes` for the scope on the
    /// way down).
    member_import_active: std::collections::HashSet<(usize, usize)>,
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

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct Binding {
    elem: usize,
    sub_scope: Option<usize>,
    /// Visibility of the Membership that contributes this name. KerML's
    /// default membership visibility is public.
    visibility: LookupAccess,
}

/// Visibility admitted by a lookup. The ordering is intentional:
/// public-only < public-or-protected < all memberships.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum LookupAccess {
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

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum LookupResult {
    Missing,
    Found(usize, Option<usize>),
    Ambiguous,
}

impl LookupResult {
    fn option(self) -> Option<(usize, Option<usize>)> {
        match self {
            Self::Found(elem, scope) => Some((elem, scope)),
            Self::Missing | Self::Ambiguous => None,
        }
    }
}

#[derive(Clone, Debug)]
struct NamespaceImport {
    target: QualifiedName,
    recursive: bool,
    is_import_all: bool,
    filters: Vec<usize>,
    relationship: usize,
    /// Effective visibility of the imported membership in this namespace.
    is_public: bool,
}

#[derive(Clone, Debug)]
struct MemberImport {
    target: QualifiedName,
    is_import_all: bool,
    filters: Vec<usize>,
    relationship: usize,
    is_public: bool,
}

/// A scope made visible by a namespace import. `is_import_all` controls
/// whether non-public memberships of the source namespace participate.
#[derive(Clone, Debug, PartialEq, Eq)]
struct ImportedScope {
    scope: usize,
    recursive: bool,
    is_import_all: bool,
    filters: Vec<usize>,
    relationship: usize,
    is_public: bool,
}

/// A reference recorded for the post-pass, once all scopes exist.
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

/// One pending reference paired with cache bookkeeping before resolution is
/// reordered to put specialization outcomes first.
struct PendingWork {
    source_order: usize,
    pending: PendingRef,
    lib_hint: Option<Option<Uuid>>,
    record_pos: Option<usize>,
}

pub(crate) struct Elem {
    pub(crate) ty: &'static str,
    id: Uuid,
    /// Ownership path used to derive `id` and children's ids.
    path: String,
    pub(crate) props: Map<String, Value>,
    pub(crate) owned_relationships: Vec<usize>,
    pub(crate) owning_relationship: Option<usize>,
}

#[derive(Default)]
struct Scope {
    parent: Option<usize>,
    /// The element whose body this scope is (for base-resolution
    /// self-exclusion).
    owner: Option<usize>,
    /// name → all memberships contributing that name. Keeping every
    /// candidate is required both for ambiguity detection and KerML
    /// namespace distinguishability; insertion order must never choose a
    /// semantic target.
    names: HashMap<String, Vec<Binding>>,
    /// Effective names of unnamed features (from their first referenced or
    /// redefined feature). Consulted after `names`, and skipped entirely for
    /// feature-chain steps (which do not resolve lexically).
    effective_names: HashMap<String, Vec<Binding>>,
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
    aliases: Vec<(String, QualifiedName, bool)>,
    /// Implied end-feature names of a binary connector-family usage: its two
    /// ends implicitly redefine `source`/`target` (SysML 8.4.2, the ends of
    /// `Connections::BinaryConnection`), so those names resolve — in the
    /// usage's body — to the usage's own end features. Each entry is
    /// (name, end element, end scope); the end scope bases on the end's
    /// connected feature, so chain members (`source.x`) resolve through it.
    /// Lift names these ends positionally (`implied_end_name`) — the two
    /// must stay in sync or the round-trip gate trips.
    implied_ends: Vec<(&'static str, usize, usize)>,
    /// Specialization/typing targets of the element owning this scope —
    /// members of these resolve as inherited members.
    bases: Vec<QualifiedName>,
    /// Specialization/typing targets written as feature chains — the
    /// chain's last link contributes inherited members exactly like a
    /// plain-name base (`part m :> a.b { attribute :>> x; }` finds `x`
    /// among `b`'s members).
    chain_bases: Vec<Vec<QualifiedName>>,
}

impl Builder {
    fn build(&mut self, unit: &SourceUnit) {
        let root_scope = self.push_scope(None);
        let root = self.new_element("Namespace", None, "$root".to_string());
        for (i, member) in unit.members.iter().enumerate() {
            self.build_member(member, root, root_scope, i);
        }
        self.resolve_pending();
        self.assign_user_ids(0, &[root]);
    }

    /// Build all units of a model into one graph (library units first) and
    /// return the element index where non-library output starts.
    pub(crate) fn build_model(&mut self, model: &crate::model::Model) -> usize {
        match self.build_model_inner(model, false) {
            Ok(boundary) => boundary,
            // Sealed-snapshot validation failed (a lowering change at the
            // same crate version — possible during development). Rebuild
            // cold; the model's slot flips to Record so the next save
            // overwrites the stale cache file.
            Err(()) => {
                *self = Builder::default();
                model.rerecord_library_cache();
                self.build_model_inner(model, true)
                    .expect("cold build cannot fail snapshot validation")
            }
        }
    }

    fn build_model_inner(
        &mut self,
        model: &crate::model::Model,
        no_cache: bool,
    ) -> Result<usize, ()> {
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
        let mut snapshot: Option<crate::libcache::LibraryCache> = None;
        match slot {
            crate::model::LibCacheSlot::Use(cache) if !top_level_shadowing(model) => {
                self.lib_ids_in = Some(cache.lib_ids.clone().into_iter());
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
        }
        if boundary_units == ordered.len() {
            boundary = self.elements.len();
        }
        self.lib_boundary = boundary;

        let lib_names_pending = if let Some(cache) = snapshot {
            let exhausted = self
                .lib_ids_in
                .as_mut()
                .is_none_or(|it| it.next().is_none());
            self.lib_ids_in = None;
            if !exhausted
                || boundary != cache.lib_ids.len()
                || cache.fingerprint != self.lib_pending_fingerprint()
            {
                return Err(());
            }
            self.lib_qnames = cache.lib_qnames;
            self.lib_mem_qnames = cache.lib_mem_qnames;
            self.lib_hints = Some(cache.outcomes.into_iter());
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
        if let Some(outcomes) = self.lib_record.take() {
            model.deposit_recorded(crate::libcache::LibraryCache {
                outcomes,
                fingerprint: lib_fingerprint,
                lib_ids: self.elements[..boundary].iter().map(|e| e.id).collect(),
                lib_qnames: self.lib_qnames.clone(),
                lib_mem_qnames: self.lib_mem_qnames.clone(),
            });
        }
        Ok(boundary)
    }

    /// Order-sensitive hash of the library-origin pending references —
    /// the sequence a [`crate::libcache::LibraryCache`]'s outcomes are
    /// positionally aligned with.
    fn lib_pending_fingerprint(&self) -> u64 {
        let mut h = crate::libcache::Fnv::new();
        for p in &self.pending {
            if p.elem >= self.lib_boundary {
                continue;
            }
            h.update(&(p.elem as u64).to_le_bytes());
            h.update(p.key.as_bytes());
            h.update(p.qn.to_ref_string().as_bytes());
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
        let mut remap: HashMap<String, String> = HashMap::new();
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
            for e in &mut self.elements {
                for v in e.props.values_mut() {
                    patch_ids(v, &remap);
                }
            }
        }
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
        fn target_of(elements: &[Elem], i: usize) -> Option<Uuid> {
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
        remap: &mut HashMap<String, String>,
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

    fn reassign_id(&mut self, e: usize, id: Uuid, remap: &mut HashMap<String, String>) {
        let old = self.elements[e].id;
        if old != id {
            remap.insert(old.to_string(), id.to_string());
            self.elements[e].id = id;
        }
    }

    /// The graph-effective name of an unnamed element (KerML 8.2.3.5):
    /// the first `Redefinition`/`ReferenceSubsetting` target's name in
    /// `ownedRelationship` order, read from the *graph* — a resolved
    /// `{"@id"}` target names through `names`, a hermetic `{"@ref"}`
    /// placeholder carries the name itself (last qualification segment).
    fn graph_effective_name(
        &self,
        e: usize,
        by_id: &HashMap<Uuid, usize>,
        names: &[Option<String>],
    ) -> Option<String> {
        for &r in &self.elements[e].owned_relationships {
            let rel = &self.elements[r];
            let key = match rel.ty {
                "Redefinition" => "redefinedFeature",
                "ReferenceSubsetting" => "referencedFeature",
                _ => continue,
            };
            let target = rel.props.get(key)?;
            if let Some(s) = target.get("@ref").and_then(Value::as_str) {
                return Some(s.rsplit("::").next().unwrap_or(s).to_string());
            }
            let s = target.get("@id").and_then(Value::as_str)?;
            let t = *by_id.get(&Uuid::parse_str(s).ok()?)?;
            return names[t].clone();
        }
        None
    }

    /// Reassign user-element ids to the graph-derived scheme (IDS.md;
    /// id scheme 1): `id(child) = uuid5(id(parent),
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
        // Relationship → owned elements, creation (= array) order.
        let mut owned_by_rel: Vec<Vec<usize>> = vec![Vec::new(); n];
        for (i, e) in self.elements.iter().enumerate() {
            if let Some(r) = e.owning_relationship {
                owned_by_rel[r].push(i);
            }
        }
        // Pre-reassignment id → index, for resolved reference targets.
        let mut by_id: HashMap<Uuid, usize> = HashMap::with_capacity(n);
        for (i, e) in self.elements.iter().enumerate() {
            by_id.insert(e.id, i);
        }
        // Names: declared everywhere; library elements additionally
        // through the effective-name tables; unnamed user elements by
        // the graph-effective fixpoint (`:>>` chains may pass through
        // other effectively named members).
        let mut names: Vec<Option<String>> = (0..n).map(|i| self.effective_name(i)).collect();
        for (id, segs) in self.lib_qnames.iter().chain(self.lib_mem_qnames.iter()) {
            if let Some(&i) = by_id.get(id) {
                if names[i].is_none() {
                    names[i] = segs.last().cloned();
                }
            }
        }
        loop {
            let mut changed = false;
            for e in boundary..n {
                if names[e].is_some() || self.elements[e].ty.ends_with("Membership") {
                    continue;
                }
                if let Some(name) = self.graph_effective_name(e, &by_id, &names) {
                    names[e] = Some(name);
                    changed = true;
                }
            }
            if !changed {
                break;
            }
        }
        // Top-down walk: parents carry their final ids before children
        // derive from them.
        let mut remap: HashMap<String, String> = HashMap::new();
        let mut stack: Vec<usize> = roots.to_vec();
        while let Some(owner) = stack.pop() {
            let owner_id = self.elements[owner].id;
            let rels = self.elements[owner].owned_relationships.clone();
            let mut used: HashSet<String> = HashSet::new();
            for (i, rel) in rels.into_iter().enumerate() {
                let kids = owned_by_rel[rel].clone();
                let membership = self.elements[rel].ty.ends_with("Membership");
                // A single-member membership whose member has an
                // id-name chains **past the membership**:
                // the member takes the owner-scope named segment, and
                // the membership is named by its member — neither
                // references the ordinal, so member insertion cannot
                // disturb named siblings. Owner-scope collisions
                // (duplicate member names, aliases) drop the pair
                // back to the positional chain.
                if membership && kids.len() == 1 {
                    if let Some(name) = &names[kids[0]] {
                        let named = format!("::{}", escape_name(name));
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
                        .and_then(Value::as_str)
                        .or_else(|| props.get("memberShortName").and_then(Value::as_str))
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
                        if let Some(name) = &names[kid] {
                            let named = format!("::{}", escape_name(name));
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
        // Re-point every captured reference (library elements never
        // reference user elements, so the sweep stays in user range).
        for e in &mut self.elements[boundary..] {
            for v in e.props.values_mut() {
                patch_ids(v, &remap);
            }
        }
    }

    fn finish(self, boundary: usize) -> Value {
        let end = self.elements.len();
        self.finish_range(boundary, end)
    }

    fn finish_range(mut self, start: usize, end: usize) -> Value {
        // Materialize relationship arrays as {"@id"} references.
        let ids: Vec<Uuid> = self.elements.iter().map(|e| e.id).collect();
        let mut out = Vec::with_capacity(end - start);
        for elem in &mut self.elements[start..end] {
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
                        .map(|&i| id_ref(ids[i]))
                        .collect(),
                ),
            );
            obj.insert(
                "owningRelationship".into(),
                elem.owning_relationship
                    .map(|i| id_ref(ids[i]))
                    .unwrap_or(Value::Null),
            );
            obj.append(&mut elem.props);
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
        self.visit_stamp.push([0; 3]);
        self.visit_result.push([None; 3]);
        self.scopes.len() - 1
    }

    /// Register an element's declared name and short name in `scope`, with
    /// its body scope `sub_scope`.
    fn register(&mut self, scope: usize, id: &Identification, elem: usize, sub_scope: usize) {
        let visibility = match self.elements[elem]
            .owning_relationship
            .and_then(|r| self.elements[r].props.get("visibility"))
            .and_then(Value::as_str)
        {
            Some("private") => LookupAccess::All,
            Some("protected") => LookupAccess::Protected,
            _ => LookupAccess::Public,
        };
        let binding = Binding {
            elem,
            sub_scope: Some(sub_scope),
            visibility,
        };
        for name in id.name.iter().chain(&id.short_name) {
            self.scopes[scope]
                .names
                .entry(name.value.clone())
                .or_default()
                .push(binding);
        }
        self.elem_scope.insert(elem, sub_scope);
        self.scopes[sub_scope].owner = Some(elem);
    }

    /// Next replayed library element id, when a sealed snapshot is active.
    fn next_lib_id(&mut self) -> Option<Uuid> {
        self.lib_ids_in.as_mut().and_then(|it| it.next())
    }

    fn new_element(&mut self, ty: &'static str, owner_rel: Option<usize>, path: String) -> usize {
        let id = self
            .next_lib_id()
            .unwrap_or_else(|| Uuid::new_v5(&id_namespace(), path.as_bytes()));
        self.elements.push(Elem {
            ty,
            id,
            path,
            props: Map::new(),
            owned_relationships: Vec::new(),
            owning_relationship: owner_rel,
        });
        self.elements.len() - 1
    }

    /// Create a relationship element owned by `owner` (appended to its
    /// `ownedRelationship` list).
    /// The element's `@id` (for check-time id → index maps).
    pub(crate) fn elem_id(&self, i: usize) -> Uuid {
        self.elements[i].id
    }

    fn new_relationship(&mut self, ty: &'static str, owner: usize, path_seg: &str) -> usize {
        let (path, id) = match self.next_lib_id() {
            // Sealed snapshot: paths only feed id derivation, so skip both.
            Some(id) => (String::new(), id),
            None => {
                let path = format!("{}/{}", self.elements[owner].path, path_seg);
                let id = Uuid::new_v5(&id_namespace(), path.as_bytes());
                (path, id)
            }
        };
        self.elements.push(Elem {
            ty,
            id,
            path,
            props: Map::new(),
            owned_relationships: Vec::new(),
            owning_relationship: None,
        });
        let idx = self.elements.len() - 1;
        self.elements[owner].owned_relationships.push(idx);
        // owningRelatedElement is the owned counterpart on the relationship.
        let owner_id = self.elements[owner].id;
        self.elements[idx]
            .props
            .insert("owningRelatedElement".into(), id_ref(owner_id));
        idx
    }

    /// Create an element owned via `rel` (`ownedRelatedElement`).
    fn new_owned_element(&mut self, ty: &'static str, rel: usize, name_seg: &str) -> usize {
        let (path, id) = match self.next_lib_id() {
            // Sealed snapshot: paths only feed id derivation, so skip both.
            Some(id) => (String::new(), id),
            None => {
                let path = format!("{}/{}", self.elements[rel].path, name_seg);
                let id = Uuid::new_v5(&id_namespace(), path.as_bytes());
                (path, id)
            }
        };
        self.elements.push(Elem {
            ty,
            id,
            path,
            props: Map::new(),
            owned_relationships: Vec::new(),
            owning_relationship: Some(rel),
        });
        let idx = self.elements.len() - 1;
        let id_val = id_ref(id);
        let rel_elem = &mut self.elements[rel];
        match rel_elem.props.entry("ownedRelatedElement") {
            serde_json::map::Entry::Occupied(mut e) => {
                if let Value::Array(a) = e.get_mut() {
                    a.push(id_val);
                }
            }
            serde_json::map::Entry::Vacant(e) => {
                e.insert(Value::Array(vec![id_val]));
            }
        }
        idx
    }

    fn set(&mut self, elem: usize, key: &str, value: Value) {
        self.elements[elem].props.insert(key.to_string(), value);
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
        self.set_ref(ft, "type", scope, &TargetRef::Name(m.clone()));
        let e_id = self.elements[e].id;
        self.set(ft, "typedFeature", id_ref(e_id));
        // Recorded like declared typings so the semantic checks (and
        // explicit-supertype walks) see prefix metadata too.
        self.spec_targets
            .push((e, "FeatureTyping", scope, m.clone()));
        self.metadata_of.entry(owner).or_default().push(e);
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
            source.multiplicity = member.leading_then_multiplicity.as_deref().cloned();
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
                self.user_imports.push((
                    rel,
                    member.span,
                    member.visibility == Some(Visibility::Private),
                ));
                let fids = self.record_filters(&imp.filters, scope);
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
                if let Some(name) = &a.id.name {
                    self.scopes[scope].aliases.push((
                        name.value.clone(),
                        a.target.clone(),
                        member.visibility.is_none()
                            || member.visibility == Some(Visibility::Public),
                    ));
                }
            }
            MemberKind::Comment(c) => {
                let rel = self.new_relationship("OwningMembership", owner, &format!("m{index}"));
                self.set(rel, "visibility", Self::visibility_value(member.visibility));
                self.set(rel, "isImplied", json!(false));
                let e = self.new_owned_element("Comment", rel, &format!("comment{index}"));
                self.set_identification(e, &c.id);
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
                let fids = self.record_filters(std::slice::from_ref(expr), scope);
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
                let fids = self.record_filters(&imp.filters, scope);
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
        if matches!(d.kind, DefKind::Occurrence | DefKind::Individual) {
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
            self.scopes[body_scope].bases.push(lib_qn(base));
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
        if matches!(
            u.prefix.direction,
            Some(FeatureDirection::In | FeatureDirection::InOut)
        ) {
            if let Some(n) = &u.declaration.id.name {
                self.in_params
                    .entry(owner)
                    .or_default()
                    .push(n.value.clone());
            }
        }
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
            self.metadata_of.entry(owner).or_default().push(e);
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
        if let Some(cross) = &u.prefix.end_cross {
            let om = self.new_relationship("OwningMembership", e, "crossFeature");
            self.set(om, "isImplied", json!(false));
            self.set(om, "visibility", json!("public"));
            let cf = self.new_owned_element("ReferenceUsage", om, "crossFeature");
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
            self.emit_specializations(cf, &cross.decl, scope);
            if let Some(mult) = &cross.decl.multiplicity {
                self.emit_multiplicity(cf, mult, scope);
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
            self.set(e, "isVariable", json!(u.prefix.is_variable));
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

        let body_scope = self.push_scope(Some(scope));
        self.register(scope, &u.declaration.id.clone(), e, body_scope);
        // Unnamed features take an effective name from the first feature
        // they redefine (KerML 8.2.3.5) or reference (SysML variant/perform/
        // exhibit/… reference forms): `variant manualTransmission;` and
        // `:>> mass = 5;` are findable by those names. Resolution-only —
        // declaredName stays null.
        if u.declaration.id.name.is_none() && u.declaration.id.short_name.is_none() {
            if let Some(name) = effective_ref_name(&u.declaration) {
                self.effective_hint.insert(e, name.clone());
                self.scopes[scope]
                    .effective_names
                    .entry(name)
                    .or_default()
                    .push(Binding {
                        elem: e,
                        sub_scope: Some(body_scope),
                        visibility: match self.elements[rel]
                            .props
                            .get("visibility")
                            .and_then(Value::as_str)
                        {
                            Some("private") => LookupAccess::All,
                            Some("protected") => LookupAccess::Protected,
                            _ => LookupAccess::Public,
                        },
                    });
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
                self.scopes[body_scope].bases.push(lib_qn(base));
            }
        }
        // Implicit parameter redefinition (SysML 8.3): a named directed
        // parameter redefines the same-named parameter of its owner's type.
        // Its own name as a base resolves — with the owner excluded — to
        // that inherited parameter, making its members visible
        // (`focus.image.isWellFocused` with `out item image;`).
        if u.prefix.direction.is_some() {
            if let Some(name) = &u.declaration.id.name {
                self.scopes[body_scope].bases.push(QualifiedName {
                    is_global: false,
                    segments: vec![name.clone()],
                    span: name.span,
                });
            }
        }

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
                self.set_ref(fc, "chainingFeature", scope, &TargetRef::Name(link.clone()));
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

        let end_elems = self.build_usage_detail(e, &detail, scope);

        // A *binary* connector-family usage (exactly two ends): its body
        // additionally bases on the library's binary variant (SysML 8.4.2
        // Table 32 — BinaryConnection/BinaryInterface declare the end
        // features `source`/`target`; the n-ary bases don't), and its own
        // two ends implicitly redefine those ends, so `source`/`target` in
        // the body resolve to the end features themselves. Each end gets a
        // scope basing on its connected feature, so chain members
        // (`flow … from source.x to target.y`) resolve through the ends.
        // The base resolves from the end scope's parent — the owning scope,
        // where the end target itself resolves.
        if matches!(
            u.kind,
            UsageKind::Connection
                | UsageKind::Interface
                | UsageKind::Allocation
                | UsageKind::Connector
        ) && end_elems.len() == 2
        {
            if self.dialect == Dialect::Sysml {
                let binary = match u.kind {
                    UsageKind::Connection => Some("Connections::binaryConnections"),
                    UsageKind::Interface => Some("Interfaces::binaryInterfaces"),
                    _ => None,
                };
                if let Some(base) = binary {
                    self.scopes[body_scope].bases.push(lib_qn(base));
                }
            }
            let UsageDetail::Connector { ends } = &detail else {
                unreachable!()
            };
            for ((name, &end_elem), end) in [("source", &end_elems[0]), ("target", &end_elems[1])]
                .into_iter()
                .zip(ends)
            {
                let end_scope = self.push_scope(Some(scope));
                self.scopes[end_scope].owner = Some(end_elem);
                if let Some(qn) = flat_target_qn(&end.target) {
                    self.scopes[end_scope].bases.push(qn);
                }
                self.elem_scope.insert(end_elem, end_scope);
                self.scopes[body_scope]
                    .implied_ends
                    .push((name, end_elem, end_scope));
            }
        }

        for (i, m) in body_members.into_iter().enumerate() {
            self.build_member(m, e, body_scope, i);
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
            target: TargetRef::Chain(Vec::new()),
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
            self.emit_multiplicity(ru, mult, scope);
        }
        // Empty targets occur for implicit source ends of successions.
        let is_empty = matches!(&end.target, TargetRef::Chain(links) if links.is_empty());
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
                    // owns a FeatureChainMember (plain Membership for a
                    // name, OwningMembership for an owned chain).
                    let fv = self.new_relationship("FeatureValue", ru, "value");
                    self.set(fv, "isImplied", json!(false));
                    let fre = self.new_owned_element("FeatureReferenceExpression", fv, "expr");
                    let m_ty = match by {
                        TargetRef::Chain(links) if links.len() >= 2 => "OwningMembership",
                        _ => "Membership",
                    };
                    let m = self.new_relationship(m_ty, fre, "ref");
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
                    self.transition_guards.insert(e, (t_scope, guard.clone()));
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

    /// Like [`build_usage_element`] but with an explicit pre-created scope
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
                    Literal::Real(r) => (
                        "LiteralRational",
                        r.parse::<f64>()
                            .map(|v| json!(v))
                            .unwrap_or_else(|_| json!(r)),
                    ),
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
                self.operand(e, then_branch, scope, 1);
                self.operand(e, else_branch, scope, 2);
                e
            }
            ExprKind::Binary { op, lhs, rhs } => {
                let e = self.operator_expr(rel, seg, binary_op_str(*op));
                self.operand(e, lhs, scope, 0);
                self.operand(e, rhs, scope, 1);
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
                for (i, a) in args.iter().enumerate() {
                    self.argument(e, a, scope, i, ty);
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
            ExprKind::BodyTerminator => self.new_owned_element("Expression", rel, seg),
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
            self.pending.push(PendingRef {
                elem: rd,
                key: "redefinedFeature".to_string(),
                scope,
                qn: name.clone(),
                exclude: None,
                declared_only: false,
                spec_idx: None,
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
        let pending = std::mem::take(&mut self.pending);
        let mut hints = self.lib_hints.take();
        let mut replay_active = hints.is_some();
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
                        Some(hint) => Some(hint),
                        None => {
                            replay_active = false;
                            None
                        }
                    }
                } else {
                    None
                };
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
            record.resize(lib_pos, None);
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
                    Some(Some(id)) => {
                        let ids = lib_ids.get_or_insert_with(|| {
                            self.elements[..self.lib_boundary]
                                .iter()
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
                                if self.spec_resolved.len() <= si {
                                    self.spec_resolved.resize(si + 1, None);
                                }
                                self.spec_resolved[si] = Some(target);
                            }
                            self.set_pending_value(elem, &key, id_ref(id));
                            continue;
                        }
                        // Unknown target — cache/content skew; fall through
                        // to a full resolve of this entry.
                    }
                    Some(None) => {
                        self.unresolved.push((elem, qn.clone()));
                        let v = json!({ "@ref": qn.to_ref_string() });
                        self.set_pending_value(elem, &key, v);
                        continue;
                    }
                    None => {}
                }
            }
            let (saved, saved_mode) = (self.exclude, self.declared_only);
            self.exclude = exclude;
            // Contextual chain-step resolution first (effective names are
            // legitimate inside the target's scope), then the recorded
            // lexical mode as fallback.
            self.declared_only = false;
            let mut was_ambiguous = false;
            let mut resolved = if key == "importedNamespace" {
                // A namespace import's own target takes the outcome the
                // resolution machinery computed (entry self-excluded); a
                // plain re-resolve here could capture a member through the
                // completed import (`import Domain::*` importing a package
                // that owns a member also named `Domain`).
                self.import_scopes(scope);
                self.import_targets
                    .get(&(scope, qn.to_ref_string()))
                    .copied()
                    .flatten()
            } else {
                self.resolve_chain_member(scope, chain.as_deref(), &qn)
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
                let lexical = match self.resolve_result(scope, &qn, 0, false) {
                    LookupResult::Found(found, _) => Some(found),
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
            // Record the reference site while `resolved` is still the
            // element the name *denotes* (before the serialization
            // substitutions below). Library-internal sites are skipped:
            // the sealed snapshot replays them without reaching this
            // point, and cold/warm builds must record identically.
            if !is_lib_ref {
                if let Some(target) = resolved {
                    let kind = key.split_once('#').map_or(key.as_str(), |(b, _)| b);
                    let unit = self.unit_of_elem(elem);
                    let plain = chain.is_none() && !declared_only && key != "importedNamespace";
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
                    });
                }
                // Interior qualifier segments name ancestor elements
                // (`NominalScenario::TimeStateRecord` — the first segment
                // denotes the attribute def): a rename of those must
                // respell them, so each resolvable proper prefix records
                // its own site even when a later segment makes the whole
                // reference unresolved or ambiguous.
                let unit = self.unit_of_elem(elem);
                for k in 1..qn.segments.len() {
                    let prefix = QualifiedName {
                        is_global: qn.is_global,
                        segments: qn.segments[..k].to_vec(),
                        span: qn.span,
                    };
                    if let Some(t) = self.resolve(scope, &prefix, 0) {
                        self.ref_sites.push(RefSite {
                            unit,
                            span: qn.span,
                            name_span: qn.segments[k - 1].span,
                            target: ElementRef(t),
                            kind: "qualifier".to_string(),
                            scope: ScopeRef(scope),
                            exclude: None,
                            plain: false,
                            owner: ElementRef(elem),
                            chain_root: None,
                        });
                    }
                }
            }
            // `importedMembership` is Membership-typed (KerML 7.2.5.2): a
            // membership import references the resolved member's owning
            // Membership, not the member element itself. (An import through
            // an alias canonicalizes to the target's own membership.)
            if key == "importedMembership" {
                resolved = resolved.map(|t| self.elements[t].owning_relationship.unwrap_or(t));
            }
            // A `~P` typing references P's implicit ConjugatedPortDefinition.
            if self.elements[elem].ty == "ConjugatedPortTyping" && key == "type" {
                resolved = resolved.map(|t| self.conjugated_defs.get(&t).copied().unwrap_or(t));
            }
            let value = match resolved {
                Some(target) => id_ref(self.elements[target].id),
                None => {
                    if was_ambiguous {
                        self.ambiguous.push((elem, qn.clone()));
                    } else {
                        self.unresolved.push((elem, qn.clone()));
                    }
                    json!({ "@ref": qn.to_ref_string() })
                }
            };
            (self.exclude, self.declared_only) = (saved, saved_mode);
            if let Some(si) = spec_idx {
                if self.spec_resolved.len() <= si {
                    self.spec_resolved.resize(si + 1, None);
                }
                self.spec_resolved[si] = resolved;
            }
            if let Some(pos) = record_pos {
                self.lib_record.as_mut().unwrap()[pos] = resolved.map(|t| self.elements[t].id);
            }
            self.set_pending_value(elem, &key, value);
        }
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

    /// Store a resolved (or `@ref`) value under a pending ref's key —
    /// `key#n` spellings append to the `key` array property.
    fn set_pending_value(&mut self, elem: usize, key: &str, value: Value) {
        if let Some((base, _)) = key.split_once('#') {
            let entry = self.elements[elem]
                .props
                .entry(base.to_string())
                .or_insert_with(|| Value::Array(vec![]));
            if let Value::Array(a) = entry {
                a.push(value);
            }
        } else {
            self.set(elem, key, value);
        }
    }

    /// The elements owned by `e` through its owned memberships (any
    /// Membership kind), in declaration order — KerML
    /// `Namespace::ownedMember`. With `features_only`, just the members
    /// owned via FeatureMembership kinds (`Type::ownedFeature`), so a
    /// package answers none. Aliases own no element, so they never
    /// appear; anonymous members do.
    /// Element index for an interchange id string, if any element
    /// carries it (see [`Self::id_index`]).
    pub(crate) fn element_index_of_id(&mut self, id: &str) -> Option<usize> {
        let id: Uuid = id.parse().ok()?;
        let stale = self
            .id_index
            .as_ref()
            .is_none_or(|m| m.len() != self.elements.len());
        if stale {
            self.id_index = Some(
                self.elements
                    .iter()
                    .enumerate()
                    .map(|(i, el)| (el.id, i))
                    .collect(),
            );
        }
        self.id_index.as_ref().unwrap().get(&id).copied()
    }

    pub(crate) fn owned_member_elems(&self, e: usize, features_only: bool) -> Vec<usize> {
        let rels: HashSet<usize> = self.elements[e]
            .owned_relationships
            .iter()
            .copied()
            .filter(|&r| {
                let ty = self.elements[r].ty;
                if features_only {
                    is_feature_membership(ty)
                } else {
                    ty.ends_with("Membership")
                }
            })
            .collect();
        if rels.is_empty() {
            return Vec::new();
        }
        self.elements
            .iter()
            .enumerate()
            .filter(|(_, el)| el.owning_relationship.is_some_and(|r| rels.contains(&r)))
            .map(|(i, _)| i)
            .collect()
    }

    /// Original unit index of the unit that built element `elem`.
    pub(crate) fn unit_of_elem(&self, elem: usize) -> usize {
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
            for (_, qn, _) in self.scopes[s].aliases.clone() {
                if self.resolve(s, &qn, 0).is_none() {
                    out.push((self.unit_of_scope(s), qn));
                }
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
                if let Some(elem) = self.resolve(s, &entry.target, 0) {
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
            for imported in self.import_scopes(s) {
                stack.push(imported.scope);
            }
        }
        false
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
            LookupResult::Found(found, _) => Some(found),
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
            LookupResult::Found(elem, _) => Some(elem),
            LookupResult::Missing | LookupResult::Ambiguous => None,
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
                LookupResult::Found(elem, sub_scope) => {
                    return self.resolve_rest_unrestricted(elem, sub_scope, &qn.segments[1..], 0);
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
            return LookupResult::Found(elem, scope);
        }
        let Some(scope) = scope else {
            return LookupResult::Missing;
        };
        let stamp = self.next_stamp();
        match self.lookup_at(scope, &rest[0].value, depth + 1, stamp, LookupAccess::All) {
            LookupResult::Found(next, next_scope) => {
                self.resolve_rest_unrestricted(next, next_scope, &rest[1..], depth + 1)
            }
            other => other,
        }
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
        if depth > 24 || qn.segments.is_empty() {
            return LookupResult::Missing;
        }
        let first = qn.segments[0].value.clone();
        // `$::` roots resolution at the global namespace (scope 0).
        let mut current = Some(if qn.is_global { 0 } else { scope });
        let stamp = self.next_stamp();
        while let Some(s) = current {
            match self.lookup_at(s, &first, depth, stamp, LookupAccess::All) {
                LookupResult::Found(elem, sub_scope) => {
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
        if depth > 24 {
            return LookupResult::Missing;
        }
        let mode = access as usize;
        if self.visit_stamp[s][mode] == stamp {
            return self.visit_result[s][mode].unwrap_or(LookupResult::Missing);
        }
        self.visit_stamp[s][mode] = stamp;
        self.visit_result[s][mode] = None;
        let hit = self.lookup_body(s, name, depth, stamp, access);
        self.visit_result[s][mode] = Some(hit);
        hit
    }

    fn merge_lookup(&self, left: LookupResult, right: LookupResult) -> LookupResult {
        match (left, right) {
            (LookupResult::Ambiguous, _) | (_, LookupResult::Ambiguous) => LookupResult::Ambiguous,
            (LookupResult::Missing, hit) | (hit, LookupResult::Missing) => hit,
            (LookupResult::Found(a, ascope), LookupResult::Found(b, bscope)) if a == b => {
                LookupResult::Found(a, ascope.or(bscope))
            }
            (LookupResult::Found(a, ascope), LookupResult::Found(b, _))
                if !metaclasses_overlap(self.elements[a].ty, self.elements[b].ty) =>
            {
                // KerML Membership::isDistinguishableFrom: concrete sibling
                // metaclasses with equal names do not make the namespace
                // ambiguous. Context-sensitive selection is a later stage;
                // retain the earlier candidate here for stable traversal.
                LookupResult::Found(a, ascope)
            }
            (LookupResult::Found(..), LookupResult::Found(..)) => LookupResult::Ambiguous,
        }
    }

    /// Distinct same-named hits inherited from different bases are not
    /// ambiguous when one (transitively) redefines another (KerML 8.3.3:
    /// a redefined feature's membership is not inherited alongside its
    /// redefinition) — the redefining feature shadows its target. An
    /// overriding usage `part :>> c : N;` inherits `d` both through the
    /// redefinition target's type (the original) and through `N` (the
    /// override); the override wins.
    fn drop_redefined_hits(&self, hits: &mut Vec<LookupResult>) {
        let mut found: Vec<usize> = hits
            .iter()
            .filter_map(|h| h.option().map(|(e, _)| e))
            .collect();
        found.sort_unstable();
        found.dedup();
        if found.len() < 2 {
            return;
        }
        let mut shadowed: Vec<usize> = Vec::new();
        for &e in &found {
            let mut stack = self.recorded_redefinition_targets(e);
            let mut seen = HashSet::new();
            while let Some(t) = stack.pop() {
                if !seen.insert(t) {
                    continue;
                }
                if found.contains(&t) && !shadowed.contains(&t) {
                    shadowed.push(t);
                }
                stack.extend(self.recorded_redefinition_targets(t));
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
        if remaining.len() > 1 {
            for &x in &remaining {
                if !self.elements[x].ty.ends_with("Usage") {
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
                    if ox != oy && self.recorded_conforms(ox, oy) && !self.recorded_conforms(oy, ox)
                    {
                        shadowed.push(y);
                    }
                }
            }
        }
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

    /// Is `sup` reachable from `sub` through *recorded* explicit
    /// specialization outcomes? Like [`Self::recorded_redefinition_targets`],
    /// a direct scan with no resolution and no index — this runs inside
    /// `lookup_body` (see that method's doc for why both are off-limits).
    fn recorded_conforms(&self, sub: usize, sup: usize) -> bool {
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
    fn recorded_redefinition_targets(&self, e: usize) -> Vec<usize> {
        let mut out = Vec::new();
        for (i, (owner, kind, _, _)) in self.spec_targets.iter().enumerate() {
            if *owner == e && *kind == "Redefinition" {
                if let Some(t) = self.spec_resolved.get(i).copied().flatten() {
                    if t != e && !out.contains(&t) {
                        out.push(t);
                    }
                }
            }
        }
        out
    }

    fn binding_result(
        &self,
        bindings: Option<&Vec<Binding>>,
        access: LookupAccess,
        exclude: Option<usize>,
    ) -> LookupResult {
        let mut result = LookupResult::Missing;
        for binding in bindings.into_iter().flatten().copied() {
            if Some(binding.elem) == exclude || !access.admits(binding.visibility) {
                continue;
            }
            result =
                self.merge_lookup(result, LookupResult::Found(binding.elem, binding.sub_scope));
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
    ) -> LookupResult {
        let direct = self.binding_result(self.scopes[s].names.get(name), access, self.exclude);
        if direct != LookupResult::Missing {
            return direct;
        }
        if !self.declared_only {
            let effective = self.binding_result(
                self.scopes[s].effective_names.get(name),
                access,
                self.exclude,
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
                || (access == LookupAccess::Public && !self.scopes[s].aliases[i].2)
            {
                continue;
            }
            let target = self.scopes[s].aliases[i].1.clone();
            match self.resolve_result(s, &target, depth + 1, false) {
                LookupResult::Found(elem, _) => {
                    aliases = self.merge_lookup(
                        aliases,
                        LookupResult::Found(elem, self.elem_scope.get(&elem).copied()),
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
                implied = self.merge_lookup(implied, LookupResult::Found(elem, Some(sub)));
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
            let resolved = self.resolve_result(s, &entry.target, depth + 1, entry.is_import_all);
            self.member_import_active.remove(&(s, i));
            match resolved {
                LookupResult::Found(elem, _) => {
                    if self.filters_admit(s, &entry.filters, elem, depth) {
                        self.used_imports.insert(entry.relationship);
                        let sub = self.elem_scope.get(&elem).copied();
                        imported_members =
                            self.merge_lookup(imported_members, LookupResult::Found(elem, sub));
                    }
                }
                LookupResult::Ambiguous => imported_members = LookupResult::Ambiguous,
                LookupResult::Missing => {}
            }
        }
        if imported_members != LookupResult::Missing {
            return imported_members;
        }
        let mut hits: Vec<LookupResult> = Vec::new();
        for base in self.base_scopes(s) {
            hits.push(self.lookup_at(base, name, depth + 1, stamp, access.inherited()));
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
        for entry in self.import_scopes(s) {
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
                self.lookup_at(
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
            };
            match hit {
                LookupResult::Found(elem, sub) => {
                    if self.filters_admit(s, &entry.filters, elem, depth) {
                        self.used_imports.insert(entry.relationship);
                        imported = self.merge_lookup(imported, LookupResult::Found(elem, sub));
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
        if depth > 24 {
            return LookupResult::Missing;
        }
        let mut result = self.lookup_at(s, name, depth, stamp, access);
        let mut subs: Vec<usize> = self.scopes[s]
            .names
            .values()
            .flatten()
            .filter(|binding| access.admits(binding.visibility))
            .filter_map(|binding| binding.sub_scope)
            .collect();
        subs.sort_unstable();
        subs.dedup();
        for sub in subs {
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
    fn import_scopes(&mut self, s: usize) -> Vec<ImportedScope> {
        if let Some(cached) = &self.import_cache[s] {
            return cached.clone();
        }
        // Placeholder breaks cycles while computing. An import target may
        // itself be visible only through an earlier import of the same
        // scope (`import P::*; import P_Member::*;`), and resolving it
        // re-enters this scope's cache — so iterate to a fixpoint. Each
        // entry resolves with every *other* entry's current outcome seeded
        // (never its own): `import Domain::*;` where the imported package
        // owns a member also named `Domain` must not capture that member
        // through the import itself on the second pass — the
        // namespace-import analogue of `member_import_active`.
        self.import_cache[s] = Some(Vec::new());
        let imports = self.scopes[s].imports.clone();
        let mut outcomes: Vec<Option<(usize, ImportedScope)>> = vec![None; imports.len()];
        for _ in 0..=imports.len() {
            let mut changed = false;
            for i in 0..imports.len() {
                let entry = imports[i].clone();
                let others: Vec<ImportedScope> = outcomes
                    .iter()
                    .enumerate()
                    .filter(|(j, o)| *j != i && o.is_some())
                    .map(|(_, o)| o.as_ref().unwrap().1.clone())
                    .collect();
                self.import_cache[s] = Some(others);
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
                if next != outcomes[i] {
                    outcomes[i] = next;
                    changed = true;
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
            self.import_targets.insert(key, o.as_ref().map(|(e, _)| *e));
            if let Some((_, scope)) = o {
                if !result.contains(&scope) {
                    result.push(scope);
                }
            }
        }
        self.import_cache[s] = Some(result.clone());
        result
    }

    /// Record import filter expressions and return their indices into
    /// [`Self::filter_exprs`]. `scope` is where the expressions' names
    /// (metaclass references like `Safety`) resolve from.
    fn record_filters(&mut self, filters: &[Expr], scope: usize) -> Vec<usize> {
        filters
            .iter()
            .map(|f| {
                self.filter_exprs.push((scope, f.clone()));
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
        if depth > 24 || self.filters_active[fid] {
            return Tri::Unknown;
        }
        self.filters_active[fid] = true;
        let (scope, expr) = self.filter_exprs[fid].clone();
        let out = self.filter_expr_verdict(&expr, scope, elem, depth);
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
                ty: TargetRef::Name(qn),
            } => self.metadata_test(scope, qn, elem, depth),
            // `(as M).attr` — a boolean attribute of the candidate's `M`
            // metadata annotation.
            ExprKind::ChainStep { target, member } => {
                let ExprKind::Classification {
                    op: ClassificationOp::As,
                    operand: None,
                    ty: TargetRef::Name(meta_qn),
                } = &target.kind
                else {
                    return Tri::Unknown;
                };
                let TargetRef::Name(attr) = member else {
                    return Tri::Unknown;
                };
                if attr.segments.len() != 1 {
                    return Tri::Unknown;
                }
                let attr = attr.segments[0].value.clone();
                self.metadata_attr_verdict(scope, meta_qn, &attr, elem, depth)
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
            return self.metaclass_test(target, elem);
        }
        Tri::False
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
        attr: &str,
        elem: usize,
        depth: usize,
    ) -> Tri {
        let Some(target) = self.resolve(scope, meta_qn, depth + 1) else {
            return Tri::Unknown;
        };
        let metas = self.metadata_of.get(&elem).cloned().unwrap_or_default();
        for m in metas {
            if !self.conforms_upward(m, target) {
                continue;
            }
            // The annotation's `attr` member — declared (`isMandatory =
            // true;`) or redefining (`:>> isMandatory = true;`, findable
            // by its effective name).
            let Some(&ms) = self.elem_scope.get(&m) else {
                return Tri::Unknown;
            };
            let f = self.scopes[ms]
                .names
                .get(attr)
                .or_else(|| self.scopes[ms].effective_names.get(attr))
                .and_then(|bindings| bindings.first())
                .map(|binding| binding.elem);
            let Some(f) = f else {
                return Tri::Unknown;
            };
            return match self.values.get(&f).map(|(_, e)| &e.kind) {
                Some(ExprKind::Literal(Literal::Bool(true))) => Tri::True,
                Some(ExprKind::Literal(Literal::Bool(false))) => Tri::False,
                _ => Tri::Unknown,
            };
        }
        Tri::False
    }

    /// The body scopes of the specialization bases of the element owning
    /// scope `s` (inherited-member resolution). Base names resolve from the
    /// owning scope's parent.
    fn base_scopes(&mut self, s: usize) -> Vec<usize> {
        if let Some(cached) = &self.base_cache[s] {
            return cached.clone();
        }
        self.base_cache[s] = Some(Vec::new());
        let bases = self.scopes[s].bases.clone();
        let chain_bases = self.scopes[s].chain_bases.clone();
        let from = self.scopes[s].parent.unwrap_or(s);
        let mut result = Vec::new();
        // A base name must never resolve to the element being specialized
        // itself (its effective name may equal the base's name).
        let saved = self.exclude;
        self.exclude = self.scopes[s].owner;
        // Fresh depth budget: the cache is permanent, so outcomes must not
        // depend on the first caller's recursion depth (see import_scopes).
        for qn in &bases {
            if let Some(elem) = self.resolve(from, qn, 0) {
                if let Some(&sc) = self.elem_scope.get(&elem) {
                    if sc != s {
                        result.push(sc);
                    }
                }
            }
        }
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
        self.base_cache[s] = Some(result.clone());
        result
    }

    /// The resolved `baseType` targets of the element's SemanticMetadata
    /// annotations: for each annotation whose metadata definition conforms
    /// to `Metaobjects::SemanticMetadata`, resolve the definition's
    /// `baseType` feature value (idiomatically `f meta SysML::Usage` or
    /// `f as SysML::Usage` — the feature reference under the cast) in the
    /// scope that value was written in. Never serialized — consumed by
    /// [`Self::base_scopes`] as implied bases only.
    fn semantic_base_targets(&mut self, elem: usize, depth: usize) -> Vec<usize> {
        if depth > 24 {
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
            return memo;
        }
        let r = self.resolve(0, &lib_qn("Metaobjects::SemanticMetadata"), 0);
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
            let t = match recorded {
                Some(t) => Some(t),
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
    fn ensure_spec_index(&mut self) {
        if self.spec_index.is_none() {
            let mut map: HashMap<usize, Vec<usize>> = HashMap::new();
            for (i, (owner, kind, _, _)) in self.spec_targets.iter().enumerate() {
                if matches!(
                    *kind,
                    "FeatureTyping" | "Subclassification" | "Subsetting" | "Redefinition"
                ) {
                    map.entry(*owner).or_default().push(i);
                }
            }
            self.spec_index = Some(map);
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
                if let Some(t) = self.resolve(scope, &qn, 0) {
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
                if let Some(t) = self.spec_resolved.get(i).copied().flatten() {
                    if t != e && !out.contains(&t) {
                        out.push(t);
                    }
                }
            }
        }
        out
    }

    pub(crate) fn resolve_rest(
        &mut self,
        elem: usize,
        scope: Option<usize>,
        rest: &[Name],
        depth: usize,
    ) -> Option<usize> {
        match self.resolve_rest_result(scope.unwrap_or(0), elem, scope, rest, depth, false) {
            LookupResult::Found(found, _) => Some(found),
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
            return LookupResult::Found(elem, scope);
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
            LookupResult::Found(next, next_scope) => self.resolve_rest_result(
                origin,
                next,
                next_scope,
                &rest[1..],
                depth + 1,
                allow_last_non_public,
            ),
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

fn id_ref(id: Uuid) -> Value {
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

/// Recursively replace remapped `@id` values inside a JSON value.
fn patch_ids(v: &mut Value, remap: &HashMap<String, String>) {
    match v {
        Value::Object(m) => {
            if let Some(Value::String(id)) = m.get_mut("@id") {
                if let Some(new) = remap.get(id.as_str()) {
                    *id = new.clone();
                }
            }
            for x in m.values_mut() {
                patch_ids(x, remap);
            }
        }
        Value::Array(a) => {
            for x in a {
                patch_ids(x, remap);
            }
        }
        _ => {}
    }
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
            ty: TargetRef::Name(qn),
            ..
        } => Some(vec![qn.clone()]),
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
fn effective_ref_name(d: &FeatureDeclaration) -> Option<String> {
    for s in &d.specializations {
        let target = match s {
            FeatureSpecialization::References(t) => Some(t),
            FeatureSpecialization::Redefines(ts) => ts.first(),
            _ => None,
        };
        if let Some(t) = target {
            let qn = match t {
                TargetRef::Name(qn) => qn,
                TargetRef::Chain(links) => links.last()?,
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
        DefKind::Flow => &["Flows::Flow"],
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
        DefKind::Extended | DefKind::Metaclass => &[],
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
        UsageKind::Flow | UsageKind::Message => &["Flows::flows"],
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
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct ElementRef(pub(crate) usize);

/// An opaque handle to one name-resolution scope of a resolved model (a
/// namespace body an expression's references resolve from).
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct ScopeRef(pub(crate) usize);

/// One resolved reference site: a qualified name written in a user unit
/// and the element it resolved to (see [`ResolvedModel::references_to`]).
/// The enabling record for find-usages and rename — a rename must respell
/// the `name_span` text at every site of its element.
#[derive(Clone, Debug)]
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

/// One `satisfy R by x;` claim expanded to the constraint verdicts it
/// implies: every constraint reachable through R's requirement
/// composition, evaluated with R's subjects bound to the satisfaction
/// target (see [`ResolvedModel::satisfactions`]).
pub struct SatisfactionInfo {
    /// The SatisfyRequirementUsage element.
    pub satisfy: ElementRef,
    /// Qualified name of the satisfied requirement — the context label
    /// verdict reports carry.
    pub context: Option<String>,
    /// The constraints the claim implies, ready for verdict evaluation
    /// with [`ResolvedModel::evaluate_in_with`].
    pub constraints: Vec<ConstraintInfo>,
    /// Subject bindings: every subject parameter in the satisfied
    /// requirement's explicit closure → the satisfaction target.
    pub overrides: std::collections::HashMap<usize, crate::eval::Value>,
}

/// A model lowered to the element graph with all names resolved — the
/// entry point for semantic queries and expression evaluation.
pub struct ResolvedModel {
    pub(crate) b: Builder,
    /// Relationship index → owning element, built lazily by
    /// [`Self::element_qualified_name`] (empty until first use).
    rel_owner: Vec<Option<usize>>,
    /// Interchange `@id` → element index, built lazily by the connector /
    /// transition accessors (empty until first use).
    by_id: HashMap<Uuid, usize>,
    /// Per-unit (name, line index), aligned with the model's unit list —
    /// span-to-line conversion for declaration sites (diagram links).
    unit_meta: Vec<(String, sysmlv2_syntax::span::LineIndex)>,
    /// Library scalar-quantity type lookups (by dimension key and by
    /// `mRef` unit definition), built lazily by
    /// [`Self::quantity_type_candidates`] (`None` until first use).
    pub(crate) quantity_index: Option<QuantityIndex>,
}

/// The lazily-built quantity-type index of a resolved model (see
/// `crate::quantity`): scalar quantity types keyed by their dimension
/// and by the unit definitions their `mRef`s name.
pub(crate) struct QuantityIndex {
    pub(crate) by_dims: HashMap<String, Vec<usize>>,
    pub(crate) by_unit_def: HashMap<usize, Vec<usize>>,
}

impl ResolvedModel {
    /// Build the element graph for `model` (libraries included) and resolve
    /// all names.
    pub fn build(model: &crate::model::Model) -> ResolvedModel {
        let mut b = Builder::default();
        b.build_model(model);
        ResolvedModel {
            b,
            rel_owner: Vec::new(),
            by_id: HashMap::new(),
            unit_meta: model
                .units()
                .iter()
                .map(|u| (u.name.clone(), u.lines.clone()))
                .collect(),
            quantity_index: None,
        }
    }

    /// Resolve a `::`-separated qualified name (quoted segments allowed)
    /// from the model's root namespace.
    pub fn resolve_qualified(&mut self, name: &str) -> Option<ElementRef> {
        self.resolve_segments(&split_qualified(name))
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
            LookupResult::Found(elem, _) => Some(ElementRef(elem)),
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
    pub fn element_short_name(&self, e: ElementRef) -> Option<&str> {
        self.b.elements[e.0]
            .props
            .get("declaredShortName")
            .and_then(|v| v.as_str())
    }

    /// The element's declared name, declared short name, or syntactic
    /// effective name inherited from its first redefinition/reference
    /// target (`attribute :>> mass` → `mass`). This is the name lookup and
    /// structural projections use for unnamed features.
    pub fn element_effective_name(&self, e: ElementRef) -> Option<String> {
        self.b
            .effective_name(e.0)
            .or_else(|| self.b.effective_hint.get(&e.0).cloned())
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

    /// Render an evaluated value for display with model context:
    /// element results (enum literals, referenced features) show their
    /// declared (or short) name instead of `Display`'s opaque
    /// `<element>`, recursively through quantities, instances, and
    /// sequences. Everything else matches the value's own `Display`.
    pub fn render_value(&self, v: &crate::eval::Value) -> String {
        use crate::eval::Value;
        match v {
            Value::Element(e) | Value::Unbound(e) => {
                let el = &self.b.elements[e.0];
                el.props
                    .get("declaredName")
                    .or_else(|| el.props.get("declaredShortName"))
                    .and_then(|n| n.as_str())
                    .map(str::to_string)
                    .unwrap_or_else(|| v.to_string())
            }
            Value::Quantity(n, u) => format!("{} [{}]", self.render_value(n), u.display()),
            Value::Instance {
                ty_name, fields, ..
            } => {
                let fields = fields
                    .iter()
                    .map(|(name, v)| format!("{name} = {}", self.render_value(v)))
                    .collect::<Vec<_>>()
                    .join(", ");
                format!("{ty_name}({fields})")
            }
            Value::Sequence(s) if s.is_empty() => v.to_string(),
            Value::Sequence(s) => {
                let items = s
                    .iter()
                    .map(|v| self.render_value(v))
                    .collect::<Vec<_>>()
                    .join(", ");
                format!("({items})")
            }
            _ => v.to_string(),
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

    /// Build the relationship → owning-element map on first use.
    fn ensure_rel_owner(&mut self) {
        if self.rel_owner.len() != self.b.elements.len() {
            let mut map = vec![None; self.b.elements.len()];
            for (i, el) in self.b.elements.iter().enumerate() {
                for &r in &el.owned_relationships {
                    map[r] = Some(i);
                }
            }
            self.rel_owner = map;
        }
    }

    /// The element's qualified name — declared (or short) names joined
    /// with `::` from its document root, restricted names quoted. `None`
    /// when the element or an ancestor is unnamed.
    pub fn element_qualified_name(&mut self, e: ElementRef) -> Option<String> {
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
            let name = el
                .props
                .get("declaredName")
                .and_then(|v| v.as_str())
                .or_else(|| el.props.get("declaredShortName").and_then(|v| v.as_str()))?;
            segs.push(sysmlv2_syntax::ast::escape_name(name));
            cur = self.rel_owner[rel]?;
        }
        if segs.is_empty() {
            return None;
        }
        segs.reverse();
        Some(segs.join("::"))
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
        let candidates: Vec<(usize, Span, usize)> = self
            .b
            .user_imports
            .iter()
            .filter(|(rel, _, private)| *private && !self.b.used_imports.contains(rel))
            .map(|(rel, span, _)| (*rel, *span, self.b.unit_of_elem(*rel)))
            .collect();
        let mut out = Vec::new();
        for (rel, span, unit) in candidates {
            // The import's own target (recorded as a ref site inside the
            // member span). An unresolved target already warns
            // referentially — stay quiet here.
            let Some(target) = self
                .b
                .ref_sites
                .iter()
                .find(|s| {
                    s.unit == unit
                        && s.span.start >= span.start
                        && s.span.end <= span.end
                        && (s.kind == "importedNamespace" || s.kind == "importedMembership")
                })
                .map(|s| s.target)
            else {
                continue;
            };
            let sites: Vec<ElementRef> = self
                .b
                .ref_sites
                .iter()
                .filter(|s| {
                    s.unit == unit && !(s.span.start >= span.start && s.span.end <= span.end)
                })
                .map(|s| s.target)
                .collect();
            let mut feeds = false;
            for site_target in sites {
                if site_target == target {
                    feeds = true;
                    break;
                }
                let mut e = site_target;
                for _ in 0..64 {
                    match self.owner(e) {
                        Some(o) if o == target => {
                            feeds = true;
                            break;
                        }
                        Some(o) => e = o,
                        None => break,
                    }
                }
                if feeds {
                    break;
                }
            }
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
        let mut out = Vec::new();
        let mut frontier = vec![(e, 0usize)];
        while let Some((cur, depth)) = frontier.pop() {
            let props = &self.b.elements[cur.0].props;
            for key in ["declaredName", "declaredShortName"] {
                if let Some(name) = props.get(key).and_then(|v| v.as_str()) {
                    out.push(name.to_string());
                }
            }
            if depth < 8 && out.len() < 4096 {
                for m in self.owned_members(cur) {
                    frontier.push((m, depth + 1));
                }
            }
        }
        out
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

    /// Every element of the given abstract-syntax metaclass (library
    /// elements included — filter with [`Self::is_library_element`]), in
    /// creation (document) order.
    pub fn elements_of_metaclass(&self, ty: &str) -> Vec<ElementRef> {
        (0..self.b.elements.len())
            .filter(|&i| self.b.elements[i].ty == ty)
            .map(ElementRef)
            .collect()
    }

    /// Whether `e` belongs to a loaded library unit (resolution target
    /// only — never serialized, never a transformation target).
    pub fn is_library_element(&self, e: ElementRef) -> bool {
        e.0 < self.b.lib_boundary
    }

    /// Evaluated numeric bounds of `e`'s *explicitly declared*
    /// multiplicity: `[l..u]` → `(l, u)`, `[u]` → `(u, u)` except `[*]`
    /// → `(0, ∞)` — the same reading the multiplicity checks use.
    /// `None` when `e` declares no multiplicity of its own (inherited
    /// ones are not walked) or a bound does not evaluate to a number.
    pub fn declared_multiplicity(&mut self, e: ElementRef) -> Option<(f64, f64)> {
        let (scope, m) = self
            .b
            .multiplicities
            .iter()
            .find(|(o, _, _)| *o == e.0)
            .map(|(_, s, m)| (*s, m.clone()))?;
        let as_num = |v: crate::eval::Value| match v {
            crate::eval::Value::Integer(i) => Some(i as f64),
            crate::eval::Value::Rational(f) => Some(f),
            _ => None,
        };
        let hi = as_num(crate::eval::evaluate_expr_in(&mut self.b, scope, &m.upper).ok()?)?;
        let lo = match &m.lower {
            Some(l) => as_num(crate::eval::evaluate_expr_in(&mut self.b, scope, l).ok()?)?,
            None if hi.is_infinite() => 0.0,
            None => hi,
        };
        Some((lo, hi))
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
    /// spellings). A transformation gate: an edit that was supposed to be
    /// semantics-preserving must not change this.
    pub fn unresolved_count(&self) -> usize {
        self.b.unresolved.len()
    }

    /// Every reference that failed to resolve: the element whose property
    /// carries it, the spelling as written, and the unit it was written
    /// in. Relocation edits (which must not create unresolved references)
    /// diff this list pre/post to name exactly what they broke.
    pub fn unresolved_references(&self) -> Vec<UnresolvedReference> {
        self.b
            .unresolved
            .iter()
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
            .and_then(Value::as_str)
    }

    /// The full source extent of the member declaration that created `e`
    /// (keyword through body or terminator): (unit index, span). `None`
    /// for synthesized elements, document roots, and aliases/imports
    /// (which own no element).
    pub fn member_extent(&self, e: ElementRef) -> Option<(usize, Span)> {
        let span = *self.b.member_spans.get(&e.0)?;
        Some((self.b.unit_of_elem(e.0), span))
    }

    /// Every element built from the user units (libraries excluded), in
    /// creation (document) order.
    pub fn user_elements(&self) -> impl Iterator<Item = ElementRef> + '_ {
        (self.b.lib_boundary..self.b.elements.len()).map(ElementRef)
    }

    /// The element's interchange `@id` (deterministic UUIDv5 — ownership
    /// path, or the normative KerML 9.1 id for library elements).
    pub fn element_id(&self, e: ElementRef) -> uuid::Uuid {
        self.b.elem_id(e.0)
    }

    /// Every constraint/requirement/invariant element carrying its own
    /// trailing result expression, in (unit, source-position) order.
    pub fn constraints(&mut self) -> Vec<ConstraintInfo> {
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
                unit: self.b.unit_of_elem(*owner),
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
        let own: std::collections::HashSet<usize> =
            self.b.result_exprs.iter().map(|(o, _, _)| *o).collect();
        let bodies: HashMap<usize, Expr> = self
            .b
            .result_exprs
            .iter()
            .map(|(o, _, e)| (*o, e.clone()))
            .collect();
        let asserts: Vec<usize> = (0..self.b.elements.len())
            .filter(|&e| {
                matches!(
                    self.b.elements[e].ty,
                    "AssertConstraintUsage" | "SatisfyRequirementUsage" | "Invariant"
                ) && !own.contains(&e)
                    && self.b.lib_boundary <= e
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
            let mut found: Option<(usize, Expr)> = None;
            let mut steps = 0;
            while let Some(t) = queue.pop_front() {
                steps += 1;
                if steps > 256 {
                    break;
                }
                if let Some(expr) = bodies.get(&t) {
                    found = Some((t, expr.clone()));
                    break;
                }
                for s in self.b.explicit_supertype_elems(t) {
                    if seen.insert(s) {
                        queue.push_back(s);
                    }
                }
            }
            let Some((def, expr)) = found else { continue };
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
                unit: self.b.unit_of_elem(def),
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
        let claims = self.b.satisfy_by.clone();
        let mut out = Vec::new();
        for (sat, scope, by) in claims {
            if sat < self.b.lib_boundary {
                continue;
            }
            let Some(req) = self.rel_prop_target(sat, "ReferenceSubsetting", "referencedFeature")
            else {
                continue;
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
            let mut seen: std::collections::HashSet<(usize, usize)> =
                std::collections::HashSet::new();
            let entry_scope = self.b.elem_scope.get(&req).copied().unwrap_or(scope);
            self.collect_satisfaction_constraints(req, entry_scope, &mut seen, &mut constraints, 0);
            constraints.sort_by_key(|c| (c.unit, c.span.start));
            out.push(SatisfactionInfo {
                satisfy: ElementRef(sat),
                context: self.element_qualified_name(ElementRef(req)),
                constraints,
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

    /// Elements owned by `e` through memberships of the given metaclass.
    fn members_under(&self, e: usize, rel_ty: &str) -> Vec<usize> {
        let rels: std::collections::HashSet<usize> = self.b.elements[e]
            .owned_relationships
            .iter()
            .copied()
            .filter(|&r| self.b.elements[r].ty == rel_ty)
            .collect();
        if rels.is_empty() {
            return Vec::new();
        }
        self.b
            .elements
            .iter()
            .enumerate()
            .filter(|(_, el)| el.owning_relationship.is_some_and(|r| rels.contains(&r)))
            .map(|(i, _)| i)
            .collect()
    }

    /// Walk one requirement node for [`Self::satisfactions`]: constraints
    /// on the node and its explicit closure evaluate in `eval_scope` (the
    /// most-derived usage body on the path); nested requirement members
    /// and reference-subsetted requirements recurse with their own body
    /// scope.
    fn collect_satisfaction_constraints(
        &mut self,
        node: usize,
        eval_scope: usize,
        seen: &mut std::collections::HashSet<(usize, usize)>,
        out: &mut Vec<ConstraintInfo>,
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
                            self.collect_satisfaction_constraints(
                                target,
                                m_scope,
                                seen,
                                out,
                                depth + 1,
                            );
                        }
                    }
                    "RequirementUsage" | "SatisfyRequirementUsage" => {
                        let m_scope = self.b.elem_scope.get(&m).copied().unwrap_or(eval_scope);
                        // The nested member's own body (bindings,
                        // redefinitions) is the freshest context for
                        // everything reached through it.
                        self.collect_satisfaction_constraints(m, m_scope, seen, out, depth + 1);
                        if let Some(target) =
                            self.rel_prop_target(m, "ReferenceSubsetting", "referencedFeature")
                        {
                            self.collect_satisfaction_constraints(
                                target,
                                m_scope,
                                seen,
                                out,
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
        let rels: Vec<usize> = self.b.elements[e.0].owned_relationships.clone();
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

    /// The elements a view usage exposes: every member visible through
    /// the view's `expose` imports (recursively for `::**` forms), each
    /// admitted by the view's `filter` conditions — the same
    /// three-valued filter machinery that governs import visibility, so
    /// only a provably-false condition hides a member. Order follows
    /// discovery (per import, declaration order).
    pub fn view_exposed_elements(&mut self, view: ElementRef) -> Vec<ElementRef> {
        let Some(&scope) = self.b.elem_scope.get(&view.0) else {
            return Vec::new();
        };
        let mut out = Vec::new();
        let mut seen = std::collections::HashSet::new();
        // Membership exposes (`expose P::name;`, and the target itself of
        // `expose P::**`) contribute their resolved element directly.
        for entry in self.b.scopes[scope].member_imports.clone() {
            if let Some(elem) = self.b.resolve(scope, &entry.target, 0) {
                if self.b.filters_admit(scope, &entry.filters, elem, 0)
                    && !out.contains(&ElementRef(elem))
                {
                    out.push(ElementRef(elem));
                }
            }
        }
        for entry in self.b.import_scopes(scope) {
            self.collect_exposed(
                scope,
                entry.scope,
                entry.recursive,
                &entry.filters,
                &mut seen,
                &mut out,
            );
        }
        out
    }

    fn collect_exposed(
        &mut self,
        view_scope: usize,
        sc: usize,
        recursive: bool,
        fids: &[usize],
        seen: &mut std::collections::HashSet<usize>,
        out: &mut Vec<ElementRef>,
    ) {
        // The seen-set breaks scope cycles (each scope enumerates once).
        if !seen.insert(sc) {
            return;
        }
        let Some(owner) = self.b.scopes[sc].owner else {
            return;
        };
        for m in self.b.owned_member_elems(owner, false) {
            if !self.b.filters_admit(view_scope, fids, m, 0) {
                continue;
            }
            if !out.contains(&ElementRef(m)) {
                out.push(ElementRef(m));
            }
            if recursive {
                if let Some(&msc) = self.b.elem_scope.get(&m) {
                    self.collect_exposed(view_scope, msc, true, fids, seen, out);
                }
            }
        }
    }

    /// The declared name of the rendering a view usage requests
    /// (`render asInterconnectionDiagram;` → `asInterconnectionDiagram`),
    /// read from the view's ViewRenderingMembership member's reference.
    pub fn view_rendering(&mut self, view: ElementRef) -> Option<String> {
        self.ensure_by_id();
        let m = self
            .members_under(view.0, "ViewRenderingMembership")
            .into_iter()
            .next()?;
        let target = self.rel_prop_target(m, "ReferenceSubsetting", "referencedFeature")?;
        self.b.elements[target]
            .props
            .get("declaredName")
            .and_then(|v| v.as_str())
            .map(str::to_string)
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
    /// expression run under (see [`RefSite::exclude`]).
    pub fn resolve_in_excluding(
        &mut self,
        scope: ScopeRef,
        qn: &QualifiedName,
        exclude: Option<ElementRef>,
    ) -> Option<ElementRef> {
        let saved = self.b.exclude;
        self.b.exclude = exclude.map(|e| e.0);
        let out = self.b.resolve(scope.0, qn, 0);
        self.b.exclude = saved;
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
        if let Some((_, s, expr)) = self.b.result_exprs.iter().find(|(o, _, _)| *o == e.0) {
            return Some((ScopeRef(*s), expr.clone()));
        }
        let ret = self.b.return_params.get(&e.0)?;
        self.b
            .values
            .get(ret)
            .map(|(s, expr)| (ScopeRef(*s), expr.clone()))
    }

    /// Declared `in`/`inout` parameter names, in declaration order.
    pub fn calc_params(&self, e: ElementRef) -> Vec<String> {
        self.b.in_params.get(&e.0).cloned().unwrap_or_default()
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
            let Some(Value::Array(items)) = r.b.elements[e.0].props.get(key) else {
                return Vec::new();
            };
            items
                .iter()
                .filter_map(|v| v.get("@id")?.as_str())
                .filter_map(|s| Uuid::parse_str(s).ok())
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
        let is_variant = |e: usize| {
            self.b.elements[e]
                .owning_relationship
                .map(|r| self.b.elements[r].ty == "VariantMembership")
                .unwrap_or(false)
        };
        let mut out = Vec::new();
        for (&elem, &scope) in &self.b.elem_scope {
            let enum_def = self.b.elements[elem].ty == "EnumerationDefinition";
            // Enum literals and variation variants are both owned via
            // `VariantMembership` since the enum-body metaclass fix.
            let mut lits: Vec<usize> = self.b.scopes[scope]
                .names
                .values()
                .flatten()
                .map(|binding| binding.elem)
                .filter(|&e| is_variant(e))
                .collect();
            lits.sort_unstable();
            lits.dedup();
            if enum_def || !lits.is_empty() {
                out.push((ElementRef(elem), lits.into_iter().map(ElementRef).collect()));
            }
        }
        out.sort_by_key(|(e, _)| e.0);
        out
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
        let rels: Vec<usize> = self.b.elements[e.0]
            .owned_relationships
            .iter()
            .copied()
            .filter(|&r| self.b.elements[r].ty == rel_ty)
            .collect();
        rels.into_iter()
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
        let rels: Vec<usize> = self.b.elements[e.0]
            .owned_relationships
            .iter()
            .copied()
            .filter(|&r| self.b.elements[r].ty == "Annotation")
            .collect();
        rels.into_iter()
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

    /// The metadata annotating `e` — prefix metadata (`#M` / `@M`)
    /// recorded at lowering — in declaration order.
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
        if self.by_id.len() != self.b.elements.len() {
            self.by_id = self
                .b
                .elements
                .iter()
                .enumerate()
                .map(|(i, el)| (el.id, i))
                .collect();
        }
    }

    /// Elements owned *by relationship* `rel` (its `ownedRelatedElement`
    /// children), in creation order.
    fn rel_children(&self, rel: usize) -> Vec<usize> {
        self.b
            .elements
            .iter()
            .enumerate()
            .filter(|(_, el)| el.owning_relationship == Some(rel))
            .map(|(i, _)| i)
            .collect()
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
        self.b.elements[e]
            .props
            .get(key)?
            .get("@id")?
            .as_str()
            .and_then(|s| Uuid::parse_str(s).ok())
            .and_then(|id| self.by_id.get(&id).copied())
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
        let rels: Vec<usize> = self.b.elements[e.0]
            .owned_relationships
            .iter()
            .copied()
            .filter(|&r| self.b.elements[r].ty == "ReferenceSubsetting")
            .collect();
        rels.into_iter()
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
        let rels: Vec<usize> = self.b.elements[e.0]
            .owned_relationships
            .iter()
            .copied()
            .filter(|&r| self.b.elements[r].ty == "StateSubactionMembership")
            .collect();
        rels.into_iter()
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

/// Split `A::'two words'::b` into unquoted segments.
fn split_qualified(name: &str) -> Vec<String> {
    let mut out = Vec::new();
    let mut cur = String::new();
    let mut chars = name.chars().peekable();
    while let Some(c) = chars.next() {
        match c {
            '\'' => {
                while let Some(c) = chars.next() {
                    match c {
                        '\\' => {
                            if let Some(e) = chars.next() {
                                cur.push(e);
                            }
                        }
                        '\'' => break,
                        c => cur.push(c),
                    }
                }
            }
            ':' if chars.peek() == Some(&':') => {
                chars.next();
                out.push(std::mem::take(&mut cur));
            }
            c => cur.push(c),
        }
    }
    out.push(cur);
    out.retain(|s| !s.is_empty());
    out
}
