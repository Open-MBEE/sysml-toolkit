//! Derived properties over the resolved model — the read API for the
//! abstract syntax's `isDerived` properties, answered per element from the
//! model rather than from an emitted payload.
//!
//! One function per property family computes the value the specification
//! defines (KerML/SysML clause 8.3, the `derive…` OCL rules recorded in
//! `spec-refs/derived-properties.json`); [`ResolvedModel::derived`] is the
//! single spec-name entry point over them. The answer is a tri-state so a
//! consumer can tell "not a property of this metaclass" from "a property
//! this toolkit does not compute" from a value — an empty list is only
//! meaningful in the third case.
//!
//! Fidelity is static: [`derives`] says, per metaclass and name, whether a
//! value is exact, a *passthrough* approximation, or not computed at all. A
//! passthrough name is one whose specification reads the inheritance or
//! import closures (`feature = featureMembership.ownedMemberFeature` where
//! `featureMembership` unions `inheritedMembership`); until the closure
//! policy is on, the value covers the owned side only, exactly as the
//! full-form emitter's passthrough conformance level does.
//!
//! Implied relationships (the library specializations every part and
//! action gets from SysML Tables 31/32) are not elements of the model;
//! they are synthesized on demand by the families that list relationships,
//! which this module does not reach yet.

use super::derived_compositions::COMPOSITIONS;
use super::{ElementRef, ResolvedModel};
use crate::metaclass::conforms;
use crate::properties::Atom;
use std::sync::Arc;
use uuid::Uuid;

/// One target of a reference-typed derived property. A property whose
/// type is a reference to an arbitrary element (`type`, `annotatedElement`,
/// `importedElement`, `featureTarget`, a relationship's ends — anything
/// not composed under `ownedElement`/`ownedRelationship`) may point
/// outside the model: at a library element when no library is loaded, at
/// a foreign id, or at a spelling that never resolved. The layer reports
/// such a target rather than dropping it, so a consumer can tell "no
/// value" from "a value it has no element for". The full form spells an
/// `External` id as it is and an `Unresolved` spelling as the dangling id
/// the unresolved-reference policy derives from it.
#[derive(Clone, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub enum Reference {
    /// An element of the model.
    Element(ElementRef),
    /// An element outside the model, by its interchange id.
    External(Uuid),
    /// A reference that did not resolve, by its written spelling.
    Unresolved(String),
}

impl Reference {
    /// The model element, if the reference is one.
    pub fn element(&self) -> Option<ElementRef> {
        match self {
            Self::Element(e) => Some(*e),
            _ => None,
        }
    }
}

/// A derived property's value. The shape is fixed per property name: a
/// property composed under the ownership tree (`ownedFeature`, `owner`,
/// `ownedSpecialization`, …) answers `Element`/`Elements`, whose targets
/// are always model elements; a reference-typed property answers
/// `Reference`/`References` (see [`Reference`]). Non-exhaustive.
#[derive(Clone, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub enum DerivedValue {
    /// The property is single-valued and has no value here (`null`).
    Null,
    Bool(bool),
    Str(String),
    /// A single-valued composition.
    Element(ElementRef),
    /// A multi-valued composition, in the specification's order.
    Elements(Vec<ElementRef>),
    /// A single-valued reference, possibly outside the model.
    Reference(Reference),
    /// A multi-valued reference, in the specification's order, targets
    /// outside the model included.
    References(Vec<Reference>),
    /// A multi-valued string property — the requirement/concern `text`.
    Strings(Vec<String>),
}

impl DerivedValue {
    /// The single model element of a single-valued value, composition or
    /// reference; `None` for `Null`, a target outside the model, or a
    /// multi-valued value.
    pub fn element(&self) -> Option<ElementRef> {
        match self {
            Self::Element(e) => Some(*e),
            Self::Reference(r) => r.element(),
            _ => None,
        }
    }

    /// The model elements of a multi-valued value, composition or
    /// reference, in order — targets outside the model are *omitted*
    /// (match [`Self::References`] to see them). Empty for anything else.
    pub fn elements(&self) -> Vec<ElementRef> {
        match self {
            Self::Elements(es) => es.clone(),
            Self::References(rs) => rs.iter().filter_map(Reference::element).collect(),
            _ => Vec::new(),
        }
    }
}

/// The tri-state answer of [`ResolvedModel::derived`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Derived {
    /// The metaclass does not declare the property (or it is owned, not
    /// derived — read it with the property accessors instead).
    NotDeclared,
    /// Declared, but this toolkit does not compute it yet; the full form
    /// emits the catalog's type-correct empty default for it.
    NotComputed,
    Value(DerivedValue),
}

/// What [`ResolvedModel::derived`] can answer for one (metaclass, name),
/// decided statically.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Derives {
    /// The metaclass does not declare the name as a derived property.
    NotDeclared,
    /// Declared and not computed.
    NotComputed,
    /// Computed under the passthrough level: the specification reads an
    /// inheritance or import closure, and the value covers the owned side
    /// only until the closure policy is on.
    Passthrough,
    /// Computed as specified.
    Exact,
}

/// The names this module computes exactly (sorted; binary-searched).
const EXACT: &[&str] = &[
    "annotatedElement",
    "annotatingElement",
    "annotation",
    "assertedConstraint",
    "association",
    "assumedConstraint",
    "bodyAction",
    "bound",
    "chainingFeature",
    "conjugatedPortDefinition",
    "crossFeature",
    "crossingFeature",
    "definition",
    "differencingType",
    "doAction",
    "documentedElement",
    "effectAction",
    "elseAction",
    "endOwningType",
    "entryAction",
    "enumeratedValue",
    "eventOccurrence",
    "exhibitedState",
    "exitAction",
    "featureChained",
    "featureTarget",
    "featureWithValue",
    "filterCondition",
    "function",
    "guardExpression",
    "ifArgument",
    "importOwningNamespace",
    "importedElement",
    "includedUseCase",
    "individualDefinition",
    "instantiatedType",
    "interaction",
    "intersectingType",
    "isConjugated",
    "isLibraryElement",
    "isReference",
    "loopVariable",
    "lowerBound",
    "memberElementId",
    "membershipOwningNamespace",
    "metaclass",
    "multiplicity",
    "name",
    "originalPortDefinition",
    "ownedAnnotatingElement",
    "ownedAnnotatingRelationship",
    "ownedAnnotation",
    "ownedConjugator",
    "ownedCrossSubsetting",
    "ownedElement",
    "ownedEndFeature",
    "ownedFeature",
    "ownedFeatureInverting",
    "ownedFeatureMembership",
    "ownedImport",
    "ownedMember",
    "ownedMemberElement",
    "ownedMemberElementId",
    "ownedMemberFeature",
    "ownedMemberName",
    "ownedMemberShortName",
    "ownedMembership",
    "ownedPortConjugator",
    "ownedReferenceSubsetting",
    "ownedSpecialization",
    "ownedTypeFeaturing",
    "owner",
    "owningAnnotatedElement",
    "owningAnnotatingElement",
    "owningAnnotatingRelationship",
    "owningClassifier",
    "owningDefinition",
    "owningFeature",
    "owningFeatureMembership",
    "owningFeatureOfType",
    "owningMembership",
    "owningNamespace",
    "owningType",
    "owningUsage",
    "payloadArgument",
    "payloadFeature",
    "payloadType",
    "performedAction",
    "predicate",
    "qualifiedName",
    "receiverArgument",
    "referencedConcern",
    "referencedConstraint",
    "referencedElement",
    "referencedRendering",
    "referencingFeature",
    "referent",
    "relatedElement",
    "representedElement",
    "requiredConstraint",
    "satisfiedRequirement",
    "satisfiedViewpoint",
    "senderArgument",
    "seqArgument",
    "shortName",
    "source",
    "succession",
    "target",
    "targetArgument",
    "terminatedOccurrenceArgument",
    "text",
    "thenAction",
    "triggerAction",
    "type",
    "typeDifferenced",
    "typeIntersected",
    "typeUnioned",
    "unioningType",
    "untilArgument",
    "upperBound",
    "useCaseIncluded",
    "valueExpression",
    "variant",
    "viewCondition",
    "whileArgument",
];

/// The names this module computes at the passthrough level (owned side
/// only; their specification unions the inheritance/import closures).
/// Sorted; binary-searched.
const PASSTHROUGH: &[&str] = &[
    "actorParameter",
    "argument",
    "associationEnd",
    "connectionEnd",
    "connectorEnd",
    "defaultFeaturingType",
    "directedFeature",
    "endFeature",
    "exposedElement",
    "expression",
    "feature",
    "featureMembership",
    "featuringType",
    "framedConcern",
    "importedMembership",
    "inheritedFeature",
    "inheritedMembership",
    "input",
    "interfaceEnd",
    "isModelLevelEvaluable",
    "member",
    "membership",
    "objectiveRequirement",
    "output",
    "parameter",
    "payloadParameter",
    "relatedFeature",
    "relatedType",
    "result",
    "resultExpression",
    "satisfyingFeature",
    "sourceFeature",
    "sourceOutputFeature",
    "sourceType",
    "stakeholderParameter",
    "subjectParameter",
    "targetFeature",
    "targetInputFeature",
    "targetType",
    "verifiedRequirement",
    "viewRendering",
    "viewpointStakeholder",
];

/// Hand-written names that are a *different* property on another
/// metaclass carrying the same name (`Connector::targetFeature` is the
/// related features past the source; `FeatureChainExpression::targetFeature`
/// the accessed feature; `RequirementVerificationMembership::verifiedRequirement`
/// one referenced requirement, a verification case's the list its
/// objective verifies): computed, with the listed fidelity, only where
/// the metaclass conforms to a listed kind.
const HAND_WRITTEN_ON: &[(&str, &str, Derives)] = &[
    ("targetFeature", "Connector", Derives::Passthrough),
    ("targetFeature", "FeatureChainExpression", Derives::Exact),
    (
        "verifiedRequirement",
        "RequirementVerificationMembership",
        Derives::Exact,
    ),
    (
        "verifiedRequirement",
        "VerificationCaseUsage",
        Derives::Passthrough,
    ),
    (
        "verifiedRequirement",
        "VerificationCaseDefinition",
        Derives::Passthrough,
    ),
];

/// Membership-side single references that redefine the owned member
/// under the membership kind's own name (`ownedMemberParameter`,
/// `ownedSubjectParameter`, `ownedConstraint` on a
/// RequirementConstraintMembership, `action` on a
/// StateSubactionMembership, …): exact wherever the element conforms to
/// the listed membership kind, whatever the same name means elsewhere (a
/// composition on the owner, say).
const MEMBER_SIDE: &[(&str, &str)] = &[
    ("action", "StateSubactionMembership"),
    ("condition", "ElementFilterMembership"),
    ("ownedActorParameter", "ActorMembership"),
    ("ownedConcern", "FramedConcernMembership"),
    ("ownedConstraint", "RequirementConstraintMembership"),
    ("ownedMemberParameter", "ParameterMembership"),
    ("ownedObjectiveRequirement", "ObjectiveMembership"),
    ("ownedRendering", "ViewRenderingMembership"),
    ("ownedRequirement", "RequirementVerificationMembership"),
    ("ownedResultExpression", "ResultExpressionMembership"),
    ("ownedStakeholderParameter", "StakeholderMembership"),
    ("ownedSubjectParameter", "SubjectMembership"),
    ("ownedVariantUsage", "VariantMembership"),
    ("transitionFeature", "TransitionFeatureMembership"),
    ("value", "FeatureValue"),
];

/// The membership kind under which `name` is a member-side reference on
/// `metaclass`, if any.
fn member_side(metaclass: &str, name: &str) -> Option<&'static str> {
    MEMBER_SIDE
        .iter()
        .find(|(n, kind)| *n == name && conforms(metaclass, kind))
        .map(|(_, kind)| *kind)
}

/// Whether the concrete metaclass `metaclass` conforms to (is, or
/// specializes) the abstract-syntax metaclass `general` (`"PartUsage"`
/// conforms to `"Usage"`, `"Feature"`, `"Element"`). The generator hook's
/// companion: which declaring metaclass a catalog row's metaclass falls
/// under.
pub fn metaclass_conforms(metaclass: &str, general: &str) -> bool {
    conforms(metaclass, general)
}

/// The shape the interchange schema gives a property (the catalog's
/// default when a value is absent).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub enum PropertyShape {
    /// A list (`[]` when empty).
    Array,
    /// A boolean (`false` by default).
    Boolean,
    /// A nullable single value (`null` by default).
    Nullable,
    /// A string or number the emitter computes.
    Scalar,
    /// An enumeration literal the emitter computes.
    Enumeration,
    /// A required single reference (the emitter's self-reference
    /// placeholder when it has no value).
    RequiredReference,
}

/// One row of the property catalog: a concrete metaclass, a property the
/// schema declares on it, and the property's shape.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CatalogEntry {
    pub metaclass: &'static str,
    pub property: &'static str,
    pub shape: PropertyShape,
    /// Whether the abstract syntax owns the property there (the compact
    /// form may spell it) or derives it (`derived` answers it, at the
    /// fidelity [`derives`] reports).
    pub owned: bool,
}

/// Every (concrete metaclass, property) pair the interchange schema
/// declares, metaclasses and properties sorted — the generator hook: an
/// SDK generator walks this with [`derives`]/[`derives_under`] for the
/// fidelity of each derived row and the value shape of
/// [`DerivedValue`] for its type.
pub fn property_catalog() -> impl Iterator<Item = CatalogEntry> {
    use crate::derived_names::ABSTRACT_METACLASSES;
    crate::schema_props::METACLASS_PROPS
        .iter()
        // The schema carries a few abstract metaclasses; no element has
        // one.
        .filter(|(metaclass, _)| ABSTRACT_METACLASSES.binary_search(metaclass).is_err())
        .flat_map(|(metaclass, props)| {
            props.iter().map(move |(property, code)| CatalogEntry {
                metaclass,
                property,
                // The catalog spells booleans as nullable (`N`); the `B`
                // and `E` codes are defined but unused by this schema.
                shape: match code {
                    b'A' => PropertyShape::Array,
                    b'B' => PropertyShape::Boolean,
                    b'N' => PropertyShape::Nullable,
                    b'S' => PropertyShape::Scalar,
                    b'E' => PropertyShape::Enumeration,
                    b'R' => PropertyShape::RequiredReference,
                    other => unreachable!("catalog shape code {other}"),
                },
                owned: !declared(metaclass, property),
            })
        })
}

/// The deterministic dangling id of an unresolved reference spelling —
/// what the full form spells for a reference that never resolved
/// (`Reference::Unresolved` in the read API), so a consumer can
/// correlate the two.
pub fn dangling_id(spelling: &str) -> String {
    Uuid::new_v5(
        &Uuid::NAMESPACE_OID,
        format!("unresolved:{spelling}").as_bytes(),
    )
    .to_string()
}

/// Owned properties a generated composition may build on: not derived,
/// so never answered by [`ResolvedModel::derived`] themselves, but exact
/// bases (`ownedDisjoining = ownedRelationship->selectByKind(Disjoining)`).
const OWNED_BASES: &[&str] = &["ownedRelationship"];

fn is_exact(name: &str) -> bool {
    EXACT.binary_search(&name).is_ok()
}

fn is_passthrough(name: &str) -> bool {
    PASSTHROUGH.binary_search(&name).is_ok()
}

fn is_hand_written(name: &str) -> bool {
    is_exact(name) || is_passthrough(name)
}

/// The generated kind-filtered composition for `name`, if any.
fn composition(name: &str) -> Option<(&'static str, &'static str, bool)> {
    COMPOSITIONS
        .binary_search_by(|(n, _, _, _)| n.cmp(&name))
        .ok()
        .map(|i| (COMPOSITIONS[i].1, COMPOSITIONS[i].2, COMPOSITIONS[i].3))
}

/// Whether `metaclass` carries the property `name` at all (owned or
/// derived), per the schema catalog.
fn carries(metaclass: &str, name: &str) -> bool {
    use crate::schema_props::METACLASS_PROPS;
    // The catalog and each property list are sorted (pinned by
    // `tests::catalog_is_sorted`), so this is a few string compares per
    // call — it sits on the SDK's per-property hot path.
    METACLASS_PROPS
        .binary_search_by(|(m, _)| m.cmp(&metaclass))
        .ok()
        .is_some_and(|i| {
            METACLASS_PROPS[i]
                .1
                .binary_search_by(|(p, _)| p.cmp(&name))
                .is_ok()
        })
}

/// Whether `name` is a *derived* property of `metaclass` (a concrete
/// metaclass name), per the schema catalog and the XMI's derived-name
/// table.
fn declared(metaclass: &str, name: &str) -> bool {
    use crate::derived_names::{DERIVED_NAMES, OWNED_ON};
    carries(metaclass, name)
        && DERIVED_NAMES.binary_search(&name).is_ok()
        && !OWNED_ON
            .iter()
            .any(|(n, classes)| *n == name && classes.contains(&metaclass))
}

/// The fidelity of a declared `name` on `metaclass`: hand-written names
/// by their list; a composition by its base's fidelity *on the same
/// metaclass* — the same name is a different property on a metaclass
/// that does not carry the base (`action` on StateSubactionMembership is
/// a single required reference, not `usage->selectByKind(ActionUsage)`),
/// and is not computed there. A composition over a passthrough base is
/// passthrough; over an owned base ([`OWNED_BASES`]) exact.
fn fidelity(metaclass: &str, name: &str, depth: usize) -> Derives {
    if member_side(metaclass, name).is_some() {
        return Derives::Exact;
    }
    let gated: Vec<&(&str, &str, Derives)> = HAND_WRITTEN_ON
        .iter()
        .filter(|(n, _, _)| *n == name)
        .collect();
    if !gated.is_empty() {
        return gated
            .iter()
            .find(|(_, kind, _)| conforms(metaclass, kind))
            .map_or(Derives::NotComputed, |(_, _, f)| *f);
    }
    if is_exact(name) {
        Derives::Exact
    } else if is_passthrough(name) {
        Derives::Passthrough
    } else if let Some((base, _, _)) = composition(name) {
        if depth > 8 {
            return Derives::NotComputed;
        }
        if OWNED_BASES.contains(&base) {
            return if carries(metaclass, base) {
                Derives::Exact
            } else {
                Derives::NotComputed
            };
        }
        if !declared(metaclass, base) {
            return Derives::NotComputed;
        }
        match fidelity(metaclass, base, depth + 1) {
            Derives::NotDeclared | Derives::NotComputed => Derives::NotComputed,
            f => f,
        }
    } else {
        Derives::NotComputed
    }
}

/// Whether the abstract syntax declares `name` on `metaclass` as an
/// *owned* (non-derived) property — one the compact form may spell and
/// the property accessors read, which [`ResolvedModel::derived`] never
/// answers (`declaredName`, `isAbstract`, a relationship's `source` and
/// `target`, …). `metaclass` is a concrete metaclass name.
pub fn is_owned_property(metaclass: &str, name: &str) -> bool {
    carries(metaclass, name) && !declared(metaclass, name)
}

/// What [`ResolvedModel::derived`] answers for `name` on an element of
/// `metaclass`, decided without a model, at the passthrough level.
/// `metaclass` is a concrete abstract-syntax metaclass name
/// (`"PartUsage"`). See [`derives_under`] for the closure policy.
pub fn derives(metaclass: &str, name: &str) -> Derives {
    derives_under(metaclass, name, super::ClosurePolicy::Passthrough)
}

/// Passthrough names whose approximation is not the closure and that
/// no policy makes exact: `isModelLevelEvaluable` (the library-function
/// over-approximation), `exposedElement` (the exposed namespaces' own
/// members, not their imported and inherited memberships) and
/// `defaultFeaturingType` (the omitted `specializes` clauses).
const APPROXIMATE: &[&str] = &[
    "defaultFeaturingType",
    "exposedElement",
    "isModelLevelEvaluable",
];

/// [`derives`] under a closure policy: with the closures in force *and
/// the implied heritage included* ([`super::ClosurePolicy::Closure`] with
/// `include_implied: true` — the specification's `inheritedMemberships`
/// does not exclude the implied heritage) every passthrough name but
/// `defaultFeaturingType`, `exposedElement` and `isModelLevelEvaluable`
/// is computed as specified and answers
/// `Exact`; the written-heritage tier (`include_implied: false`) is a
/// documented deviation and stays `Passthrough`.
pub fn derives_under(metaclass: &str, name: &str, policy: super::ClosurePolicy) -> Derives {
    if !declared(metaclass, name) {
        return Derives::NotDeclared;
    }
    match fidelity(metaclass, name, 0) {
        Derives::Passthrough
            if policy.include_implied() == Some(true) && !APPROXIMATE.contains(&name) =>
        {
            Derives::Exact
        }
        f => f,
    }
}

/// Every derived name this module can answer on some metaclass: the
/// hand-written families and every generated composition (each name
/// once). Whether a given metaclass gets a value is [`derives`]'s call.
pub fn computed_names() -> impl Iterator<Item = &'static str> {
    EXACT
        .iter()
        .chain(PASSTHROUGH)
        .copied()
        .chain(
            COMPOSITIONS
                .iter()
                .map(|(n, _, _, _)| *n)
                .filter(|n| !is_hand_written(n)),
        )
        .chain(
            MEMBER_SIDE
                .iter()
                .map(|(n, _)| *n)
                .filter(|n| !is_hand_written(n) && composition(n).is_none()),
        )
}

impl ResolvedModel {
    /// The derived property `name` of `e`, by its specification name
    /// (`"ownedFeature"`, `"owningNamespace"`, …). See [`Derived`] for the
    /// three answers and [`derives`] for the static fidelity of a name.
    pub fn derived(&mut self, e: ElementRef, name: &str) -> Derived {
        let ty = self.b.elements[e.0].ty;
        match self.derives_memo(ty, name) {
            Derives::NotDeclared => return Derived::NotDeclared,
            Derives::NotComputed => return Derived::NotComputed,
            Derives::Passthrough | Derives::Exact => {}
        }
        self.derived_computable(e, name)
    }

    /// [`derives`] for `ty`, memoized per metaclass: the static answer
    /// for every derived name of the catalog is computed once per
    /// metaclass the model exhibits, so a projection that asks for every
    /// name on every element (the full-form emitter) pays the catalog
    /// search once per metaclass rather than once per element — on a
    /// large model that search was the larger part of the emission.
    fn derives_memo(&mut self, ty: &'static str, name: &str) -> Derives {
        use crate::derived_names::DERIVED_NAMES;
        // A name outside the derived catalog is declared nowhere.
        let Ok(idx) = DERIVED_NAMES.binary_search(&name) else {
            return Derives::NotDeclared;
        };
        self.derives_memo
            .entry(ty)
            .or_insert_with(|| DERIVED_NAMES.iter().map(|n| derives(ty, n)).collect())[idx]
    }

    /// The names [`Self::derived`] answers with a value on an element of
    /// `metaclass`: [`computed_names`] filtered by [`derives`] (a
    /// passthrough or exact answer), in the order `computed_names` yields
    /// them, memoized per metaclass; empty for a metaclass outside the
    /// schema catalog. The per-metaclass companion of `computed_names` for
    /// a caller that projects every computed name of an element.
    pub fn computable_names(&mut self, metaclass: &str) -> Arc<[&'static str]> {
        use crate::schema_props::METACLASS_PROPS;
        // The memo is keyed by the catalog's own spelling of the metaclass.
        let Ok(i) = METACLASS_PROPS.binary_search_by(|(m, _)| m.cmp(&metaclass)) else {
            return Arc::from(Vec::new());
        };
        let ty: &'static str = METACLASS_PROPS[i].0;
        if let Some(plan) = self.plan_memo.get(ty) {
            return Arc::clone(plan);
        }
        let plan: Arc<[&'static str]> = computed_names()
            .filter(|n| {
                matches!(
                    self.derives_memo(ty, n),
                    Derives::Passthrough | Derives::Exact
                )
            })
            .collect();
        self.plan_memo.insert(ty, Arc::clone(&plan));
        plan
    }

    /// [`Self::derived`] for a `name` the static gate has already admitted
    /// on `e`'s metaclass (one of [`Self::computable_names`]); the gate is
    /// not repeated. For a name the gate would refuse this may answer a
    /// value the metaclass does not declare, or panic on a name with no
    /// arm, so callers hold the invariant.
    pub(crate) fn derived_computable(&mut self, e: ElementRef, name: &str) -> Derived {
        let ty = self.b.elements[e.0].ty;
        use DerivedValue as V;
        // A membership-side reference: the owned member.
        if member_side(ty, name).is_some() {
            return Derived::Value(opt(self.d_owned_member_element(e)));
        }
        // A generated composition — unless the name is hand-written, which
        // wins (`ownedMembership` is spelled as a composition over the
        // owned relationships but computed directly): the base's list
        // filtered by kind.
        if let Some((base, kind, single)) = composition(name).filter(|_| !is_hand_written(name)) {
            // A composition keeps its base's shape; over a reference-typed
            // base, a target outside the model passes the kind filter as
            // it is (see [`ResolvedModel::cast`]).
            let (items, by_reference): (Vec<Reference>, bool) = if OWNED_BASES.contains(&base) {
                // The only owned base today is `ownedRelationship`, implied
                // relationships included.
                let rels = self.d_owned_relationships(e);
                (rels.into_iter().map(Reference::Element).collect(), false)
            } else {
                match self.derived(e, base) {
                    Derived::Value(V::Elements(items)) => {
                        (items.into_iter().map(Reference::Element).collect(), false)
                    }
                    Derived::Value(V::Element(x)) => (vec![Reference::Element(x)], false),
                    Derived::Value(V::References(items)) => (items, true),
                    Derived::Value(V::Reference(r)) => (vec![r], true),
                    Derived::Value(V::Null) => (Vec::new(), by_reference_base(base)),
                    _ => return Derived::NotComputed,
                }
            };
            let mut kept = items.into_iter().filter_map(|r| self.cast(r, kind));
            return Derived::Value(match (single, by_reference) {
                (true, false) => opt(kept.next().and_then(|r| r.element())),
                (true, true) => opt_ref(kept.next()),
                (false, false) => V::Elements(kept.filter_map(|r| r.element()).collect()),
                (false, true) => V::References(kept.collect()),
            });
        }
        let v = match name {
            "owner" => opt(self.d_owner(e)),
            "owningMembership" => opt(self.d_owning_membership(e)),
            "owningNamespace" => opt(self.d_owning_namespace(e)),
            "ownedElement" => V::Elements(self.d_owned_elements(e)),
            "isLibraryElement" => V::Bool(self.d_is_library_element(e)),
            "ownedMembership" => V::Elements(self.d_owned_memberships(e)),
            "membership" => V::Elements(self.d_memberships(e)),
            "ownedMember" => V::Elements(self.d_owned_members(e)),
            "member" => V::References(self.d_members(e)),
            "ownedImport" => V::Elements(self.d_owned_imports(e)),
            "ownedFeatureMembership" => V::Elements(self.d_owned_feature_memberships(e)),
            "featureMembership" => V::Elements(self.d_feature_memberships(e)),
            "ownedFeature" => V::Elements(self.d_owned_features(e)),
            "feature" => V::Elements(self.d_features(e)),
            // ---- the closures (`json/closures.rs`) ----
            "inheritedMembership" => V::Elements(self.d_inherited_memberships(e)),
            "inheritedFeature" => V::Elements(self.d_inherited_features(e)),
            "importedMembership" => V::Elements(self.imported_memberships(e)),
            "featuringType" => V::Elements(self.d_featuring_types(e)),
            "owningType" => opt(self.d_owning_type_any(e)),
            "owningClassifier" => opt(self
                .d_relationship_owning_type(e)
                .filter(|&o| self.is_kind(o, "Classifier"))),
            "owningFeature" => opt(self
                .d_relationship_owning_type(e)
                .filter(|&o| self.is_kind(o, "Feature"))),
            "owningFeatureOfType" => opt(self
                .d_relationship_owning_type(e)
                .filter(|&o| self.is_kind(o, "Feature"))),
            "owningFeatureMembership" => opt(self.d_owning_feature_membership(e)),
            "endOwningType" => opt(self.d_end_owning_type(e)),
            "owningDefinition" => opt(self
                .d_owning_type(e)
                .filter(|&o| self.is_kind(o, "Definition"))),
            "owningUsage" => opt(self.d_owning_type(e).filter(|&o| self.is_kind(o, "Usage"))),
            "membershipOwningNamespace" | "importOwningNamespace" => {
                opt(self.d_owning_related_element(e))
            }
            "ownedMemberElement" | "ownedMemberFeature" => opt(self.d_owned_member_element(e)),
            "importedElement" => opt_ref(self.d_imported_element(e)),
            "isReference" => self.d_is_reference(e).map_or(V::Null, V::Bool),
            "name" => self.element_effective_name(e).map_or(V::Null, V::Str),
            "shortName" => self.element_short_name(e).map_or(V::Null, V::Str),
            "qualifiedName" => self.element_qualified_name(e).map_or(V::Null, V::Str),
            "text" => V::Strings(self.d_text(e)),
            "multiplicity" => opt(self.d_multiplicity(e)),
            "ownedConjugator" => opt(self
                .owned_relationships_of_kind(e, "Conjugation")
                .into_iter()
                .next()),
            "annotation" => V::Elements(self.d_annotations(e)),
            "ownedAnnotatingRelationship" => V::Elements(self.d_owned_annotations(e, false)),
            "ownedAnnotation" => V::Elements(self.d_owned_annotations(e, true)),
            // `annotatedElement` is owned on Annotation itself; derived
            // only on the annotating element.
            "annotatedElement" => V::References(self.d_annotating_targets(e)),
            "documentedElement" | "representedElement" => {
                opt_ref(self.d_annotating_targets(e).into_iter().next())
            }
            "annotatingElement" => opt(self.d_annotating_element(e)),
            "ownedAnnotatingElement" => opt(self.d_owned_annotating_element(e)),
            "owningAnnotatingElement" => opt(self
                .d_owning_related_element(e)
                .filter(|_| self.d_owned_annotating_element(e).is_none())
                .filter(|&o| self.is_kind(o, "AnnotatingElement"))),
            // `owningAnnotatedElement subsets annotatedElement`: the owner
            // only when it *is* the annotated element.
            "owningAnnotatedElement" => {
                let owner = self.d_owning_related_element(e);
                opt(owner.filter(|&o| self.d_annotated_element(e) == Some(Reference::Element(o))))
            }
            "owningAnnotatingRelationship" => opt(self.b.elements[e.0]
                .owning_relationship
                .map(ElementRef)
                .filter(|&r| self.b.elements[r.0].ty == "Annotation")),
            "type" => V::References(self.d_types(e)),
            "definition" => V::References(self.d_types_of_kind(e, "Classifier")),
            // ---- states, transitions, actions (`json/behavior.rs`) ----
            "entryAction" => opt(self.d_state_subaction(e, "entry")),
            "doAction" => opt(self.d_state_subaction(e, "do")),
            "exitAction" => opt(self.d_state_subaction(e, "exit")),
            "triggerAction" => {
                V::Elements(self.d_transition_features(e, "trigger", "AcceptActionUsage"))
            }
            "guardExpression" => V::Elements(self.d_transition_features(e, "guard", "Expression")),
            "effectAction" => V::Elements(self.d_transition_features(e, "effect", "ActionUsage")),
            "succession" => opt(self.d_succession(e)),
            "source" => opt_ref(self.d_transition_source(e)),
            "target" => opt_ref(self.d_transition_target(e)),
            "loopVariable" => opt(self.d_loop_variable(e)),
            "ifArgument" | "whileArgument" => opt(self.d_parameter_as(e, 1, "Expression")),
            "thenAction" | "bodyAction" => opt(self.d_parameter_as(e, 2, "ActionUsage")),
            "elseAction" => opt(self.d_parameter_as(e, 3, "ActionUsage")),
            "untilArgument" => opt(self.d_parameter_as(e, 3, "Expression")),
            "payloadArgument" if ty == "AcceptActionUsage" => {
                opt(self.d_accept_payload_argument(e))
            }
            "seqArgument"
            | "targetArgument"
            | "terminatedOccurrenceArgument"
            | "payloadArgument" => opt(self.d_argument(e, 1)),
            "valueExpression" | "senderArgument" => opt(self.d_argument(e, 2)),
            "receiverArgument" => {
                let position = if ty == "SendActionUsage" { 3 } else { 2 };
                opt(self.d_argument(e, position))
            }
            "payloadParameter" => {
                let features = self.d_features(e);
                opt(self.d_directed(features, None).into_iter().next())
            }
            "eventOccurrence" => opt_ref(self.d_referenced_or_self(e, "OccurrenceUsage")),
            "performedAction" => opt_ref(self.d_referenced_or_self(e, "ActionUsage")),
            "exhibitedState" => opt_ref(self.d_referenced_or_self(e, "StateUsage")),
            "useCaseIncluded" => opt_ref(self.d_referenced_or_self(e, "UseCaseUsage")),
            "assertedConstraint" => opt_ref(self.d_referenced_or_self(e, "ConstraintUsage")),
            "satisfiedRequirement" => opt_ref(self.d_referenced_or_self(e, "RequirementUsage")),
            "includedUseCase" => V::References(self.d_included_use_cases(e)),
            // ---- expressions and functions ----
            "result" => opt(self.d_result(e)),
            "function" => opt_ref(self.d_types_of_kind(e, "Function").into_iter().next()),
            "predicate" => opt_ref(self.d_types_of_kind(e, "Predicate").into_iter().next()),
            "metaclass" => opt_ref(self.d_types_of_kind(e, "Metaclass").into_iter().next()),
            "association" => V::References(self.d_types_of_kind(e, "Association")),
            "interaction" => V::References(self.d_types_of_kind(e, "Interaction")),
            "payloadFeature" => opt(self.d_payload_feature(e)),
            "payloadType" => V::References(self.d_payload_type(e)),
            "individualDefinition" => opt_ref(self.d_individual_definition(e)),
            "instantiatedType" => opt_ref(self.d_instantiated_type(e)),
            "argument" => V::References(self.d_arguments(e)),
            "referent" if ty == "AssignmentActionUsage" => {
                opt_ref(self.d_unowned_member(e, "Feature"))
            }
            "referent" => opt_ref(self.d_referent(e)),
            "targetFeature" if ty == "FeatureChainExpression" => opt_ref(self.d_referent(e)),
            "referencedElement" => opt_ref(self.d_unowned_member(e, "Element")),
            "expression" => V::Elements(self.d_function_expressions(e)),
            "featureWithValue" => opt(self.d_owning_related_element(e)),
            "bound" => V::Elements(self.d_bounds(e)),
            "lowerBound" => {
                let bounds = self.d_bounds(e);
                opt((bounds.len() >= 2).then(|| bounds[0]))
            }
            "upperBound" => opt(self.d_bounds(e).into_iter().last()),
            "filterCondition" | "viewCondition" => V::Elements(self.d_filter_conditions(e)),
            "memberElementId" | "ownedMemberElementId" => {
                self.d_member_element_id(e).map_or(V::Null, V::Str)
            }
            "ownedMemberName" => self.d_owned_member_name(e, false).map_or(V::Null, V::Str),
            "ownedMemberShortName" => self.d_owned_member_name(e, true).map_or(V::Null, V::Str),
            "enumeratedValue" => V::Elements(self.d_variants(e)),
            "isConjugated" => V::Bool(
                !self
                    .owned_relationships_of_kind(e, "Conjugation")
                    .is_empty(),
            ),
            "conjugatedPortDefinition" => opt(self.d_conjugated_port_definition(e)),
            "ownedPortConjugator" => opt(self
                .owned_relationships_of_kind(e, "PortConjugation")
                .into_iter()
                .next()),
            "parameter" => {
                let features = self.d_features(e);
                V::Elements(self.d_directed(features, None))
            }
            "associationEnd" | "connectionEnd" | "interfaceEnd" => {
                let features = self.d_features(e);
                V::Elements(self.d_ends(features))
            }
            // ---- requirements, cases, views (`json/cases.rs`) ----
            "subjectParameter" => opt(self
                .d_members_via(e, "SubjectMembership")
                .into_iter()
                .next()),
            "actorParameter" => V::Elements(self.d_members_via(e, "ActorMembership")),
            "stakeholderParameter" => V::Elements(self.d_members_via(e, "StakeholderMembership")),
            "objectiveRequirement" => opt(self
                .d_members_via(e, "ObjectiveMembership")
                .into_iter()
                .next()),
            "framedConcern" => V::Elements(self.d_members_via(e, "FramedConcernMembership")),
            "resultExpression" => opt(self
                .d_members_via(e, "ResultExpressionMembership")
                .into_iter()
                .next()),
            "requiredConstraint" => V::Elements(self.d_requirement_constraints(e, "requirement")),
            "assumedConstraint" => V::Elements(self.d_requirement_constraints(e, "assumption")),
            "referencedConstraint" => opt_ref(self.d_referenced_member(e, "ConstraintUsage")),
            "referencedConcern" => opt_ref(self.d_referenced_member(e, "ConcernUsage")),
            "verifiedRequirement" if ty == "RequirementVerificationMembership" => {
                opt_ref(self.d_referenced_member(e, "RequirementUsage"))
            }
            "verifiedRequirement" => V::References(self.d_verified_requirements(e)),
            "referencedRendering" => opt_ref(self.d_referenced_member(e, "RenderingUsage")),
            "viewRendering" => opt_ref(self.d_view_rendering(e)),
            "satisfyingFeature" => opt_ref(self.d_satisfying_feature(e)),
            "satisfiedViewpoint" => V::Elements(self.d_satisfied_viewpoints(e)),
            "viewpointStakeholder" => V::Elements(self.d_viewpoint_stakeholders(e)),
            "exposedElement" => V::Elements(self.d_exposed_elements(e)),
            "featureTarget" => V::Reference(self.d_feature_target(e)),
            "chainingFeature" => V::References(self.d_chaining_features(e)),
            "crossFeature" => opt_ref(self.d_cross_feature(e)),
            "featureChained" | "referencingFeature" | "crossingFeature" | "typeUnioned"
            | "typeIntersected" | "typeDifferenced" => opt(self.d_owning_related_element(e)),
            // ---- type operations and evaluability (`json/typeops.rs`) ----
            "unioningType" => V::References(self.d_operation_types(e, "Unioning", "unioningType")),
            "intersectingType" => {
                V::References(self.d_operation_types(e, "Intersecting", "intersectingType"))
            }
            "differencingType" => {
                V::References(self.d_operation_types(e, "Differencing", "differencingType"))
            }
            "relatedType" => V::References(self.d_related_types(e)),
            "sourceType" => opt_ref(self.d_related_types(e).into_iter().next()),
            "targetType" => V::References(self.d_target_types(e)),
            "defaultFeaturingType" => opt(self.d_default_featuring_type(e)),
            "isModelLevelEvaluable" if self.is_kind(e, "Function") => {
                V::Bool(self.function_is_model_level_evaluable(&Reference::Element(e)))
            }
            "isModelLevelEvaluable" => V::Bool(self.d_is_model_level_evaluable(e)),
            "ownedSpecialization" => V::Elements(self.d_owned_specializations(e, "Specialization")),
            "ownedFeatureInverting" => {
                V::Elements(self.d_owned_specializations(e, "FeatureInverting"))
            }
            "ownedTypeFeaturing" => V::Elements(self.d_owned_specializations(e, "TypeFeaturing")),
            "ownedReferenceSubsetting" => opt(self
                .d_owned_specializations(e, "ReferenceSubsetting")
                .into_iter()
                .next()),
            "ownedCrossSubsetting" => opt(self
                .d_owned_specializations(e, "CrossSubsetting")
                .into_iter()
                .next()),
            "relatedElement" => {
                let (mut source, target) = self.relationship_ends(e);
                source.extend(target);
                V::References(source)
            }
            "ownedEndFeature" => V::Elements(self.d_ends(self.d_owned_features(e))),
            "endFeature" | "connectorEnd" => {
                let features = self.d_features(e);
                V::Elements(self.d_ends(features))
            }
            "relatedFeature" => V::References(self.d_related_features(e)),
            "sourceFeature" => opt_ref(self.d_related_features(e).into_iter().next()),
            "targetFeature" => {
                V::References(self.d_related_features(e).into_iter().skip(1).collect())
            }
            "sourceOutputFeature" => opt(self.d_flow_end_feature(e, 0)),
            "targetInputFeature" => opt(self.d_flow_end_feature(e, 1)),
            "directedFeature" => {
                let features = self.d_features(e);
                V::Elements(self.d_directed(features, None))
            }
            "input" => {
                let features = self.d_features(e);
                V::Elements(self.d_directed(features, Some(true)))
            }
            "output" => {
                let features = self.d_features(e);
                V::Elements(self.d_directed(features, Some(false)))
            }
            "variant" => V::Elements(self.d_variants(e)),
            "originalPortDefinition" => opt(self
                .d_owning_namespace(e)
                .filter(|&n| self.is_kind(n, "PortDefinition"))),
            _ => unreachable!("{name} is listed as computed but has no arm"),
        };
        Derived::Value(v)
    }

    pub(super) fn is_kind(&self, e: ElementRef, general: &str) -> bool {
        conforms(self.b.elements[e.0].ty, general)
    }

    // ---- Element ----

    /// `Element::isLibraryElement = libraryNamespace() <> null`: an
    /// element is a library element when a library package owns it,
    /// directly or transitively — whichever unit it was read from.
    /// (Compare [`Self::is_library_element`], which answers whether the
    /// element came from a library *unit*.)
    fn d_is_library_element(&mut self, e: ElementRef) -> bool {
        self.ensure_rel_owner();
        let mut at = Some(e.0);
        let mut steps = 0usize;
        while let Some(i) = at {
            if self.b.elements[i].ty == "LibraryPackage" {
                return true;
            }
            steps += 1;
            if steps > 2 * self.b.elements.len() {
                return false; // malformed ownership cycle
            }
            // Up one step, through relationship nodes: a relationship's
            // carrier (`owningRelatedElement`), else its own owning
            // relationship, as `Relationship::libraryNamespace()` walks.
            at = self.rel_owner[i].or(self.b.elements[i].owning_relationship);
        }
        false
    }

    /// `Element::owner = owningRelationship.owningRelatedElement`. A
    /// relationship owned directly by its related element has no owning
    /// relationship and therefore no owner (its carrier is
    /// `owningRelatedElement`); the navigation accessor
    /// [`Self::owner`] answers the carrier instead.
    fn d_owner(&mut self, e: ElementRef) -> Option<ElementRef> {
        let rel = self.b.elements[e.0].owning_relationship?;
        self.d_owning_related_element(ElementRef(rel))
    }

    /// `Relationship::owningRelatedElement` — the element whose
    /// `ownedRelationship` list carries `rel`.
    pub(super) fn d_owning_related_element(&mut self, rel: ElementRef) -> Option<ElementRef> {
        self.ensure_rel_owner();
        self.rel_owner[rel.0].map(ElementRef)
    }

    /// `Element::owningMembership` — the owning relationship when it is a
    /// Membership (in a well-formed model always an OwningMembership; the
    /// looser filter keeps a foreign payload's shape visible).
    fn d_owning_membership(&self, e: ElementRef) -> Option<ElementRef> {
        let rel = self.b.elements[e.0].owning_relationship?;
        conforms(self.b.elements[rel].ty, "Membership").then_some(ElementRef(rel))
    }

    /// `Element::owningNamespace = owningMembership.membershipOwningNamespace`.
    fn d_owning_namespace(&mut self, e: ElementRef) -> Option<ElementRef> {
        let m = self.d_owning_membership(e)?;
        self.d_owning_related_element(m)
    }

    /// `Element::ownedElement = ownedRelationship.ownedRelatedElement`, in
    /// relationship order then related-element order.
    fn d_owned_elements(&self, e: ElementRef) -> Vec<ElementRef> {
        self.b.elements[e.0]
            .owned_relationships
            .iter()
            .flat_map(|&r| self.b.elements[r].children.iter().copied())
            .map(ElementRef)
            .collect()
    }

    // ---- Namespace ----

    pub(super) fn owned_relationships_of_kind(
        &self,
        e: ElementRef,
        general: &str,
    ) -> Vec<ElementRef> {
        self.b.elements[e.0]
            .owned_relationships
            .iter()
            .copied()
            .filter(|&r| conforms(self.b.elements[r].ty, general))
            .map(ElementRef)
            .collect()
    }

    /// `Namespace::ownedMembership = ownedRelationship->selectByKind(Membership)`.
    pub(super) fn d_owned_memberships(&self, e: ElementRef) -> Vec<ElementRef> {
        self.owned_relationships_of_kind(e, "Membership")
    }

    /// `Namespace::ownedMember = ownedMembership->selectByKind(OwningMembership).ownedMemberElement`.
    pub(super) fn d_owned_members(&self, e: ElementRef) -> Vec<ElementRef> {
        self.d_owned_memberships(e)
            .into_iter()
            .filter(|&m| conforms(self.b.elements[m.0].ty, "OwningMembership"))
            .filter_map(|m| self.d_owned_member_element(m))
            .collect()
    }

    /// `Namespace::member = membership.memberElement` at the passthrough
    /// level: the owned memberships' members — owned member elements, and
    /// the targets of alias and other non-owning memberships, outside the
    /// model included.
    fn d_members(&mut self, e: ElementRef) -> Vec<Reference> {
        let memberships = self.d_memberships(e);
        self.ensure_by_id();
        memberships
            .into_iter()
            .filter_map(|m| self.d_member_element(m))
            .collect()
    }

    /// `Membership::memberElement`: the owned member, else the spelled
    /// target (a reference, resolved or not).
    pub(super) fn d_member_element(&mut self, m: ElementRef) -> Option<Reference> {
        if let Some(k) = self.d_owned_member_element(m) {
            return Some(Reference::Element(k));
        }
        let atom = self.b.elements[m.0].props.get("memberElement")?.clone();
        self.reference_of(&atom)
    }

    /// A reference-typed property value as a [`Reference`]: an id the
    /// model holds is its element, another id is external, and an
    /// unresolved `@ref` spelling is unresolved — unless the spelling is
    /// itself an id (the lift spells a target it cannot name that way),
    /// which is looked up like any id.
    pub(super) fn reference_of(&self, atom: &Atom) -> Option<Reference> {
        let by_id = |id: Uuid| match self.by_id.get(&id) {
            Some(&i) => Reference::Element(ElementRef(i)),
            None => Reference::External(id),
        };
        if let Some(id) = atom.as_reference() {
            return Some(by_id(id));
        }
        let spelling = atom.get("@ref")?.as_str()?;
        Some(match Uuid::parse_str(spelling.trim_matches('\'')) {
            Ok(id) => by_id(id),
            Err(_) => Reference::Unresolved(spelling.to_string()),
        })
    }

    /// `Namespace::ownedImport = ownedRelationship->selectByKind(Import)`.
    fn d_owned_imports(&self, e: ElementRef) -> Vec<ElementRef> {
        self.owned_relationships_of_kind(e, "Import")
    }

    // ---- Type ----

    /// `Type::ownedFeatureMembership = ownedRelationship->selectByKind(FeatureMembership)`.
    pub(super) fn d_owned_feature_memberships(&self, e: ElementRef) -> Vec<ElementRef> {
        self.owned_relationships_of_kind(e, "FeatureMembership")
    }

    /// `Type::ownedFeature = ownedFeatureMembership.ownedMemberFeature`.
    pub(super) fn d_owned_features(&self, e: ElementRef) -> Vec<ElementRef> {
        self.d_owned_feature_memberships(e)
            .into_iter()
            .filter_map(|m| self.d_owned_member_element(m))
            .collect()
    }

    // ---- Feature / Usage ----

    /// `owningType` for whichever kind of element declares it: a
    /// FeatureMembership's `membershipOwningNamespace`; a Feature's
    /// `owningFeatureMembership.owningType`; the specific side of a
    /// Specialization, Conjugation or Disjoining that owns it.
    pub(super) fn d_owning_type_any(&mut self, e: ElementRef) -> Option<ElementRef> {
        let ty = self.b.elements[e.0].ty;
        if conforms(ty, "FeatureMembership") {
            self.d_owning_related_element(e)
        } else if conforms(ty, "Feature") {
            self.d_owning_type(e)
        } else {
            self.d_relationship_owning_type(e)
        }
    }

    /// `Type::ownedSpecialization` and its kin (`ownedFeatureInverting`,
    /// `ownedTypeFeaturing`, the single-valued `ownedReferenceSubsetting`
    /// / `ownedCrossSubsetting`): the owned relationships of `kind`,
    /// implied ones included, for which the owner is the source end
    /// (every one written on its specific side is; a foreign payload may
    /// spell another source).
    pub(super) fn d_owned_specializations(&mut self, e: ElementRef, kind: &str) -> Vec<ElementRef> {
        let rels: Vec<ElementRef> = self
            .d_owned_relationships(e)
            .into_iter()
            .filter(|&r| self.is_kind(r, kind))
            .collect();
        let mut out = Vec::with_capacity(rels.len());
        for r in rels {
            if self.d_relationship_source(r).is_none_or(|s| s == e) {
                out.push(r);
            }
        }
        out
    }

    /// `Relationship::source` and `target` — the ends each relationship
    /// kind spells (a membership's owner and member, an import's owner
    /// and imported namespace or membership, a specialization's specific
    /// and general, an annotation's annotating and annotated elements, a
    /// dependency's clients and suppliers, …), a relationship written on
    /// its source side taking the owner as its source. Both are *owned*
    /// properties of Relationship in the abstract syntax (derived only on
    /// `TransitionUsage`), so [`Self::derived`] does not answer them;
    /// this is their navigation accessor, and the derived
    /// `relatedElement` is their union. A target outside the model is
    /// reported as such; empty for an element that is no relationship.
    pub fn relationship_ends(&mut self, e: ElementRef) -> (Vec<Reference>, Vec<Reference>) {
        self.ensure_by_id();
        let t = self.b.elements[e.0].ty;
        let owner = self.d_owning_related_element(e).map(Reference::Element);
        let get = |this: &Self, key: &str| -> Option<Reference> {
            this.b.elements[e.0]
                .props
                .get(key)
                .and_then(|atom| this.reference_of(atom))
        };
        let first = |this: &Self, keys: &[&str]| keys.iter().find_map(|k| get(this, k));
        let owned_first = |this: &Self| {
            this.b.elements[e.0]
                .children
                .first()
                .map(|&k| Reference::Element(ElementRef(k)))
        };
        let list = |this: &Self, key: &str| -> Vec<Reference> {
            this.b.elements[e.0]
                .props
                .get(key)
                .and_then(|v| v.as_array())
                .map(|a| a.iter().filter_map(|x| this.reference_of(x)).collect())
                .unwrap_or_default()
        };
        let (source, target): (Option<Reference>, Option<Reference>) = if conforms(t, "Membership")
        {
            (
                owner.clone(),
                get(self, "memberElement").or_else(|| owned_first(self)),
            )
        } else if conforms(t, "Import") {
            (
                owner.clone(),
                first(self, &["importedNamespace", "importedMembership"]),
            )
        } else {
            match t {
                "Subclassification" | "Specialization" => (
                    first(self, &["subclassifier", "specific"]),
                    first(self, &["superclassifier", "general"]),
                ),
                "FeatureTyping" | "ConjugatedPortTyping" => {
                    (get(self, "typedFeature"), get(self, "type"))
                }
                "Subsetting" | "Redefinition" | "ReferenceSubsetting" | "CrossSubsetting" => (
                    first(
                        self,
                        &[
                            "subsettingFeature",
                            "redefiningFeature",
                            "referencingFeature",
                            "crossingFeature",
                        ],
                    )
                    .or_else(|| owner.clone()),
                    first(
                        self,
                        &[
                            "subsettedFeature",
                            "redefinedFeature",
                            "referencedFeature",
                            "crossedFeature",
                        ],
                    ),
                ),
                "Dependency" => return (list(self, "client"), list(self, "supplier")),
                "Annotation" => (
                    self.d_annotating_element(e).map(Reference::Element),
                    self.d_annotated_element(e),
                ),
                "Conjugation" | "PortConjugation" => (
                    get(self, "conjugatedType").or_else(|| owner.clone()),
                    get(self, "originalType"),
                ),
                "Disjoining" => (
                    get(self, "typeDisjoined").or_else(|| owner.clone()),
                    get(self, "disjoiningType"),
                ),
                "FeatureInverting" => (
                    get(self, "featureInverted").or_else(|| owner.clone()),
                    get(self, "invertingFeature"),
                ),
                "TypeFeaturing" => (
                    get(self, "featureOfType").or_else(|| owner.clone()),
                    get(self, "featuringType"),
                ),
                "Unioning" | "Intersecting" | "Differencing" | "FeatureChaining"
                | "FeatureValue" => (
                    owner.clone(),
                    first(
                        self,
                        &[
                            "unioningType",
                            "intersectingType",
                            "differencingType",
                            "chainingFeature",
                        ],
                    )
                    .or_else(|| owned_first(self)),
                ),
                _ => (None, None),
            }
        };
        (source.into_iter().collect(), target.into_iter().collect())
    }

    /// The Type that owns a Specialization, Conjugation, Disjoining,
    /// FeatureInverting or TypeFeaturing *and* is its source end — a
    /// relationship written on its specific side (`part def B :> A`)
    /// rather than standalone (`specialization Sub subclassifier B …`,
    /// which rides a membership and has no owning related element).
    fn d_relationship_owning_type(&mut self, e: ElementRef) -> Option<ElementRef> {
        if self.b.elements[e.0].owning_relationship.is_some() {
            return None;
        }
        let owner = self.d_owning_related_element(e)?;
        if !self.is_kind(owner, "Type") {
            return None;
        }
        match self.d_relationship_source(e) {
            Some(src) if src != owner => None,
            _ => Some(owner),
        }
    }

    /// The source end a relationship spells, by its metaclass's source
    /// property (`subclassifier`, `subsettingFeature`, `conjugatedType`,
    /// …). `None` when unspelled or unresolved — in which case
    /// [`Self::d_relationship_owning_type`] takes the owning related
    /// element as the source, which the grammars guarantee for every
    /// relationship written on its specific side. Each carrier stores
    /// only its own key, so no wrong key can match.
    fn d_relationship_source(&mut self, e: ElementRef) -> Option<ElementRef> {
        self.ensure_by_id();
        const SOURCES: &[&str] = &[
            "subclassifier",
            "subsettingFeature",
            "redefiningFeature",
            "referencingFeature",
            "crossingFeature",
            "typedFeature",
            "specific",
            "conjugatedType",
            "typeDisjoined",
            "featureInverted",
            "featureOfType",
        ];
        SOURCES
            .iter()
            .find_map(|k| self.prop_target(e.0, k))
            .map(ElementRef)
    }

    /// `Feature::owningFeatureMembership` — the owning relationship when it
    /// is a FeatureMembership.
    fn d_owning_feature_membership(&self, e: ElementRef) -> Option<ElementRef> {
        let rel = self.b.elements[e.0].owning_relationship?;
        conforms(self.b.elements[rel].ty, "FeatureMembership").then_some(ElementRef(rel))
    }

    /// `Feature::owningType = owningFeatureMembership.owningType`.
    pub(super) fn d_owning_type(&mut self, e: ElementRef) -> Option<ElementRef> {
        let m = self.d_owning_feature_membership(e)?;
        self.d_owning_related_element(m)
            .filter(|&o| self.is_kind(o, "Type"))
    }

    /// `Feature::endOwningType` — the owning type through an
    /// EndFeatureMembership.
    fn d_end_owning_type(&mut self, e: ElementRef) -> Option<ElementRef> {
        let m = self.d_owning_feature_membership(e)?;
        if self.b.elements[m.0].ty != "EndFeatureMembership" {
            return None;
        }
        self.d_owning_type(e)
    }

    // ---- Names, annotations and per-element structure ----

    /// `Usage::isReference = not isComposite`; `None` where the metaclass
    /// spells no compositeness.
    fn d_is_reference(&self, e: ElementRef) -> Option<bool> {
        self.b.elements[e.0]
            .props
            .get("isComposite")
            .and_then(|v| v.as_bool())
            .map(|c| !c)
    }

    /// `RequirementDefinition::text = documentation.body` — the bodies of
    /// the element's owned Documentation, in declaration order.
    fn d_text(&self, e: ElementRef) -> Vec<String> {
        self.d_owned_elements(e)
            .into_iter()
            .filter(|&k| self.b.elements[k.0].ty == "Documentation")
            .filter_map(|k| {
                self.b.elements[k.0]
                    .props
                    .get("body")
                    .and_then(|v| v.as_str())
                    .map(str::to_string)
            })
            .collect()
    }

    /// `Type::multiplicity` — the owned member that is a Multiplicity (a
    /// `[n..m]` MultiplicityRange, or a KerML `multiplicity` member). A
    /// Type owns at most one. KerML's derive rule adds a fallback to the
    /// general Type's multiplicity through an owned Specialization; that
    /// contradicts the property's `subsets ownedMember`, and the property
    /// definition wins here, as it does in the emitter.
    fn d_multiplicity(&self, e: ElementRef) -> Option<ElementRef> {
        self.d_owned_members(e)
            .into_iter()
            .find(|&m| self.is_kind(m, "Multiplicity"))
    }

    /// The Annotation relationships `e` owns that annotate `e` itself
    /// (`annotates`) or another element (the `about` shape). An Annotation
    /// that owns its annotating element annotates its owner.
    fn d_owned_annotations(&mut self, e: ElementRef, annotates_self: bool) -> Vec<ElementRef> {
        let owned = self.owned_relationships_of_kind(e, "Annotation");
        if owned.is_empty() {
            return owned;
        }
        self.ensure_by_id();
        owned
            .into_iter()
            .filter(|&r| {
                let annotates = match self.prop_target(r.0, "annotatedElement") {
                    Some(t) => t == e.0,
                    // Unspelled: an Annotation that owns its annotating
                    // element annotates its owner (the prefix shape).
                    None => self.d_owned_annotating_element(r).is_some(),
                };
                annotates == annotates_self
            })
            .collect()
    }

    /// `AnnotatingElement::annotation` — the owning Annotation (the
    /// prefix shape) followed by the owned ones that annotate another.
    fn d_annotations(&mut self, e: ElementRef) -> Vec<ElementRef> {
        let owning = self.b.elements[e.0]
            .owning_relationship
            .map(ElementRef)
            .filter(|&r| self.b.elements[r.0].ty == "Annotation");
        let mut out: Vec<ElementRef> = owning.into_iter().collect();
        out.extend(self.d_owned_annotations(e, false));
        out
    }

    /// `AnnotatingElement::annotatedElement = if annotation->notEmpty()
    /// then annotation.annotatedElement else Sequence{owningNamespace}` —
    /// the owner stands in only when the element carries no annotation at
    /// all. A target outside the model is reported as such.
    fn d_annotating_targets(&mut self, e: ElementRef) -> Vec<Reference> {
        let annotations = self.d_annotations(e);
        if annotations.is_empty() {
            return self
                .d_owner(e)
                .map(Reference::Element)
                .into_iter()
                .collect();
        }
        let mut out = Vec::new();
        for a in annotations {
            if let Some(t) = self.d_annotated_element(a) {
                out.push(t);
            }
        }
        out
    }

    /// `Annotation::annotatedElement` — spelled, else the owner in the
    /// shape where the Annotation owns its annotating element.
    fn d_annotated_element(&mut self, a: ElementRef) -> Option<Reference> {
        self.ensure_by_id();
        if let Some(atom) = self.b.elements[a.0].props.get("annotatedElement").cloned() {
            if let Some(r) = self.reference_of(&atom) {
                return Some(r);
            }
        }
        self.d_owned_annotating_element(a)
            .and(self.d_owning_related_element(a))
            .map(Reference::Element)
    }

    /// `Annotation::ownedAnnotatingElement` — the prefix-annotation
    /// shape. Defensive: no model built from text carries it, and the
    /// payload loader normalizes it away on load (the emitter reads it
    /// from a raw array — `full_json.rs::prefix_annotation_shape_derives_from_compact`),
    /// so this branch is reached only by a hand-built model.
    fn d_owned_annotating_element(&self, a: ElementRef) -> Option<ElementRef> {
        self.b.elements[a.0]
            .children
            .iter()
            .copied()
            .map(ElementRef)
            .find(|&k| self.is_kind(k, "AnnotatingElement"))
    }

    /// `Annotation::annotatingElement` — the owned annotating element,
    /// else the owner (the `about` shape this toolkit emits).
    fn d_annotating_element(&mut self, a: ElementRef) -> Option<ElementRef> {
        if let Some(k) = self.d_owned_annotating_element(a) {
            return Some(k);
        }
        self.d_owning_related_element(a)
            .filter(|&o| self.is_kind(o, "AnnotatingElement"))
    }

    // ---- Typing and structure bases ----

    /// `Feature::type`: the targets of the feature's own typings
    /// (`FeatureTyping`, `ConjugatedPortTyping`) and, transitively, of its
    /// typing features — the features it subsets, redefines or references
    /// through an owned Subsetting kind, and the last link of an owned
    /// feature chain (KerML `Feature::typingFeatures`, closed). A typing
    /// target outside the model (a library type when no library is
    /// loaded) is reported as such; the walk through typing features stays
    /// inside the model (library features included when loaded) and
    /// guards cycles.
    pub(super) fn d_types(&mut self, e: ElementRef) -> Vec<Reference> {
        self.ensure_by_id();
        let mut out: Vec<Reference> = Vec::new();
        let mut visited: std::collections::HashSet<usize> = std::collections::HashSet::new();
        let mut stack = vec![e.0];
        while let Some(f) = stack.pop() {
            if !visited.insert(f) {
                continue;
            }
            // The explicit relationships and the implied *typings* (a
            // variant's typing by its variation definition). The implied
            // library subsettings are deliberately not followed: they
            // would append the library chain (`Part`, `Item`, `Occurrence`,
            // `Anything`) to every usage's types, a growth that belongs
            // with the inheritance closure policy and its measurement.
            let mut rels: Vec<usize> = self.b.elements[f].owned_relationships.to_vec();
            rels.extend(
                self.implied_relationships(ElementRef(f))
                    .into_iter()
                    .map(|r| r.0)
                    .filter(|&r| self.b.elements[r].ty == "FeatureTyping"),
            );
            let mut last_chain: Option<usize> = None;
            for r in rels {
                let ty = self.b.elements[r].ty;
                if matches!(ty, "FeatureTyping" | "ConjugatedPortTyping") {
                    if let Some(t) = self.b.elements[r]
                        .props
                        .get("type")
                        .and_then(|atom| self.reference_of(atom))
                    {
                        if !out.contains(&t) {
                            out.push(t);
                        }
                    }
                } else if conforms(ty, "Subsetting") {
                    let key = match ty {
                        "Redefinition" => "redefinedFeature",
                        "ReferenceSubsetting" => "referencedFeature",
                        "CrossSubsetting" => "crossedFeature",
                        _ => "subsettedFeature",
                    };
                    if let Some(t) = self.prop_target(r, key) {
                        stack.push(t);
                    }
                } else if ty == "FeatureChaining" {
                    last_chain = self.prop_target(r, "chainingFeature");
                }
            }
            if let Some(t) = last_chain {
                stack.push(t);
            }
        }
        out
    }

    /// `Feature::chainingFeature = ownedFeatureChaining.chainingFeature`,
    /// in chaining order; a link outside the model is reported as such.
    pub(super) fn d_chaining_features(&mut self, e: ElementRef) -> Vec<Reference> {
        self.ensure_by_id();
        self.b.elements[e.0]
            .owned_relationships
            .iter()
            .copied()
            .filter(|&r| self.b.elements[r].ty == "FeatureChaining")
            .filter_map(|r| {
                self.b.elements[r]
                    .props
                    .get("chainingFeature")
                    .and_then(|atom| self.reference_of(atom))
            })
            .collect()
    }

    /// `Feature::featureTarget = if chainingFeature->isEmpty() then self
    /// else chainingFeature->last()`.
    pub(super) fn d_feature_target(&mut self, e: ElementRef) -> Reference {
        self.d_chaining_features(e)
            .pop()
            .unwrap_or(Reference::Element(e))
    }

    /// `Feature::crossFeature` — the second chaining feature of the
    /// crossed feature of the owned CrossSubsetting, if any; `None` when
    /// the crossed feature is outside the model (its chain is not
    /// visible).
    fn d_cross_feature(&mut self, e: ElementRef) -> Option<Reference> {
        self.ensure_by_id();
        let cross = self
            .owned_relationships_of_kind(e, "CrossSubsetting")
            .into_iter()
            .next()?;
        let crossed = ElementRef(self.prop_target(cross.0, "crossedFeature")?);
        self.d_chaining_features(crossed).into_iter().nth(1)
    }

    /// `Connector::relatedFeature` — the referenced features of the
    /// connector ends (`connectorEnd.ownedReferenceSubsetting.referencedFeature`),
    /// in end order; an end without a reference subsetting contributes
    /// nothing, a target outside the model is reported as such.
    /// `sourceFeature` is the first, `targetFeature` the rest.
    pub(super) fn d_related_features(&mut self, e: ElementRef) -> Vec<Reference> {
        self.ensure_by_id();
        let features = self.d_features(e);
        let ends = self.d_ends(features);
        ends.into_iter()
            .filter_map(|end| {
                self.owned_relationships_of_kind(end, "ReferenceSubsetting")
                    .into_iter()
                    .next()
            })
            .filter_map(|r| {
                self.b.elements[r.0]
                    .props
                    .get("referencedFeature")
                    .and_then(|atom| self.reference_of(atom))
            })
            .collect()
    }

    /// `Flow::sourceOutputFeature` / `targetInputFeature`: the first
    /// owned feature of the first / second flow end (`from a.out` lowers
    /// to a flow end owning a feature that redefines `out`).
    fn d_flow_end_feature(&mut self, e: ElementRef, position: usize) -> Option<ElementRef> {
        let features = self.d_features(e);
        let end = self
            .d_ends(features)
            .into_iter()
            .filter(|&f| self.b.elements[f.0].ty == "FlowEnd")
            .nth(position)?;
        self.d_owned_features(end).into_iter().next()
    }

    /// `Type::endFeature = feature->select(isEnd)` over the given features.
    pub(super) fn d_ends(&self, features: Vec<ElementRef>) -> Vec<ElementRef> {
        features
            .into_iter()
            .filter(|&f| {
                self.b.elements[f.0]
                    .props
                    .get("isEnd")
                    .and_then(|v| v.as_bool())
                    .unwrap_or(false)
            })
            .collect()
    }

    /// The direction-filtered features in feature order, per the OCL
    /// (`feature->select(f | directionOf(f) = in or inout)`): every
    /// directed one (`None`), the inputs (`Some(true)`: `in` and `inout`)
    /// or the outputs (`Some(false)`: `out` and `inout`). The direction is
    /// the effective one ([`Self::effective_direction`]: a parameter
    /// membership's default stands in for an unspelled direction).
    pub(super) fn d_directed(
        &self,
        features: Vec<ElementRef>,
        input: Option<bool>,
    ) -> Vec<ElementRef> {
        let dir = |f: ElementRef| -> Option<&str> { self.effective_direction(f) };
        let one_way = match input {
            None => return features.into_iter().filter(|&f| dir(f).is_some()).collect(),
            Some(true) => "in",
            Some(false) => "out",
        };
        features
            .into_iter()
            .filter(|&f| matches!(dir(f), Some(d) if d == one_way || d == "inout"))
            .collect()
    }

    /// `variant = variantMembership.ownedVariantUsage`.
    pub(super) fn d_variants(&self, e: ElementRef) -> Vec<ElementRef> {
        self.b.elements[e.0]
            .owned_relationships
            .iter()
            .copied()
            .filter(|&r| self.b.elements[r].ty == "VariantMembership")
            .flat_map(|r| self.b.elements[r].children.iter().copied())
            .map(ElementRef)
            .collect()
    }

    // ---- Membership / Import side ----

    /// `OwningMembership::ownedMemberElement` — the element the membership
    /// owns (its `ownedRelatedElement`).
    pub(super) fn d_owned_member_element(&self, m: ElementRef) -> Option<ElementRef> {
        self.b.elements[m.0]
            .children
            .first()
            .copied()
            .map(ElementRef)
    }

    /// `Import::importedElement`: the imported namespace of a
    /// NamespaceImport, the imported membership's member for a
    /// MembershipImport. A target outside the model is reported as such —
    /// an external membership cannot be dereferenced, so it stands for
    /// its member.
    fn d_imported_element(&mut self, imp: ElementRef) -> Option<Reference> {
        self.ensure_by_id();
        if let Some(atom) = self.b.elements[imp.0]
            .props
            .get("importedNamespace")
            .cloned()
        {
            return self.reference_of(&atom);
        }
        let atom = self.b.elements[imp.0]
            .props
            .get("importedMembership")?
            .clone();
        match self.reference_of(&atom)? {
            Reference::Element(m) if conforms(self.b.elements[m.0].ty, "Membership") => {
                self.d_member_element(m)
            }
            // A foreign payload may reference the element directly.
            other => Some(other),
        }
    }
}

/// Whether a composition base answers by reference (so an empty base
/// yields an empty `References` rather than `Elements`).
fn by_reference_base(base: &str) -> bool {
    matches!(
        base,
        "type"
            | "definition"
            | "member"
            | "annotatedElement"
            | "importedElement"
            | "featureTarget"
            | "function"
            | "instantiatedType"
            | "referent"
    ) || composition(base).is_some_and(|(b, _, _)| by_reference_base(b))
}

fn opt(e: Option<ElementRef>) -> DerivedValue {
    match e {
        Some(e) => DerivedValue::Element(e),
        None => DerivedValue::Null,
    }
}

fn opt_ref(r: Option<Reference>) -> DerivedValue {
    match r {
        Some(r) => DerivedValue::Reference(r),
        None => DerivedValue::Null,
    }
}

#[cfg(test)]
mod tests {
    /// `declared` binary-searches the schema catalog: the metaclass entries
    /// and every property list must stay sorted.
    #[test]
    fn catalog_is_sorted() {
        use crate::schema_props::METACLASS_PROPS;
        assert!(METACLASS_PROPS.windows(2).all(|w| w[0].0 < w[1].0));
        for (m, props) in METACLASS_PROPS {
            assert!(
                props.windows(2).all(|w| w[0].0 < w[1].0),
                "{m}'s property list is not sorted"
            );
        }
        assert!(
            crate::derived_names::DERIVED_NAMES
                .windows(2)
                .all(|w| w[0] < w[1])
        );
    }

    #[test]
    fn hand_written_tables_are_sorted() {
        assert!(super::EXACT.windows(2).all(|w| w[0] < w[1]));
        assert!(super::PASSTHROUGH.windows(2).all(|w| w[0] < w[1]));
        let mut seen = std::collections::HashSet::new();
        for n in super::computed_names() {
            assert!(seen.insert(n), "{n} listed twice");
        }
    }

    /// `derives` and `derived` agree by construction: a composition is
    /// computed on a metaclass only where its whole base chain is
    /// declared there.
    #[test]
    fn composition_fidelity_follows_the_declared_base_chain() {
        use super::{Derives, OWNED_BASES, carries, composition, declared, derives, member_side};
        for (m, _) in crate::schema_props::METACLASS_PROPS {
            for name in super::computed_names() {
                if !matches!(derives(m, name), Derives::Exact | Derives::Passthrough) {
                    continue;
                }
                // A membership-side name is the owned member there, not the
                // composition of the same name on the owner.
                if member_side(m, name).is_some() {
                    continue;
                }
                let mut at = name;
                while let Some((base, _, _)) =
                    composition(at).filter(|_| !super::is_hand_written(at))
                {
                    if OWNED_BASES.contains(&base) {
                        assert!(
                            carries(m, base),
                            "{m}.{name}: owned base {base} not carried"
                        );
                        break;
                    }
                    assert!(declared(m, base), "{m}.{name}: base {base} not declared");
                    at = base;
                }
            }
        }
    }

    #[test]
    fn computed_names_are_declared_somewhere() {
        for name in super::computed_names() {
            assert!(
                crate::derived_names::DERIVED_NAMES
                    .binary_search(&name)
                    .is_ok(),
                "{name} is not a derived name"
            );
        }
    }
}
