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

use crate::json::{
    implicit_def_bases, implicit_usage_bases, model_to_compact_json, to_compact_json,
};
use crate::lift::{def_kind_of, usage_kind_of};
use crate::model::Model;
use crate::schema_props::METACLASS_PROPS;
use serde_json::{Map, Value, json};
use std::collections::HashMap;
use sysmlv2_syntax::ast::{Dialect, SourceUnit};
use uuid::Uuid;

/// How full-form interchange handles compact `{"@ref": ...}` values. The
/// published full schema permits only `@id` references, so preserving a
/// partial model requires schema-valid textual recovery annotations.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum UnresolvedReferencePolicy {
    /// Emit deterministic recovery annotations. This is the default and is
    /// lossless when lifted by this toolkit.
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

/// Serialize a model to the full interchange form. Library units provide
/// the implied-relationship targets (normative IDs) and are not emitted.
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
    let compact = model_to_compact_json(model);
    // Elements only: membership ids share their member's qualified name and
    // must not win the name→id inversion (implied bases target elements).
    let lib_names = crate::json::library_element_name_map(model);
    let mut by_name = HashMap::new();
    for (id, segments) in &lib_names {
        by_name.insert(segments.join("::"), id.clone());
    }
    full_from_compact_policy(compact, &by_name, policy)
}

/// Serialize a single unit to the full form. Without a library, implied
/// relationships cannot be resolved and are omitted (`isImpliedIncluded`
/// stays `false`); derived properties are still completed.
pub fn to_full_json(unit: &SourceUnit) -> Value {
    to_full_json_with_policy(unit, UnresolvedReferencePolicy::Preserve)
        .expect("the preserve policy cannot reject")
}

/// [`to_full_json`] with unresolved-reference recovery annotations — see
/// [`model_to_full_json_with`].
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
    full_from_compact_policy(to_compact_json(unit), &HashMap::new(), policy)
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
    full_from_compact_with(compact, lib_by_name, recover_refs)
}

pub fn from_compact_value_with_policy(
    compact: Value,
    lib_by_name: &HashMap<String, String>,
    policy: UnresolvedReferencePolicy,
) -> Result<Value, UnresolvedReferenceError> {
    full_from_compact_policy(compact, lib_by_name, policy)
}

fn id_ref(id: &str) -> Value {
    json!({ "@id": id })
}

fn ty(el: &Map<String, Value>) -> &str {
    el.get("@type").and_then(|v| v.as_str()).unwrap_or("")
}

fn eid(el: &Map<String, Value>) -> String {
    el.get("@id")
        .and_then(|v| v.as_str())
        .unwrap_or("")
        .to_string()
}

fn ref_of(v: &Value) -> Option<String> {
    v.get("@id").and_then(|x| x.as_str()).map(|s| s.to_string())
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
                out.push(spelling.to_string());
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
    ))
}

pub(crate) fn full_from_compact_with(
    compact: Value,
    lib_by_name: &HashMap<String, String>,
    recover_refs: bool,
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
    if !lib_by_name.is_empty() {
        add_implied_relationships(&mut elements, lib_by_name);
    }
    let implied_included = !lib_by_name.is_empty();

    // ---- graph indexes ----
    let index: HashMap<String, usize> = elements
        .iter()
        .enumerate()
        .map(|(i, el)| (eid(el), i))
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

    let catalog: HashMap<&str, &[(&str, u8)]> = METACLASS_PROPS.iter().copied().collect();

    // ---- derived properties ----
    for i in 0..elements.len() {
        let t = ty(&elements[i]).to_string();
        let mut derived: Map<String, Value> = Map::new();
        // Derivations that must win over a compact-spelled value (the
        // pilot computes these at the model level regardless of the
        // textual spelling): applied with insert, not or_insert.
        let mut overrides: Map<String, Value> = Map::new();

        // Ownership.
        let owner_idx = owner_rel[i].and_then(|r| rel_owner[r]);
        derived.insert(
            "owner".into(),
            owner_idx
                .map(|o| id_ref(&eid(&elements[o])))
                .unwrap_or(Value::Null),
        );
        let owning_membership = owner_rel[i].filter(|&r| is_membership(ty(&elements[r])));
        derived.insert(
            "owningMembership".into(),
            owning_membership
                .map(|r| id_ref(&eid(&elements[r])))
                .unwrap_or(Value::Null),
        );
        derived.insert(
            "owningNamespace".into(),
            owning_membership
                .and(owner_idx)
                .map(|o| id_ref(&eid(&elements[o])))
                .unwrap_or(Value::Null),
        );
        // Feature::endOwningType — the owner through an EndFeatureMembership
        // (the catalog filter drops this for metaclasses without it) — and
        // such end features are constant (KerML 2025 metamodel).
        if owner_rel[i].is_some_and(|r| ty(&elements[r]) == "EndFeatureMembership") {
            if let Some(o) = owner_idx {
                derived.insert("endOwningType".into(), id_ref(&eid(&elements[o])));
            }
            if t != "FlowEnd" {
                derived.insert("isConstant".into(), Value::Bool(true));
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

        // Owned elements: through each owned relationship.
        let mut owned_elements = Vec::new();
        for &r in &owned_rels[i] {
            for &k in &related_elems[r] {
                owned_elements.push(id_ref(&eid(&elements[k])));
            }
        }
        derived.insert("ownedElement".into(), Value::Array(owned_elements));

        // Names.
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
        // Usage::isReference is derived as the negation of isComposite
        // (pilot `Usage_isReference_SettingDelegate`); the catalog filter
        // drops this for metaclasses without the property.
        if let Some(c) = elements[i].get("isComposite").and_then(|v| v.as_bool()) {
            derived.insert("isReference".into(), Value::Bool(!c));
        }
        derived.insert("shortName".into(), declared_short);
        derived.insert(
            "qualifiedName".into(),
            qnames[i].clone().map(Value::String).unwrap_or(Value::Null),
        );

        // Annotating members.
        let owned_kids: Vec<usize> = owned_rels[i]
            .iter()
            .flat_map(|&r| related_elems[r].iter().copied())
            .collect();
        let kids_of_type = |name: &str| -> Vec<Value> {
            owned_kids
                .iter()
                .filter(|&&k| ty(&elements[k]) == name)
                .map(|&k| id_ref(&eid(&elements[k])))
                .collect()
        };
        derived.insert(
            "documentation".into(),
            Value::Array(kids_of_type("Documentation")),
        );
        // Requirement/concern `text` is the owned documentation bodies
        // (pilot `RequirementDefinition_text_SettingDelegate`); the catalog
        // filter drops it for metaclasses without the property.
        let texts: Vec<Value> = owned_kids
            .iter()
            .filter(|&&k| ty(&elements[k]) == "Documentation")
            .filter_map(|&k| elements[k].get("body").filter(|v| !v.is_null()).cloned())
            .collect();
        derived.insert("text".into(), Value::Array(texts));
        derived.insert(
            "textualRepresentation".into(),
            Value::Array(kids_of_type("TextualRepresentation")),
        );
        derived.insert(
            "ownedAnnotation".into(),
            Value::Array(
                owned_rels[i]
                    .iter()
                    .filter(|&&r| ty(&elements[r]) == "Annotation")
                    .map(|&r| id_ref(&eid(&elements[r])))
                    .collect(),
            ),
        );

        // Namespace-level memberships and imports.
        let memberships: Vec<Value> = owned_rels[i]
            .iter()
            .filter(|&&r| is_membership(ty(&elements[r])))
            .map(|&r| id_ref(&eid(&elements[r])))
            .collect();
        derived.insert("ownedMembership".into(), Value::Array(memberships.clone()));
        derived.insert("membership".into(), Value::Array(memberships));
        let owned_members: Vec<Value> = owned_rels[i]
            .iter()
            .filter(|&&r| is_membership(ty(&elements[r])))
            .flat_map(|&r| related_elems[r].iter().map(|&k| id_ref(&eid(&elements[k]))))
            .collect();
        derived.insert("ownedMember".into(), Value::Array(owned_members.clone()));
        derived.insert("member".into(), Value::Array(owned_members));
        derived.insert(
            "ownedImport".into(),
            Value::Array(
                owned_rels[i]
                    .iter()
                    .filter(|&&r| is_import(ty(&elements[r])))
                    .map(|&r| id_ref(&eid(&elements[r])))
                    .collect(),
            ),
        );

        // Type-level features.
        let feature_memberships: Vec<usize> = owned_rels[i]
            .iter()
            .copied()
            .filter(|&r| {
                matches!(
                    ty(&elements[r]),
                    "FeatureMembership"
                        | "EndFeatureMembership"
                        | "ParameterMembership"
                        | "ReturnParameterMembership"
                        | "ResultExpressionMembership"
                        | "VariantMembership"
                        | "SubjectMembership"
                        | "ActorMembership"
                        | "StakeholderMembership"
                        | "ObjectiveMembership"
                        | "RequirementConstraintMembership"
                        | "FramedConcernMembership"
                        | "RequirementVerificationMembership"
                        | "StateSubactionMembership"
                        | "TransitionFeatureMembership"
                        | "ViewRenderingMembership"
                        | "ElementFilterMembership"
                )
            })
            .collect();
        derived.insert(
            "ownedFeatureMembership".into(),
            Value::Array(
                feature_memberships
                    .iter()
                    .map(|&r| id_ref(&eid(&elements[r])))
                    .collect(),
            ),
        );
        derived.insert(
            "featureMembership".into(),
            derived["ownedFeatureMembership"].clone(),
        );
        let features: Vec<usize> = feature_memberships
            .iter()
            .flat_map(|&r| related_elems[r].iter().copied())
            .collect();
        let feature_refs: Vec<Value> = features
            .iter()
            .map(|&k| id_ref(&eid(&elements[k])))
            .collect();
        derived.insert("ownedFeature".into(), Value::Array(feature_refs.clone()));
        derived.insert("feature".into(), Value::Array(feature_refs));
        let ends: Vec<Value> = features
            .iter()
            .filter(|&&k| {
                elements[k]
                    .get("isEnd")
                    .and_then(|v| v.as_bool())
                    .unwrap_or(false)
            })
            .map(|&k| id_ref(&eid(&elements[k])))
            .collect();
        derived.insert("ownedEndFeature".into(), Value::Array(ends.clone()));
        derived.insert("endFeature".into(), Value::Array(ends));
        let by_direction = |dir: &str| -> Vec<Value> {
            features
                .iter()
                .filter(|&&k| {
                    elements[k].get("direction").and_then(|v| v.as_str()) == Some(dir)
                        || (dir == "inout"
                            && elements[k].get("direction").and_then(|v| v.as_str())
                                == Some("inout"))
                })
                .map(|&k| id_ref(&eid(&elements[k])))
                .collect()
        };
        let mut input = by_direction("in");
        input.extend(by_direction("inout"));
        let mut output = by_direction("out");
        output.extend(by_direction("inout"));
        derived.insert("input".into(), Value::Array(input));
        derived.insert("output".into(), Value::Array(output));
        let directed: Vec<Value> = features
            .iter()
            .filter(|&&k| {
                elements[k]
                    .get("direction")
                    .map(|v| v.is_string())
                    .unwrap_or(false)
            })
            .map(|&k| id_ref(&eid(&elements[k])))
            .collect();
        derived.insert("directedFeature".into(), Value::Array(directed.clone()));
        derived.insert("directedUsage".into(), Value::Array(directed));

        // Specializations owned by this element.
        let rels_of = |names: &[&str]| -> Vec<Value> {
            owned_rels[i]
                .iter()
                .filter(|&&r| names.contains(&ty(&elements[r])))
                .map(|&r| id_ref(&eid(&elements[r])))
                .collect()
        };
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
        derived.insert(
            "ownedCrossSubsetting".into(),
            rels_of(&["CrossSubsetting"])
                .into_iter()
                .next()
                .unwrap_or(Value::Null),
        );
        derived.insert(
            "ownedConjugator".into(),
            rels_of(&["Conjugation", "PortConjugation"])
                .into_iter()
                .next()
                .unwrap_or(Value::Null),
        );
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
        derived.insert("type".into(), Value::Array(typing_targets.clone()));
        if t.ends_with("Usage") || usage_kind_of(&t, Dialect::Sysml).is_some() {
            derived.insert("definition".into(), Value::Array(typing_targets));
        }

        // Usage kind-filtered lists (ownedPart / nestedPart / …).
        let usage_kids: Vec<usize> = features
            .iter()
            .copied()
            .filter(|&k| usage_kind_of(ty(&elements[k]), Dialect::Sysml).is_some())
            .collect();
        let usage_kid_refs: Vec<Value> = usage_kids
            .iter()
            .map(|&k| id_ref(&eid(&elements[k])))
            .collect();
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
                    .flat_map(|&r| related_elems[r].iter().map(|&k| id_ref(&eid(&elements[k]))))
                    .collect(),
            ),
        );

        // Relationship endpoints.
        fill_relationship_endpoints(&mut derived, &elements, i, &rel_owner, &related_elems);

        // Derived redefinitions with non-nullable schema types.
        if is_membership(&t) {
            // Owning-membership family: the owned member element under
            // redefining names.
            let owned_member = related_elems[i]
                .first()
                .map(|&k| id_ref(&eid(&elements[k])));
            if let Some(m) = &owned_member {
                derived.insert("ownedMemberElement".into(), m.clone());
                derived.insert("ownedMemberFeature".into(), m.clone());
                if let Some(id) = ref_of(m) {
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
            if let Some(o) = rel_owner[i] {
                derived.insert("owningType".into(), id_ref(&eid(&elements[o])));
            }
        }
        if is_import(&t) {
            if let Some(o) = rel_owner[i] {
                derived.insert("importOwningNamespace".into(), id_ref(&eid(&elements[o])));
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
                                related_elems[m]
                                    .first()
                                    .map(|&k| id_ref(&eid(&elements[k])))
                            })
                    })
                    .unwrap_or(target);
                derived.insert("importedElement".into(), target);
            }
        }
        // Features: featureTarget = last chaining feature, else self.
        let self_ref = id_ref(&eid(&elements[i]));
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
                    .map(|&r| id_ref(&eid(&elements[r])))
                    .collect(),
            ),
        );
        derived.insert(
            "featureTarget".into(),
            last_chain.unwrap_or(self_ref.clone()),
        );
        // Expressions: `result`/`function` — approximated by self-reference
        // until result parameters are synthesized (documented).
        derived.insert("result".into(), self_ref.clone());
        if t == "FeatureValue" {
            if let Some(o) = rel_owner[i] {
                derived.insert("featureWithValue".into(), id_ref(&eid(&elements[o])));
            }
            if let Some(&k) = related_elems[i].first() {
                derived.insert("value".into(), id_ref(&eid(&elements[k])));
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
                    .or_else(|| {
                        related_elems[r]
                            .first()
                            .map(|&k| id_ref(&eid(&elements[k])))
                    })
            });
        match t.as_str() {
            "FeatureReferenceExpression" => {
                if let Some(m) = &membership_target {
                    derived.insert("referent".into(), m.clone());
                }
            }
            "FeatureChainExpression" => {
                if let Some(m) = &membership_target {
                    derived.insert("targetFeature".into(), m.clone());
                }
            }
            "ReferenceSubsetting" => {
                if let Some(o) = rel_owner[i] {
                    derived.insert("referencingFeature".into(), id_ref(&eid(&elements[o])));
                }
            }
            "CrossSubsetting" => {
                if let Some(o) = rel_owner[i] {
                    derived.insert("crossingFeature".into(), id_ref(&eid(&elements[o])));
                }
            }
            "PortDefinition" => {
                if let Some(&c) = owned_kids
                    .iter()
                    .find(|&&k| ty(&elements[k]) == "ConjugatedPortDefinition")
                {
                    derived.insert(
                        "conjugatedPortDefinition".into(),
                        id_ref(&eid(&elements[c])),
                    );
                }
            }
            "ConjugatedPortDefinition" => {
                derived.insert("isConjugated".into(), Value::Bool(true));
                if let Some(o) = owner_idx {
                    derived.insert("originalPortDefinition".into(), id_ref(&eid(&elements[o])));
                }
                if let Some(&pc) = owned_rels[i]
                    .iter()
                    .find(|&&r| ty(&elements[r]) == "PortConjugation")
                {
                    derived.insert("ownedPortConjugator".into(), id_ref(&eid(&elements[pc])));
                }
            }
            // The conjugated definition: a PortConjugation's owner, a
            // State sub-actions: the entry/do/exit members by kind.
            "StateUsage" | "StateDefinition" => {
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
                        .or_else(|| {
                            related_elems[r]
                                .first()
                                .map(|&k| id_ref(&eid(&elements[k])))
                        });
                    if let Some(v) = target {
                        derived.insert(prop.into(), v);
                    }
                }
            }
            // The verified requirement is the member's *referenced* target
            // — the chain's last link when the reference is a chain — not
            // the implicit member itself.
            "RequirementVerificationMembership" => {
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
            "VerificationCaseUsage" | "VerificationCaseDefinition" => {
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
                                        .map(|&k| id_ref(&eid(&elements[k])))
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
            "ViewRenderingMembership" => {
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
            "ViewUsage" | "ViewDefinition" => {
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
                        .or_else(|| Some(id_ref(&eid(&elements[k]))))
                });
                if let Some(v) = target {
                    derived.insert("viewRendering".into(), v);
                }
            }
            // The element whose metadata is accessed: the owned
            // Membership's member (the generic required-ref fill would
            // self-refer).
            "MetadataAccessExpression" => {
                let target = owned_rels[i]
                    .iter()
                    .find(|&&r| ty(&elements[r]) == "Membership")
                    .and_then(|&r| {
                        elements[r]
                            .get("memberElement")
                            .cloned()
                            .filter(|v| v.get("@id").is_some())
                            .or_else(|| {
                                related_elems[r]
                                    .first()
                                    .map(|&k| id_ref(&eid(&elements[k])))
                            })
                    });
                if let Some(v) = target {
                    overrides.insert("referencedElement".into(), v);
                }
            }
            // ConjugatedPortTyping's type.
            "PortConjugation" => {
                if let Some(o) = rel_owner[i] {
                    let r = id_ref(&eid(&elements[o]));
                    derived.insert("conjugatedPortDefinition".into(), r.clone());
                    derived.insert("conjugatedType".into(), r);
                }
            }
            "ConjugatedPortTyping" => {
                if let Some(t) = elements[i].get("type").cloned().filter(|v| !v.is_null()) {
                    derived.insert("conjugatedPortDefinition".into(), t);
                }
            }
            "TransitionUsage" => {
                if let Some(succ) = owned_kids
                    .iter()
                    .find(|&&k| ty(&elements[k]) == "SuccessionAsUsage")
                {
                    derived.insert("succession".into(), id_ref(&eid(&elements[*succ])));
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
                    .map(|&k| id_ref(&eid(&elements[k])))
                    .collect();
                if !ends.is_empty() {
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
                if !flow_ends.is_empty() {
                    derived.insert(
                        "flowEnd".into(),
                        Value::Array(
                            flow_ends
                                .iter()
                                .map(|&k| id_ref(&eid(&elements[k])))
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
                            .map(|&f| id_ref(&eid(&elements[f])))
                    };
                    if let Some(v) = flow_ends.first().copied().and_then(feature_of) {
                        derived.insert("sourceOutputFeature".into(), v);
                    }
                    if let Some(v) = flow_ends.get(1).copied().and_then(feature_of) {
                        derived.insert("targetInputFeature".into(), v);
                    }
                }
                if let Some(&p) = owned_kids
                    .iter()
                    .find(|&&k| ty(&elements[k]) == "PayloadFeature")
                {
                    derived.insert("payloadFeature".into(), id_ref(&eid(&elements[p])));
                }
            }
            "AcceptActionUsage" => {
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
                    derived.insert("payloadParameter".into(), id_ref(&eid(&elements[p])));
                }
                if let Some(&r) = ref_params.get(1) {
                    if let Some(&a) = owned_rels[r]
                        .iter()
                        .find(|&&fv| ty(&elements[fv]) == "FeatureValue")
                        .and_then(|&fv| related_elems[fv].first())
                    {
                        derived.insert("receiverArgument".into(), id_ref(&eid(&elements[a])));
                    }
                }
            }
            "PerformActionUsage"
            | "EventOccurrenceUsage"
            | "ExhibitStateUsage"
            | "IncludeUseCaseUsage" => {
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
            "MetadataUsage" | "MetadataFeature" => {
                let explicit: Vec<Value> = owned_rels[i]
                    .iter()
                    .filter(|&&r| ty(&elements[r]) == "Annotation")
                    .filter_map(|&r| elements[r].get("annotatedElement").cloned())
                    .collect();
                let annotated = if explicit.is_empty() {
                    owner_idx
                        .map(|o| vec![id_ref(&eid(&elements[o]))])
                        .unwrap_or_default()
                } else {
                    explicit
                };
                derived.insert("annotatedElement".into(), Value::Array(annotated));
            }
            _ => {}
        }

        // Annotating elements: annotated/documented element defaults to
        // the owning element when no explicit `about` annotation exists.
        if matches!(
            t.as_str(),
            "Comment" | "Documentation" | "TextualRepresentation"
        ) {
            let explicit: Vec<Value> = owned_rels[i]
                .iter()
                .filter(|&&r| ty(&elements[r]) == "Annotation")
                .filter_map(|&r| elements[r].get("annotatedElement").cloned())
                .collect();
            let annotated = if explicit.is_empty() {
                owner_idx
                    .map(|o| vec![id_ref(&eid(&elements[o]))])
                    .unwrap_or_default()
            } else {
                explicit
            };
            if let Some(first) = annotated.first() {
                derived.insert("documentedElement".into(), first.clone());
                derived.insert("representedElement".into(), first.clone());
                derived.insert("annotation".into(), Value::Array(Vec::new()));
            }
            derived.insert("annotatedElement".into(), Value::Array(annotated));
        }
        if t == "MultiplicityRange" {
            let bounds: Vec<Value> = owned_rels[i]
                .iter()
                .filter(|&&r| ty(&elements[r]) == "OwningMembership")
                .flat_map(|&r| related_elems[r].iter().map(|&k| id_ref(&eid(&elements[k]))))
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
            if let Some(target) = elements[i].get("memberElement").cloned().or_else(|| {
                related_elems[i]
                    .first()
                    .map(|&k| id_ref(&eid(&elements[k])))
            }) {
                if let Some(id) = ref_of(&target) {
                    derived.insert("memberElementId".into(), Value::String(id.clone()));
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
            derived.insert(
                "membershipOwningNamespace".into(),
                rel_owner[i]
                    .map(|o| id_ref(&eid(&elements[o])))
                    .unwrap_or(Value::Null),
            );
        }

        // Overlay: computed derived values (only those the metaclass
        // declares — `additionalProperties: false`), then catalog defaults
        // for anything still missing.
        let el = &mut elements[i];
        el.insert("isImpliedIncluded".into(), json!(implied_included));
        if let Some(props) = catalog.get(t.as_str()) {
            let declared: std::collections::HashSet<&str> = props.iter().map(|(n, _)| *n).collect();
            for (k, v) in derived {
                if declared.contains(k.as_str()) {
                    el.entry(k).or_insert(v);
                }
            }
            for (k, v) in std::mem::take(&mut overrides) {
                if declared.contains(k.as_str()) {
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
            let self_id = el
                .get("@id")
                .and_then(|v| v.as_str())
                .unwrap_or("")
                .to_string();
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
                            json!({ "@id": self_id })
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
                .filter(|k| {
                    !k.starts_with('@') && !declared.contains(k.as_str()) && *k != "elementId"
                })
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
        .map(|(i, e)| (eid(e), i))
        .collect();
    fn collect_refs(v: &Value, out: &mut Vec<String>) {
        match v {
            Value::Object(m) => {
                if let Some(Value::String(s)) = m.get("@ref") {
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
        let root_id = eid(&elements[root]);
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
                // Deterministic dangling ID for unresolvable references.
                let id = Uuid::new_v5(&Uuid::NAMESPACE_OID, format!("unresolved:{s}").as_bytes());
                let id = id.to_string();
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
/// implicitly redefines the callee's `in` parameters in declaration order.
/// Only derivable when the callee is in-document; a feature owning any
/// Redefinition is a named argument and keeps that name (even unresolved).
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
    // The callee: the invocation's fn/type Membership target.
    let callee_id = owner_rels
        .iter()
        .find(|&&r| ty(&elements[r]) == "Membership")
        .and_then(|&r| elements[r].get("memberElement"))
        .and_then(ref_of)?;
    let callee = *index.get(&callee_id)?;
    let params: Vec<&str> = elements[callee]
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
        .filter(|&k| elements[k].get("direction").and_then(|v| v.as_str()) == Some("in"))
        .filter_map(|k| elements[k].get("declaredName").and_then(|v| v.as_str()))
        .collect();
    let pos = owner_rels
        .iter()
        .filter(|&&r| ty(&elements[r]) == "ParameterMembership")
        .position(|&r| r == rel)?;
    params.get(pos).map(|n| n.to_string())
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
) {
    let el = &elements[i];
    let t = ty(el);
    let owner = rel_owner[i].map(|o| id_ref(&eid(&elements[o])));
    let owned: Vec<Value> = related_elems[i]
        .iter()
        .map(|&k| id_ref(&eid(&elements[k])))
        .collect();
    let get = |k: &str| el.get(k).cloned().filter(|v| !v.is_null());

    let (source, target): (Vec<Value>, Vec<Value>) = if is_membership(t) {
        let target = get("memberElement")
            .or_else(|| owned.first().cloned())
            .into_iter()
            .collect();
        (owner.clone().into_iter().collect(), target)
    } else if is_import(t) {
        let target = get("importedNamespace")
            .or_else(|| get("importedMembership"))
            .into_iter()
            .collect();
        (owner.clone().into_iter().collect(), target)
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
                    .or(owner.clone());
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
                let target = get("annotatedElement").into_iter().collect();
                (owner.clone().into_iter().collect(), target)
            }
            "Conjugation" | "PortConjugation" => {
                let target = get("originalType").into_iter().collect();
                (owner.clone().into_iter().collect(), target)
            }
            "Disjoining" => {
                let source = get("typeDisjoined").or(owner.clone());
                let target = get("disjoiningType");
                (source.into_iter().collect(), target.into_iter().collect())
            }
            "FeatureInverting" => {
                let source = get("featureInverted").or(owner.clone());
                let target = get("invertingFeature");
                (source.into_iter().collect(), target.into_iter().collect())
            }
            "TypeFeaturing" => {
                let source = get("featureOfType").or(owner.clone());
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
                (owner.clone().into_iter().collect(), target)
            }
            _ => return, // not a relationship
        }
    };
    let mut related: Vec<Value> = source.clone();
    related.extend(target.clone());
    derived.insert("source".into(), Value::Array(source));
    derived.insert("target".into(), Value::Array(target));
    derived.insert("relatedElement".into(), Value::Array(related));
}

/// Materialize implied specializations per SysML 8.4.2 Tables 31/32: every
/// definition/usage kind implicitly specializes its library base unless an
/// explicit specialization of the covering kind is present
/// (anti-redundancy, approximated as "any explicit same-kind
/// specialization").
fn add_implied_relationships(
    elements: &mut Vec<Map<String, Value>>,
    lib_by_name: &HashMap<String, String>,
) {
    let mut additions: Vec<(usize, Map<String, Value>)> = Vec::new();
    for (i, el) in elements.iter().enumerate() {
        let t = ty(el).to_string();
        let own_id = eid(el);
        let rel_types: Vec<String> = el
            .get("ownedRelationship")
            .and_then(|v| v.as_array())
            .map(|a| {
                a.iter()
                    .filter_map(|r| r.get("@id").and_then(|x| x.as_str()))
                    .map(|s| s.to_string())
                    .collect()
            })
            .unwrap_or_default();
        let _ = rel_types;

        let (bases, rel_ty, src_key, tgt_key, covering): (&[&str], &str, &str, &str, &[&str]) =
            if let Some(kind) = def_kind_of(&t) {
                (
                    implicit_def_bases(kind),
                    "Subclassification",
                    "subclassifier",
                    "superclassifier",
                    &["Subclassification", "Specialization"],
                )
            } else if let Some(kind) = usage_kind_of(&t, Dialect::Sysml) {
                (
                    implicit_usage_bases(kind),
                    "Subsetting",
                    "subsettingFeature",
                    "subsettedFeature",
                    &["Subsetting", "Redefinition", "ReferenceSubsetting"],
                )
            } else {
                continue;
            };
        if bases.is_empty() {
            continue;
        }
        // Anti-redundancy: skip when an explicit covering specialization
        // exists (its general transitively reaches the implied base through
        // its own implied relationships).
        let ids: Vec<String> = el
            .get("ownedRelationship")
            .and_then(|v| v.as_array())
            .map(|a| a.iter().filter_map(ref_of).collect())
            .unwrap_or_default();
        let has_covering = ids.iter().any(|rid| {
            elements
                .iter()
                .find(|e| eid(e) == *rid)
                .map(|r| covering.contains(&ty(r)))
                .unwrap_or(false)
        });
        if has_covering {
            continue;
        }
        for (n, base) in bases.iter().enumerate() {
            let Some(base_id) = lib_by_name.get(*base) else {
                continue;
            };
            let rel_id = Uuid::new_v5(
                &Uuid::NAMESPACE_OID,
                format!("{own_id}/implied{n}").as_bytes(),
            )
            .to_string();
            let mut rel = Map::new();
            rel.insert("@type".into(), json!(rel_ty));
            rel.insert("@id".into(), json!(rel_id));
            rel.insert("elementId".into(), json!(rel_id));
            rel.insert("isImplied".into(), json!(true));
            rel.insert("isImpliedIncluded".into(), json!(true));
            rel.insert("ownedRelationship".into(), json!([]));
            rel.insert("ownedRelatedElement".into(), json!([]));
            rel.insert("owningRelatedElement".into(), id_ref(&own_id));
            rel.insert("owningRelationship".into(), Value::Null);
            rel.insert(src_key.into(), id_ref(&own_id));
            rel.insert(tgt_key.into(), id_ref(base_id));
            rel.insert("aliasIds".into(), json!([]));
            rel.insert("declaredName".into(), Value::Null);
            rel.insert("declaredShortName".into(), Value::Null);
            additions.push((i, rel));
        }
    }
    for (owner_idx, rel) in additions {
        let rel_id = eid(&rel);
        if let Some(Value::Array(rels)) = elements[owner_idx].get_mut("ownedRelationship") {
            rels.push(id_ref(&rel_id));
        }
        elements.push(rel);
    }
}
