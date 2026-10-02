//! Bounded Usage variability over the shared specialization and ownership proof.
//! No stored derived bit or independent semantic graph supplies the answer.
use super::{
    Builder, ElementRef, ResolvedModel,
    structural_index::StoredStructure,
    type_relations::{RelationFact, TypeRelations},
};
use crate::metaclass::conforms;

/// Why Usage::mayTimeVary cannot be certified. Errors never mean false.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub enum UsageVariabilityIssue {
    WorkLimit,
    InvalidElement,
    InvalidOwnership,
    InvalidBoolean(&'static str),
    UnsupportedMetadata,
    UnsupportedConfiguration,
    MissingCanonicalRole(&'static str),
    IncompleteSpecialization,
}

/// A complete Usage variability value or an explicit qualification.
#[derive(Clone, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub struct UsageVariabilityReport {
    pub value: Result<bool, UsageVariabilityIssue>,
    /// Bounded logical work, including cold shared topology construction.
    pub steps: usize,
}
fn charge(steps: &mut usize, amount: usize) -> Result<(), UsageVariabilityIssue> {
    *steps = steps.saturating_add(amount);
    if *steps > crate::eval::MAX_STEPS {
        Err(UsageVariabilityIssue::WorkLimit)
    } else {
        Ok(())
    }
}

impl ResolvedModel {
    /// Read SysML Usage::mayTimeVary from complete identity evidence.
    ///
    /// Ordinary reference, attribute, occurrence, item and part Usages with
    /// witnessed required paths are supported. End Usages also require the
    /// complete shared ordered Membership/redefinition certificate. Independent
    /// exclusions or a proven null owning type can establish false in other
    /// contexts. Unsupported contextual families remain errors when relevant.
    /// This does not map textual end defaults or change owned isConstant.
    pub fn usage_variability_report(&mut self, usage: ElementRef) -> UsageVariabilityReport {
        self.usage_variability_report_with_budget(usage, 0)
    }

    pub(in crate::json) fn usage_variability_report_with_budget(
        &mut self,
        usage: ElementRef,
        initial_steps: usize,
    ) -> UsageVariabilityReport {
        let mut steps = initial_steps;
        let value = read(&mut self.b, usage.0, &mut steps);
        UsageVariabilityReport {
            value: if steps > crate::eval::MAX_STEPS {
                Err(UsageVariabilityIssue::WorkLimit)
            } else {
                value
            },
            steps,
        }
    }
}

fn boolean(b: &Builder, usage: usize, key: &'static str) -> Result<bool, UsageVariabilityIssue> {
    match b.elements[usage].props.get(key) {
        None => Ok(false),
        Some(value) => value
            .as_bool()
            .ok_or(UsageVariabilityIssue::InvalidBoolean(key)),
    }
}

fn specializes_role(
    b: &mut Builder,
    proof: &mut TypeRelations,
    source: usize,
    role: &'static str,
    steps: &mut usize,
) -> Result<RelationFact, UsageVariabilityIssue> {
    let target = proof
        .library_role(b, role, steps)
        .ok_or(UsageVariabilityIssue::MissingCanonicalRole(role))?;
    let fact = proof.specializes(b, source, target, steps);
    charge(steps, 0)?;
    Ok(fact)
}

fn read(b: &mut Builder, usage: usize, steps: &mut usize) -> Result<bool, UsageVariabilityIssue> {
    use UsageVariabilityIssue::*;
    charge(steps, 1)?;
    let row = b
        .elements
        .get(usage)
        .filter(|row| conforms(row.ty, "Usage"))
        .ok_or(InvalidElement)?;
    // Only this exact effective declaration is implemented, including through
    // its inherited spelling. Future redefinitions need their own capability.
    if crate::semantic_catalog::property(row.ty, "mayTimeVary")
        .and_then(|(_, effective)| effective)
        .is_none_or(|p| p.id != "Systems-DefinitionAndUsage-Usage-mayTimeVary")
    {
        return Err(UnsupportedConfiguration);
    }
    if b.positional_planning || !b.dynamic_evidence_current(usage) {
        return Err(UnsupportedConfiguration);
    }
    // Validate retained inputs before any decisive Boolean short circuit.
    // Derived aliases are shape-checked but never accepted as computed values.
    charge(steps, 5)?;
    let portion = boolean(b, usage, "isPortion")?;
    let composite = boolean(b, usage, "isComposite")?;
    for key in ["isEnd", "isVariable", "mayTimeVary"] {
        boolean(b, usage, key)?;
    }
    let structure = StoredStructure::for_annotations(b, steps).ok_or(InvalidOwnership)?;
    if !structure.ids_unique {
        return Err(InvalidElement);
    }
    if b.metadata_associations_incomplete
        || structure.annotations_incomplete
        || structure.metadata_annotation_targets.contains(&usage)
        || b.metadata_of.get(&usage).is_some_and(|v| !v.is_empty())
    {
        return Err(UnsupportedMetadata);
    }
    // Stored ownership must be reciprocal even for the null owningType case.
    // Orphan rows without a checked membership are outside this first domain.
    let membership = b.elements[usage]
        .owning_relationship
        .ok_or(InvalidOwnership)?;
    let carrier =
        super::semantic_ownership::checked_relationship_carrier(b, &structure, membership, steps)
            .flatten()
            .ok_or(InvalidOwnership)?;
    if super::membership_evidence::member(b, &structure, carrier, membership, steps) != Some(usage)
    {
        return Err(InvalidOwnership);
    }
    let mut proof = TypeRelations::default();
    let owner = proof.owning_type(b, usage, steps).ok_or(InvalidOwnership)?;
    if let Some(stored) = b.elements[usage].props.get("owningType") {
        let valid = match owner {
            Some(owner) => stored.as_reference() == Some(b.elements[owner].id),
            None => stored.is_null(),
        };
        if !valid {
            return Err(InvalidOwnership);
        }
    }
    if portion || owner.is_none() {
        return Ok(false);
    }
    let owner = owner.expect("non-null owning type");
    let occurrence = specializes_role(b, &mut proof, owner, "Occurrences::Occurrence", steps);
    if occurrence == Ok(RelationFact::No) {
        return Ok(false);
    }
    charge(steps, 0)?;
    // A positive exclusion can decide false independently of a missing role or
    // incomplete path elsewhere. Failure to find an exclusion never means No.
    let mut complete = occurrence == Ok(RelationFact::Yes);
    let mut issue = occurrence.err();
    for role in [
        "Links::SelfLink",
        "Occurrences::HappensLink",
        "Actions::Action",
    ] {
        if role == "Actions::Action" && !composite {
            continue;
        }
        match specializes_role(b, &mut proof, usage, role, steps) {
            Ok(RelationFact::Yes) => return Ok(false),
            Ok(RelationFact::No) => {}
            Ok(RelationFact::Unknown) => complete = false,
            Err(error) => {
                complete = false;
                issue.get_or_insert(error);
            }
        }
        charge(steps, 0)?;
    }
    if complete {
        Ok(true)
    } else {
        Err(issue.unwrap_or(IncompleteSpecialization))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        json::{ClosurePolicy, DerivedValue, PropertyError},
        model::Model,
    };
    use serde_json::{Value, json};
    use std::collections::HashMap;
    const LIB: &str = "standard library package Base {classifier Anything; feature things:Anything;} standard library package Occurrences {class Occurrence specializes Base::Anything; assoc HappensLink specializes Base::Anything;} standard library package Links {assoc SelfLink specializes Base::Anything;}";
    fn fixture(source: &str) -> ResolvedModel {
        let mut m = Model::new();
        assert!(
            m.add_library_source("roles.kerml", LIB)
                .diagnostics
                .is_empty()
        );
        assert!(
            m.add_library_source(
                "roles.sysml",
                "standard library package Actions { action def Action :> Occurrences::Occurrence; }"
            )
            .diagnostics
            .is_empty()
        );
        assert!(m.add_source("source.sysml", source).diagnostics.is_empty());
        let mut r = ResolvedModel::build(&m);
        r.set_closure_policy(ClosurePolicy::Closure {
            include_implied: true,
        });
        r
    }
    fn report(r: &mut ResolvedModel, name: &str) -> Result<bool, UsageVariabilityIssue> {
        let e = r.resolve_qualified(name).unwrap();
        r.usage_variability_report(e).value
    }
    fn remove_role(r: &mut ResolvedModel, role: &str) {
        r.b.lib_qnames =
            r.b.lib_qnames
                .iter()
                .filter(|(_, name)| name.join("::") != role)
                .cloned()
                .collect();
        r.b.supported_implied = None;
    }
    fn complete_end_model(format: crate::model::GraphFormat, source: &str) -> Model {
        let mut model = Model::with_graph_format(format);
        for (path, text) in [
            (
                "ends.kerml",
                "standard library package Base { classifier Anything; feature things : Anything; } standard library package Occurrences { class Occurrence specializes Base::Anything; feature occurrences : Occurrence subsets Base::things; assoc HappensLink specializes Base::Anything; } standard library package Objects { struct Object specializes Occurrences::Occurrence; feature objects : Object subsets Occurrences::occurrences; } standard library package Links { assoc SelfLink specializes Base::Anything; }",
            ),
            (
                "ends.sysml",
                "standard library package Items { item def Item :> Objects::Object; abstract ref item items : Item :> Objects::objects; } standard library package Parts { part def Part :> Items::Item; abstract ref part parts : Part :> Items::items; }",
            ),
        ] {
            let unit = model.add_library_source(path, text);
            assert!(unit.diagnostics.is_empty(), "{:?}", unit.diagnostics);
        }
        if !source.is_empty() {
            let unit = model.add_source("source.sysml", source);
            assert!(unit.diagnostics.is_empty(), "{:?}", unit.diagnostics);
        }
        model
    }
    #[test]
    fn ordinary_ends_use_complete_shared_order_and_redefinitions() {
        use crate::model::GraphFormat;
        for format in [GraphFormat::LegacyV2, GraphFormat::CanonicalV3] {
            let model = complete_end_model(
                format,
                "part def A { end ref alpha :> Base::things; end ref beta :> Base::things; } part def B :> A; part def C :> B { end ref x :> Base::things; end ref y :> Base::things; } part def D { end item typed : Items::Item; }",
            );
            let mut r = ResolvedModel::build(&model);
            r.set_closure_policy(ClosurePolicy::Closure {
                include_implied: true,
            });
            for name in ["A::alpha", "A::beta", "C::x", "C::y", "D::typed"] {
                let end = r.resolve_qualified(name).unwrap();
                assert_eq!(
                    r.usage_variability_report(end).value,
                    Ok(true),
                    "{format:?} {name}"
                );
                assert_eq!(r.property(end, "mayTimeVary"), Ok(json!(true)));
                if format == GraphFormat::CanonicalV3 {
                    assert_eq!(r.property(end, "isConstant"), Ok(json!(true)));
                    assert_eq!(
                        r.end_constancy_report(end).variable_end_is_constant,
                        Ok(true)
                    );
                }
            }
            let c = r.resolve_qualified("C").unwrap();
            let x = r.resolve_qualified("C::x").unwrap();
            let y = r.resolve_qualified("C::y").unwrap();
            assert_eq!(
                r.type_feature_report(c).projections.unwrap().end_features,
                [x, y]
            );
            let first = r.resolve_qualified("A::alpha").unwrap();
            r.b.set(first.0, "isEnd", json!("invalid"));
            assert!(r.usage_variability_report(x).value.is_err());
        }
    }

    #[test]
    fn end_completeness_refuses_inverse_ownership_and_unproved_individual_families() {
        use crate::model::GraphFormat;
        for mutation in 0..3 {
            let model = complete_end_model(
                GraphFormat::CanonicalV3,
                "part def P { end ref x :> Base::things; }",
            );
            let mut r = ResolvedModel::build(&model);
            let x = r.resolve_qualified("P::x").unwrap();
            let p = r.resolve_qualified("P").unwrap();
            assert_eq!(r.usage_variability_report(x).value, Ok(true));
            match mutation {
                0 => r.b.elements[p.0].owned_relationships = Vec::new().into(),
                1 => r.b.set(p.0, "isIndividual", json!(true)),
                _ => remove_role(&mut r, "Parts::Part"),
            }
            assert!(
                r.usage_variability_report(x).value.is_err(),
                "mutation{mutation}"
            );
            assert!(r.property(x, "isConstant").is_err(), "mutation{mutation}");
        }
    }

    #[test]
    fn canonical_positive_end_completion_replays_and_preserves_imported_flags() {
        use crate::{libcache::LibraryCache, model::GraphFormat, prepared::PreparedLibrary};
        use std::sync::Arc;
        let mut library = complete_end_model(GraphFormat::CanonicalV3, "");
        library.record_library_cache();
        ResolvedModel::build(&library);
        let cache =
            LibraryCache::from_bytes(&library.take_recorded_library_cache().unwrap().to_bytes())
                .unwrap();
        let prepared = library.prepare_library().unwrap();
        let decoded =
            Arc::new(PreparedLibrary::from_bytes(&prepared.to_bytes(191).unwrap(), 191).unwrap());
        for mode in 0..4 {
            let mut m = if mode < 2 {
                complete_end_model(GraphFormat::CanonicalV3, "")
            } else {
                Model::with_graph_format(GraphFormat::CanonicalV3)
            };
            match mode {
                1 => m.set_library_cache(cache.clone()),
                2 => Arc::clone(&prepared).install(&mut m).unwrap(),
                3 => Arc::clone(&decoded).install(&mut m).unwrap(),
                _ => {}
            }
            assert!(
                m.add_source(
                    "positive.sysml",
                    "part def P { end ref x :> Base::things; }"
                )
                .diagnostics
                .is_empty()
            );
            let mut r = ResolvedModel::build(&m);
            let x = r.resolve_qualified("P::x").unwrap();
            let before = r.element_properties(x);
            assert_eq!(r.usage_variability_report(x).value, Ok(true), "mode{mode}");
            assert_eq!(r.property(x, "isConstant"), Ok(json!(true)));
            assert_eq!(r.element_properties(x), before);
            assert!(matches!(
                r.usage_variability_report_with_budget(x, crate::eval::MAX_STEPS)
                    .value,
                Err(UsageVariabilityIssue::WorkLimit)
            ));
            assert_eq!(r.usage_variability_report(x).value, Ok(true));
            for mut doc in [
                super::super::model_to_compact_json(&m),
                crate::full::model_to_full_json(&m),
            ] {
                let row = doc
                    .as_array_mut()
                    .unwrap()
                    .iter_mut()
                    .find(|row| row["declaredName"] == "x")
                    .unwrap();
                assert_eq!(row["isConstant"], true, "mode{mode}");
                row["isConstant"] = json!(false);
                let (_, mut imported, _, _) = crate::loader::load_document_with_format(
                    &doc,
                    &HashMap::new(),
                    GraphFormat::CanonicalV3,
                )
                .unwrap();
                let x = imported.resolve_qualified("P::x").unwrap();
                assert!(!imported.canonical_text_end(x));
                assert_eq!(imported.property(x, "isConstant"), Ok(json!(false)));
            }
        }
    }

    #[test]
    fn ordinary_reference_is_positive_and_checked_aliases_share_declaration_dispatch() {
        let mut r = fixture("part def P :> Occurrences::Occurrence { ref x :> Base::things; }");
        let x = r.resolve_qualified("P::x").unwrap();
        let original = r.element_properties(x);
        assert_eq!(r.usage_variability_report(x).value, Ok(true));
        for name in ["mayTimeVary", "isVariable"] {
            assert_eq!(r.property(x, name), Ok(json!(true)));
            assert_eq!(r.derived_exact(x, name), Ok(DerivedValue::Bool(true)));
        }
        assert_eq!(r.element_properties(x), original);
        let xid = r.element_id(x);
        let issues = r.to_full_json_strict().unwrap_err().issues;
        assert!(
            !issues.iter().any(|i| i.element_id == xid
                && matches!(i.property.as_str(), "mayTimeVary" | "isVariable"))
        );
        // Retained derived aliases are never treated as computed answers.
        r.b.set(x.0, "mayTimeVary", json!(false));
        r.b.set(x.0, "isVariable", json!(false));
        assert_eq!(r.usage_variability_report(x).value, Ok(true));
        remove_role(&mut r, "Actions::Action");
        assert_eq!(r.usage_variability_report(x).value, Ok(true));
        r.set_closure_policy(ClosurePolicy::Passthrough);
        assert_eq!(
            r.property(x, "mayTimeVary"),
            Err(PropertyError::Approximate)
        );
    }
    #[test]
    fn null_owner_and_each_positive_exclusion_decide_false_independently() {
        let mut m = Model::new();
        m.add_source("root.sysml", "ref x;");
        let mut r = ResolvedModel::build(&m);
        assert_eq!(report(&mut r, "x"), Ok(false));
        let mut r = fixture("part def P { ref x :> Base::things; }");
        let x = r.resolve_qualified("P::x").unwrap();
        r.b.set(x.0, "isPortion", json!(true));
        r.b.lib_qnames = Default::default();
        r.b.supported_implied = None;
        assert_eq!(r.usage_variability_report(x).value, Ok(false));
        for role in [
            "Links::SelfLink",
            "Occurrences::HappensLink",
            "Actions::Action",
        ] {
            let mut r = fixture(&format!("part def P {{ ref x : {role}; }}"));
            let x = r.resolve_qualified("P::x").unwrap();
            if role == "Actions::Action" {
                r.b.set(x.0, "isComposite", json!(true));
            }
            remove_role(&mut r, "Occurrences::Occurrence");
            assert_eq!(r.usage_variability_report(x).value, Ok(false), "{role}");
        }
    }
    #[test]
    fn malformed_inputs_precede_false_short_circuits_and_exhaustion_precedes_all_results() {
        for key in [
            "isPortion",
            "isComposite",
            "isEnd",
            "isVariable",
            "mayTimeVary",
        ] {
            for bad in [
                Value::Null,
                json!("true"),
                json!([]),
                json!({"@id":uuid::Uuid::nil()}),
            ] {
                let mut r = fixture("ref x;");
                let x = r.resolve_qualified("x").unwrap();
                r.b.set(x.0, key, bad);
                assert_eq!(
                    r.usage_variability_report(x).value,
                    Err(UsageVariabilityIssue::InvalidBoolean(key))
                );
                assert_eq!(
                    r.usage_variability_report_with_budget(x, crate::eval::MAX_STEPS)
                        .value,
                    Err(UsageVariabilityIssue::WorkLimit)
                );
            }
        }
        let mut r = fixture("part def P :> Occurrences::Occurrence {ref x :> Base::things;}");
        let x = r.resolve_qualified("P::x").unwrap();
        r.by_id.clear();
        r.by_id_built_for = usize::MAX;
        assert_eq!(
            r.usage_variability_report_with_budget(x, crate::eval::MAX_STEPS - 2)
                .value,
            Err(UsageVariabilityIssue::WorkLimit)
        );
        assert!(r.by_id.is_empty());
        assert_eq!(r.usage_variability_report(x).value, Ok(true));
        assert!(r.by_id.is_empty());
    }
    #[test]
    fn missing_wrong_kind_duplicate_and_external_roles_never_certify_absence() {
        for mode in 0..4 {
            let mut r = fixture("part def P :> Occurrences::Occurrence {ref x :> Base::things;}");
            let target = r.resolve_qualified("Links::SelfLink").unwrap();
            match mode {
                0 => remove_role(&mut r, "Links::SelfLink"),
                1 => r.b.elements[target.0].ty = "Class",
                2 => r.b.lib_qnames.push((
                    uuid::Uuid::new_v4(),
                    vec!["Links".into(), "SelfLink".into()],
                )),
                _ => {
                    remove_role(&mut r, "Links::SelfLink");
                    r.set_library_names(&HashMap::from([(
                        uuid::Uuid::new_v4().to_string(),
                        vec!["Links".into(), "SelfLink".into()],
                    )]));
                }
            }
            assert_eq!(
                report(&mut r, "P::x"),
                Err(UsageVariabilityIssue::MissingCanonicalRole(
                    "Links::SelfLink"
                )),
                "mode {mode}"
            );
        }
    }
    #[test]
    fn end_missing_family_metadata_and_bad_ownership_remain_qualified() {
        for source in [
            "part def P { ref x; }",
            "part def P { end x :> Base::things; }",
        ] {
            let mut r = fixture(source);
            assert_eq!(
                report(&mut r, "P::x"),
                Err(UsageVariabilityIssue::IncompleteSpecialization)
            );
        }
        let mut r = fixture("ref x;");
        let x = r.resolve_qualified("x").unwrap();
        r.b.metadata_associations_incomplete = true;
        assert_eq!(
            r.usage_variability_report(x).value,
            Err(UsageVariabilityIssue::UnsupportedMetadata)
        );
        r.b.metadata_associations_incomplete = false;
        let membership = r.b.elements[x.0].owning_relationship.unwrap();
        r.b.elements[membership].children = Vec::new().into();
        assert_eq!(
            r.usage_variability_report(x).value,
            Err(UsageVariabilityIssue::InvalidOwnership)
        );
        let mut r = fixture("ref x; ref duplicate;");
        let x = r.resolve_qualified("x").unwrap();
        let other = r.resolve_qualified("duplicate").unwrap();
        r.b.elements[other.0].id = r.b.elements[x.0].id;
        assert_eq!(
            r.usage_variability_report(x).value,
            Err(UsageVariabilityIssue::InvalidElement)
        );
    }
    #[test]
    fn contradictory_membership_aliases_refuse_before_any_boolean_result() {
        for source in [
            "ref x; ref other;",
            "part def P :> Occurrences::Occurrence {ref x :> Base::things; ref other;}",
        ] {
            for key in [
                "owningRelationship",
                "owningMembership",
                "owningFeatureMembership",
            ] {
                let mut r = fixture(source);
                let nested = source.starts_with("part");
                if key == "owningFeatureMembership" && !nested {
                    continue;
                }
                let x = r
                    .resolve_qualified(if nested { "P::x" } else { "x" })
                    .unwrap();
                let other = r
                    .resolve_qualified(if nested { "P::other" } else { "other" })
                    .unwrap();
                assert_eq!(r.usage_variability_report(x).value, Ok(nested));
                let wrong = r.b.elements[other.0].owning_relationship.unwrap();
                let wrong = r.b.elements[wrong].id;
                r.b.set(x.0, key, json!({"@id":wrong}));
                assert_eq!(
                    r.usage_variability_report(x).value,
                    Err(UsageVariabilityIssue::InvalidOwnership),
                    "{key}: {source}"
                );
            }
        }
    }

    #[test]
    fn row_identity_names_and_reference_changes_cannot_reuse_old_answers() {
        let mut r = fixture("part def P :> Occurrences::Occurrence {ref x :> Base::things;}");
        let x = r.resolve_qualified("P::x").unwrap();
        assert_eq!(r.usage_variability_report(x).value, Ok(true));
        r.override_ids(&HashMap::from([(r.element_id(x), uuid::Uuid::new_v4())]));
        assert_eq!(r.usage_variability_report(x).value, Ok(true));
        r.b.set(x.0, "isComposite", json!(true));
        assert!(r.usage_variability_report(x).value.is_err());
        r.b.set(x.0, "isComposite", json!(false));
        assert_eq!(r.usage_variability_report(x).value, Ok(true));
        r.b.positional_planning = true;
        assert_eq!(
            r.usage_variability_report(x).value,
            Err(UsageVariabilityIssue::UnsupportedConfiguration)
        );
        r.b.positional_planning = false;
        let subset = r.b.elements[x.0]
            .owned_relationships
            .iter()
            .copied()
            .find(|&e| conforms(r.b.elements[e].ty, "Subsetting"))
            .unwrap();
        r.b.set(subset, "subsettedFeature", json!({"@ref":"Missing"}));
        assert!(r.usage_variability_report(x).value.is_err());
    }
    #[test]
    fn real_library_true_false_and_refusal_replay_without_changing_source_ids() {
        use crate::{libcache::LibraryCache, prepared::PreparedLibrary};
        use std::sync::Arc;
        let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../../spec-refs/SysML-v2-Release/sysml.library");
        for format in [
            crate::model::GraphFormat::LegacyV2,
            crate::model::GraphFormat::CanonicalV3,
        ] {
            let mut library = Model::with_graph_format(format);
            library.load_library_dir(&path).unwrap();
            library.record_library_cache();
            ResolvedModel::build(&library);
            let cache = LibraryCache::from_bytes(
                &library.take_recorded_library_cache().unwrap().to_bytes(),
            )
            .unwrap();
            let prepared = library.prepare_library().unwrap();
            let decoded = Arc::new(
                PreparedLibrary::from_bytes(&prepared.to_bytes(115).unwrap(), 115).unwrap(),
            );
            let mut expected = None;
            for mode in 0..4 {
                let mut m = Model::with_graph_format(format);
                match mode {
                    2 => Arc::clone(&prepared).install(&mut m).unwrap(),
                    3 => Arc::clone(&decoded).install(&mut m).unwrap(),
                    _ => {
                        m.load_library_dir(&path).unwrap();
                        if mode == 1 {
                            m.set_library_cache(cache.clone());
                        }
                    }
                }
                assert!(m.add_source("usage.sysml","ref top; part def P {ref x :> Base::things; ref defaultRef; ref selfLink : Links::SelfLink; end item e;} occurrence def Q {end ref z :> Base::things;} part def MissingType {end item unresolved : Missing;}").diagnostics.is_empty());
                let mut r = ResolvedModel::build(&m);
                r.set_closure_policy(ClosurePolicy::Closure {
                    include_implied: true,
                });
                let ids: Vec<_> = r.user_elements().map(|e| r.element_id(e)).collect();
                if let Some(expected) = &expected {
                    assert_eq!(&ids, expected);
                } else {
                    expected = Some(ids.clone());
                }
                for (name, value) in [
                    ("top", false),
                    ("P::x", true),
                    ("P::defaultRef", true),
                    ("P::selfLink", false),
                    ("P::e", true),
                    ("Q::z", true),
                ] {
                    let e = r.resolve_qualified(name).unwrap();
                    assert_eq!(
                        r.usage_variability_report(e).value,
                        Ok(value),
                        "mode {mode}: {name}"
                    );
                    for property in ["mayTimeVary", "isVariable"] {
                        assert_eq!(r.property(e, property), Ok(json!(value)));
                    }
                }
                let end = r.resolve_qualified("P::e").unwrap();
                let unresolved = r.resolve_qualified("MissingType::unresolved").unwrap();
                assert!(r.usage_variability_report(unresolved).value.is_err());
                if format == crate::model::GraphFormat::LegacyV2 {
                    assert_eq!(
                        r.property(end, "isConstant"),
                        Err(PropertyError::NotComputed)
                    );
                } else {
                    assert_eq!(r.property(end, "isConstant"), Ok(json!(true)));
                    assert!(r.property(unresolved, "isConstant").is_err());
                    let proven = r.resolve_qualified("Q::z").unwrap();
                    assert_eq!(r.property(proven, "isConstant"), Ok(json!(true)));
                }
                assert_eq!(
                    ids,
                    r.user_elements()
                        .map(|e| r.element_id(e))
                        .collect::<Vec<_>>()
                );
            }
        }
    }
}
