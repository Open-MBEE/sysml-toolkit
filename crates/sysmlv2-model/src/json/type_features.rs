//! Ordered Type projections over the shared checked Membership provider.
use super::{
    ElementRef, ResolvedModel, TypeInputIssue, membership_evidence,
    membership_projection::Membership, semantic::certified_types::Stamp,
    structural_index::StoredStructure, type_relations::TypeRelations,
};
use crate::metaclass::conforms;
use std::collections::HashSet;

/// Complete projections for supported ordinary Types. These values
/// prove the selected membership domain, not whole-model validity. All vectors
/// preserve semantic order and are unique by element or relationship identity.
#[derive(Clone, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub struct TypeFeatures {
    pub owned_memberships: Vec<ElementRef>,
    pub inherited_memberships: Vec<ElementRef>,
    pub owned_feature_memberships: Vec<ElementRef>,
    pub feature_memberships: Vec<ElementRef>,
    pub features: Vec<ElementRef>,
    pub inherited_features: Vec<ElementRef>,
    pub inputs: Vec<ElementRef>,
    pub outputs: Vec<ElementRef>,
    pub directed_features: Vec<ElementRef>,
    pub end_features: Vec<ElementRef>,
    /// Root imports require a separate collision-pruned membership projection.
    /// The feature components remain usable when their visibility-specific
    /// inherited import contributions have complete shared evidence.
    pub memberships: Result<Vec<ElementRef>, TypeInputIssue>,
    pub members: Result<Vec<ElementRef>, TypeInputIssue>,
}
/// Complete ordered Type projections or an explicit qualification.
#[derive(Clone, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub struct TypeFeatureReport {
    pub projections: Result<TypeFeatures, TypeInputIssue>,
    pub steps: usize,
}
pub(super) struct MembershipSequence {
    pub owned: Vec<Membership>,
    pub inherited: Vec<Membership>,
    // Only populated by the operation projection, keeping ordinary query work unchanged.
    pub inheritable: Vec<Membership>,
    pub non_private: Vec<Membership>,
    pub root_import: bool,
    pub required_positional: std::collections::HashMap<usize, Vec<usize>>,
}
pub(super) fn supported_root(ty: &str) -> bool {
    matches!(
        ty,
        "Type"
            | "Feature"
            | "Classifier"
            | "Class"
            | "Structure"
            | "DataType"
            | "Behavior"
            | "Function"
            | "Definition"
            | "AttributeDefinition"
            | "OccurrenceDefinition"
            | "ItemDefinition"
            | "PartDefinition"
    )
}
fn charge(steps: &mut usize, n: usize) -> Result<(), TypeInputIssue> {
    *steps = steps.saturating_add(n);
    if *steps > crate::eval::MAX_STEPS {
        Err(TypeInputIssue::WorkLimit)
    } else {
        Ok(())
    }
}
impl ResolvedModel {
    /// Prove feature and membership projections for ordinary Kernel Types and
    /// nonindividual, nonvariation Definition, AttributeDefinition,
    /// OccurrenceDefinition, ItemDefinition and PartDefinition receivers.
    /// Required library roles, complete ancestry and inverse ownership are checked.
    /// Public/protected leaf-package imports share the central positional proof.
    /// Conjugation, broader import dependencies and contextual subclasses stay qualified.
    /// No relationships are published and compatibility projections are unchanged.
    pub fn type_feature_report(&mut self, receiver: ElementRef) -> TypeFeatureReport {
        self.type_feature_report_with_budget(receiver, 0)
    }
    pub(in crate::json) fn type_feature_report_with_budget(
        &mut self,
        receiver: ElementRef,
        initial: usize,
    ) -> TypeFeatureReport {
        let mut steps = initial;
        let mut projections = self.checked_type_features(receiver.0, &mut steps);
        if steps > crate::eval::MAX_STEPS {
            projections = Err(TypeInputIssue::WorkLimit);
        }
        TypeFeatureReport { projections, steps }
    }
    pub(super) fn checked_type_features(
        &mut self,
        receiver: usize,
        steps: &mut usize,
    ) -> Result<TypeFeatures, TypeInputIssue> {
        self.b.checked_type_features(receiver, steps)
    }
}

impl super::Builder {
    pub(super) fn checked_type_features(
        &mut self,
        receiver: usize,
        steps: &mut usize,
    ) -> Result<TypeFeatures, TypeInputIssue> {
        self.checked_type_features_with_relations(receiver, steps, &mut TypeRelations::default())
    }
    pub(super) fn checked_type_features_with_relations(
        &mut self,
        receiver: usize,
        steps: &mut usize,
        relations: &mut TypeRelations,
    ) -> Result<TypeFeatures, TypeInputIssue> {
        let sequence = self.checked_type_memberships_with_relations(receiver, steps, relations)?;
        let raw =
            StoredStructure::for_query(self, steps).ok_or(TypeInputIssue::IncompleteProvider)?;
        let stamp = Stamp::capture_builder(self);
        charge(
            steps,
            sequence
                .owned
                .len()
                .saturating_add(sequence.inherited.len())
                .saturating_mul(12),
        )?;
        let owned_memberships = sequence
            .owned
            .iter()
            .map(|m| ElementRef(m.relationship))
            .collect();
        let inherited_memberships = sequence
            .inherited
            .iter()
            .map(|m| ElementRef(m.relationship))
            .collect();
        let mut owned_feature_memberships = Vec::new();
        let mut feature_memberships = Vec::new();
        let mut features = Vec::new();
        let mut inherited_features = Vec::new();
        let mut inputs = Vec::new();
        let mut outputs = Vec::new();
        let mut directed_features = Vec::new();
        let mut end_features = Vec::new();
        let mut seen_relationships = HashSet::new();
        let mut seen_features = HashSet::new();
        let mut seen_inherited = HashSet::new();
        for (inherited, membership) in sequence
            .owned
            .iter()
            .map(|m| (false, m))
            .chain(sequence.inherited.iter().map(|m| (true, m)))
        {
            if !conforms(
                self.elements[membership.relationship].ty,
                "FeatureMembership",
            ) {
                continue;
            }
            if !inherited {
                owned_feature_memberships.push(ElementRef(membership.relationship));
            }
            if seen_relationships.insert(membership.relationship) {
                feature_memberships.push(ElementRef(membership.relationship));
            }
            let feature = ElementRef(membership.member);
            if inherited && seen_inherited.insert(feature) {
                inherited_features.push(feature);
            }
            if !seen_features.insert(feature) {
                continue;
            }
            features.push(feature);
            let direction = membership_evidence::parameter_direction(self, &raw, feature.0, steps)
                .ok_or(TypeInputIssue::InvalidRelationship)?;
            if matches!(direction, Some("in" | "inout")) {
                inputs.push(feature);
            }
            if matches!(direction, Some("out" | "inout")) {
                outputs.push(feature);
            }
            if direction.is_some() {
                directed_features.push(feature);
            }
            // The provider already shape-checked every contributing isEnd.
            if self.elements[feature.0]
                .props
                .get("isEnd")
                .and_then(|v| v.as_bool())
                == Some(true)
            {
                end_features.push(feature);
            }
        }
        let (memberships, members) = if sequence.root_import {
            (
                Err(TypeInputIssue::UnsupportedConfiguration),
                Err(TypeInputIssue::UnsupportedConfiguration),
            )
        } else {
            let mut seen_memberships = HashSet::new();
            let mut seen_members = HashSet::new();
            let mut memberships = Vec::new();
            let mut members = Vec::new();
            for m in sequence.owned.iter().chain(&sequence.inherited) {
                if seen_memberships.insert(m.relationship) {
                    memberships.push(ElementRef(m.relationship));
                }
                if seen_members.insert(m.member) {
                    members.push(ElementRef(m.member));
                }
            }
            (Ok(memberships), Ok(members))
        };
        if !stamp.current_builder(self) {
            return Err(TypeInputIssue::StaleEvidence);
        }
        Ok(TypeFeatures {
            owned_memberships,
            inherited_memberships,
            owned_feature_memberships,
            feature_memberships,
            features,
            inherited_features,
            inputs,
            outputs,
            directed_features,
            end_features,
            memberships,
            members,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        json::{ClosurePolicy, PropertyError},
        model::{GraphFormat, Model},
    };
    use serde_json::json;
    const LIB: &str = "standard library package Base { classifier Anything; datatype DataValue specializes Anything; feature things:Anything; } standard library package Occurrences { class Occurrence specializes Base::Anything; feature occurrences:Occurrence subsets Base::things; } standard library package Objects { struct Object specializes Occurrences::Occurrence; } standard library package Performances { behavior Performance specializes Occurrences::Occurrence; function Evaluation specializes Performance { return result; } step performances:Performance subsets Occurrences::occurrences; expr evaluations:Evaluation subsets performances; }";
    fn fixture(source: &str, format: GraphFormat) -> ResolvedModel {
        let mut m = Model::with_graph_format(format);
        assert!(
            m.add_library_source("types-library.kerml", LIB)
                .diagnostics
                .is_empty()
        );
        let unit = m.add_source("types.kerml", source);
        assert!(unit.diagnostics.is_empty(), "{:?}", unit.diagnostics);
        ResolvedModel::build(&m)
    }
    fn refs(r: &mut ResolvedModel, names: &[&str]) -> Vec<ElementRef> {
        names
            .iter()
            .map(|name| r.resolve_qualified(name).unwrap())
            .collect()
    }
    fn complete(r: &mut ResolvedModel, name: &str) -> TypeFeatures {
        let e = r.resolve_qualified(name).unwrap();
        r.type_feature_report(e).projections.unwrap()
    }
    fn full(r: &mut ResolvedModel) {
        r.set_closure_policy(ClosurePolicy::Closure {
            include_implied: true,
        });
    }

    #[test]
    fn shared_relation_evidence_preserves_features_and_refuses_changed_rows() {
        let mut r = fixture(
            "class A {feature a;} class B specializes A {feature b;}",
            GraphFormat::CanonicalV3,
        );
        let a = r.resolve_qualified("A").unwrap();
        let b = r.resolve_qualified("B").unwrap();
        let expected_a = r.type_feature_report(a).projections.unwrap();
        let expected_b = r.type_feature_report(b).projections.unwrap();
        let mut relations = TypeRelations::default();
        let mut steps = 0;
        assert_eq!(
            r.b.checked_type_features_with_relations(a.0, &mut steps, &mut relations),
            Ok(expected_a)
        );
        assert_eq!(
            r.b.checked_type_features_with_relations(b.0, &mut steps, &mut relations),
            Ok(expected_b.clone())
        );
        let feature = r.resolve_qualified("B::b").unwrap();
        r.b.elements[feature.0]
            .props
            .insert("direction", json!("in"));
        assert!(
            r.b.checked_type_features_with_relations(b.0, &mut steps, &mut relations)
                .is_err()
        );
        let refreshed = r.type_feature_report(b).projections.unwrap();
        assert_eq!(refreshed.features, expected_b.features);
        assert_eq!(refreshed.inputs, [feature]);
        let mut exhausted = crate::eval::MAX_STEPS;
        assert!(relations.reset_with_budget(&mut exhausted).is_none());
        relations.reset_with_budget(&mut 0).unwrap();
        assert_eq!(
            r.b.checked_type_features_with_relations(b.0, &mut 0, &mut relations),
            Ok(refreshed)
        );
    }

    #[test]
    fn every_plain_root_requires_canonical_bases_and_preserves_default_projections() {
        for format in [GraphFormat::LegacyV2, GraphFormat::CanonicalV3] {
            for keyword in [
                "type",
                "classifier",
                "class",
                "struct",
                "datatype",
                "behavior",
                "function",
            ] {
                let source = format!("{keyword} A {{in feature x; out feature y;}}");
                let mut r = fixture(&source, format);
                let a = r.resolve_qualified("A").unwrap();
                let old = r.derived(a, "feature");
                let count = r.b.elements.len();
                let p = r.type_feature_report(a).projections.unwrap();
                assert_eq!(p.inputs, refs(&mut r, &["A::x"]), "{keyword}");
                assert!(p.outputs.contains(&refs(&mut r, &["A::y"])[0]));
                assert_eq!(r.b.elements.len(), count);
                assert_eq!(r.derived(a, "feature"), old);
                full(&mut r);
                assert!(r.property(a, "feature").is_ok());
                assert!(r.property(a, "output").is_ok());
                if keyword != "function" {
                    assert_eq!(
                        r.function_result_report(a).result,
                        Err(TypeInputIssue::UnsupportedConfiguration)
                    );
                }
                let mut no_library = Model::with_graph_format(format);
                no_library.add_source("types.kerml", &source);
                let mut r = ResolvedModel::build(&no_library);
                let a = r.resolve_qualified("A").unwrap();
                assert!(r.type_feature_report(a).projections.is_err(), "{keyword}");
            }
        }
    }
    #[test]
    fn owned_private_and_inherited_memberships_keep_separate_ordered_domains() {
        let mut r = fixture(
            "class A { private feature hidden; protected feature guarded; in feature a; out feature b; end feature edge; feature plain; class Nested; } class B specializes A { private inout feature own; feature local; }",
            GraphFormat::LegacyV2,
        );
        let p = complete(&mut r, "B");
        assert_eq!(
            p.features,
            refs(
                &mut r,
                &[
                    "B::own",
                    "B::local",
                    "A::a",
                    "A::b",
                    "A::edge",
                    "A::plain",
                    "A::guarded"
                ]
            )
        );
        assert_eq!(p.inputs, refs(&mut r, &["B::own", "A::a"]));
        assert_eq!(p.outputs, refs(&mut r, &["B::own", "A::b"]));
        assert_eq!(
            p.directed_features,
            refs(&mut r, &["B::own", "A::a", "A::b"])
        );
        assert_eq!(p.end_features, refs(&mut r, &["A::edge"]));
        assert_eq!(p.inherited_features, p.features[2..]);
        assert_eq!(p.feature_memberships.len(), p.features.len());
        assert_eq!(p.owned_memberships.len(), 2);
        assert_eq!(p.inherited_memberships.len(), 6);
        assert!(
            p.members
                .as_ref()
                .unwrap()
                .contains(&refs(&mut r, &["A::Nested"])[0])
        );
        assert!(
            !p.members
                .as_ref()
                .unwrap()
                .contains(&refs(&mut r, &["A::hidden"])[0])
        );
        let a = complete(&mut r, "A");
        assert!(a.features.contains(&refs(&mut r, &["A::hidden"])[0]));
    }
    #[test]
    fn private_import_qualifies_only_the_receivers_all_membership_component() {
        let mut r = fixture(
            "package P {class T;} class A { private import P::*; in feature x; } class B specializes A;",
            GraphFormat::LegacyV2,
        );
        let a = complete(&mut r, "A");
        assert_eq!(a.inputs, refs(&mut r, &["A::x"]));
        assert!(a.memberships.is_err());
        assert!(a.members.is_err());
        let b = complete(&mut r, "B");
        assert!(b.memberships.is_ok());
        assert_eq!(b.inputs, a.inputs);
        full(&mut r);
        let a = r.resolve_qualified("A").unwrap();
        assert!(r.property(a, "input").is_ok());
        assert!(matches!(
            r.property(a, "membership"),
            Err(PropertyError::IncompleteTypeFeatures(_))
        ));
        let b = r.resolve_qualified("B").unwrap();
        assert!(r.property(b, "membership").is_ok());
    }
    #[test]
    fn aliases_are_memberships_without_becoming_feature_slots() {
        let mut r = fixture(
            "class A {feature x; alias other for x;} class B specializes A;",
            GraphFormat::LegacyV2,
        );
        let a = complete(&mut r, "A");
        assert_eq!(a.features, refs(&mut r, &["A::x"]));
        assert_eq!(a.memberships.unwrap().len(), 2);
        assert_eq!(a.members.unwrap().len(), 1);
        let b = complete(&mut r, "B");
        // The shared inherited-membership filter suppresses competing aliases
        // of the same Feature by its reflexive redefinition closure.
        assert!(b.feature_memberships.is_empty());
        assert!(b.features.is_empty());
    }
    #[test]
    fn malformed_suppressed_features_and_inverse_domains_refuse_complete_reports() {
        for field in ["direction", "isEnd"] {
            let mut r = fixture(
                "class A {in feature x;} class B specializes A {in feature y redefines x;}",
                GraphFormat::LegacyV2,
            );
            let b = r.resolve_qualified("B").unwrap();
            assert!(r.type_feature_report(b).projections.is_ok());
            let x = r.resolve_qualified("A::x").unwrap();
            r.b.set(x.0, field, json!(false));
            if field == "isEnd" {
                r.b.set(x.0, field, json!("bad"));
            }
            assert!(r.type_feature_report(b).projections.is_err());
        }
        let mut r = fixture(
            "class A {feature x;} class B specializes A;",
            GraphFormat::CanonicalV3,
        );
        let b = r.resolve_qualified("B").unwrap();
        assert!(r.type_feature_report(b).projections.is_ok());
        let a = r.resolve_qualified("A").unwrap();
        r.b.elements[a.0].owned_relationships = Vec::new().into();
        assert!(r.type_feature_report(b).projections.is_err());
    }
    #[test]
    fn diamond_preserves_membership_identity_and_own_then_inherited_order() {
        let mut r = fixture(
            "class A {in feature a; class Nested;} class B specializes A {feature b;} class C specializes A {feature c;} class D specializes B, C {private feature d;}",
            GraphFormat::CanonicalV3,
        );
        let p = complete(&mut r, "D");
        assert_eq!(p.features, refs(&mut r, &["D::d", "B::b", "A::a", "C::c"]));
        assert_eq!(p.inherited_features, p.features[1..]);
        assert_eq!(p.inputs, refs(&mut r, &["A::a"]));
        assert_eq!(p.feature_memberships.len(), 4);
        assert_eq!(p.inherited_memberships.len(), 4);
        assert_eq!(p.owned_memberships.len(), 1);
        let expected_members = refs(&mut r, &["D::d", "B::b", "A::a", "A::Nested", "C::c"]);
        assert_eq!(p.members, Ok(expected_members));
        let inherited: HashSet<_> = p.inherited_memberships.iter().collect();
        assert_eq!(inherited.len(), p.inherited_memberships.len());
        let root = r.resolve_qualified("D").unwrap();
        full(&mut r);
        for (property, expected) in [
            ("featureMembership", p.feature_memberships),
            ("inheritedMembership", p.inherited_memberships),
            ("membership", p.memberships.unwrap()),
        ] {
            assert_eq!(
                r.property(root, property).unwrap(),
                json!(
                    expected
                        .iter()
                        .map(|&e| json!({"@id":r.element_id(e)}))
                        .collect::<Vec<_>>()
                ),
                "{property}"
            );
        }
    }

    #[test]
    fn empty_complete_root_does_not_widen_to_contextual_subclasses() {
        let mut r = fixture("class Empty;", GraphFormat::LegacyV2);
        let e = r.resolve_qualified("Empty").unwrap();
        let complete = r.type_feature_report(e).projections.unwrap();
        assert!(complete.features.is_empty());
        assert_eq!(complete.memberships, Ok(vec![]));
        assert_eq!(complete.members, Ok(vec![]));
        // An ordinary unfeatured Feature now has the same complete empty
        // namespace projection. The same-ID kind edit must revalidate it.
        r.b.elements[e.0].ty = "Feature";
        assert_eq!(r.type_feature_report(e).projections, Ok(complete));
        for kind in ["Association", "Expression", "PartUsage", "Predicate"] {
            r.b.elements[e.0].ty = kind;
            assert_eq!(
                r.type_feature_report(e).projections,
                Err(TypeInputIssue::UnsupportedConfiguration),
                "{kind}"
            );
        }
        assert_eq!(
            r.type_feature_report(ElementRef(usize::MAX)).projections,
            Err(TypeInputIssue::InvalidElement)
        );
    }

    #[test]
    fn directions_end_flags_and_budget_are_current_and_retryable() {
        let mut r = fixture(
            "class A {out feature x; in feature y; feature z;}",
            GraphFormat::CanonicalV3,
        );
        let a = r.resolve_qualified("A").unwrap();
        let x = r.resolve_qualified("A::x").unwrap();
        let y = r.resolve_qualified("A::y").unwrap();
        let before = r.b.elements.len();
        let p = r.type_feature_report(a).projections.unwrap();
        assert_eq!(p.features[..2], [x, y]);
        r.b.set(x.0, "direction", json!("inout"));
        r.b.set(x.0, "isEnd", json!(true));
        let p = r.type_feature_report(a).projections.unwrap();
        assert_eq!(p.inputs, [x, y]);
        assert_eq!(p.outputs, [x]);
        assert_eq!(p.end_features, [x]);
        assert_eq!(
            r.type_feature_report_with_budget(a, crate::eval::MAX_STEPS)
                .projections,
            Err(TypeInputIssue::WorkLimit)
        );
        assert!(r.type_feature_report(a).projections.is_ok());
        assert_eq!(r.b.elements.len(), before);
        full(&mut r);
        assert_eq!(
            r.property(a, "input"),
            Ok(json!([{"@id":r.element_id(x)},{"@id":r.element_id(y)}]))
        );
        r.set_closure_policy(ClosurePolicy::Passthrough);
        assert_eq!(r.property(a, "feature"), Err(PropertyError::Approximate));
    }
}
