//! Checked canonical constructor arguments over the shared complete Type feature sequence.
use super::{
    ElementRef, ResolvedModel, TypeInputIssue, membership_evidence,
    semantic::certified_types::Stamp, semantic_ownership, structural_index::StoredStructure,
    type_relations,
};
use crate::metaclass::conforms;
use std::collections::{HashMap, HashSet};

/// A supplied argument and the exact public feature it directly redefines.
#[derive(Clone, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub struct ConstructorBinding {
    pub feature: ElementRef,
    pub parameter: ElementRef,
    pub value: ElementRef,
}
/// Complete supplied arguments in public instantiated-Type feature order.
/// Omitted features remain in `features` without a binding; defaults, arity and
/// result specialization are separate obligations.
#[derive(Clone, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub struct ConstructorBindings {
    pub instantiated_type: ElementRef,
    pub result: ElementRef,
    pub features: Vec<ElementRef>,
    pub bindings: Vec<ConstructorBinding>,
}
/// A failed proof never denotes an empty argument list.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub enum ConstructorBindingIssue {
    InvalidElement,
    InvalidRelationship,
    IncompleteFeatures(TypeInputIssue),
    IncompleteProvider,
    UnsupportedConfiguration,
    UnmappedArgument,
    DuplicateArgument,
    StaleEvidence,
    WorkLimit,
}
#[derive(Clone, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub struct ConstructorBindingReport {
    pub arguments: Result<ConstructorBindings, ConstructorBindingIssue>,
    pub steps: usize,
}
use ConstructorBindingIssue::*;
fn charge(steps: &mut usize, n: usize) -> Result<(), ConstructorBindingIssue> {
    *steps = steps.saturating_add(n);
    if *steps > crate::eval::MAX_STEPS {
        Err(WorkLimit)
    } else {
        Ok(())
    }
}
/// Authoritative constructor selector and sole owned result, independent of
/// whether supplied arguments or the result specialization can be certified.
#[derive(Clone, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub struct ConstructorSelection {
    pub instantiated_type: ElementRef,
    pub result: ElementRef,
}
#[derive(Clone, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub struct ConstructorSelectionReport {
    pub selection: Result<ConstructorSelection, ConstructorBindingIssue>,
    pub steps: usize,
}
impl ResolvedModel {
    pub fn constructor_selection_report(
        &mut self,
        receiver: ElementRef,
    ) -> ConstructorSelectionReport {
        self.constructor_selection_report_with_budget(receiver, 0)
    }
    pub(in crate::json) fn constructor_selection_report_with_budget(
        &mut self,
        receiver: ElementRef,
        initial: usize,
    ) -> ConstructorSelectionReport {
        let mut steps = initial;
        let selection = (|| {
            charge(&mut steps, 1)?;
            if self.b.graph_format != crate::model::GraphFormat::CanonicalV3
                || self.b.elements.get(receiver.0).ok_or(InvalidElement)?.ty
                    != "ConstructorExpression"
                || self.b.positional_planning
            {
                return Err(UnsupportedConfiguration);
            }
            let raw =
                StoredStructure::for_query(&mut self.b, &mut steps).ok_or(IncompleteProvider)?;
            let instantiated_type = membership_evidence::first_unowned_member(
                &mut self.b,
                &raw,
                receiver.0,
                "FeatureMembership",
                "Type",
                None,
                &mut steps,
            )
            .ok_or(InvalidRelationship)?;
            let result =
                owned_result(&self.b, &raw, receiver.0, &mut steps).ok_or(InvalidRelationship)?;
            // Local syntax selection does not establish the complete effective
            // result family when metadata contributions are unavailable.
            if raw.annotations_incomplete
                || self.b.metadata_associations_incomplete
                || [receiver.0, result].into_iter().any(|element| {
                    raw.metadata_annotation_targets.contains(&element)
                        || self
                            .b
                            .metadata_of
                            .get(&element)
                            .is_some_and(|m| !m.is_empty())
                })
            {
                return Err(IncompleteProvider);
            }
            Ok(ConstructorSelection {
                instantiated_type: ElementRef(instantiated_type),
                result: ElementRef(result),
            })
        })();
        ConstructorSelectionReport {
            selection: if steps > crate::eval::MAX_STEPS {
                Err(WorkLimit)
            } else {
                selection
            },
            steps,
        }
    }
    /// Certify supplied canonical constructor arguments in complete public
    /// instantiated-Type feature order. Named bindings use checked authored
    /// Redefinitions; positional bindings require the shared published plan.
    /// Omitted features are allowed. Default and result obligations have separate
    /// reports; this does not certify whole-model conformance.
    pub fn constructor_binding_report(&mut self, receiver: ElementRef) -> ConstructorBindingReport {
        self.constructor_binding_report_with_budget(receiver, 0)
    }
    pub(in crate::json) fn constructor_binding_report_with_budget(
        &mut self,
        receiver: ElementRef,
        initial: usize,
    ) -> ConstructorBindingReport {
        let mut steps = initial;
        let arguments = self
            .b
            .checked_constructor_bindings(receiver.0, &mut steps, None);
        ConstructorBindingReport {
            arguments: if steps > crate::eval::MAX_STEPS {
                Err(WorkLimit)
            } else {
                arguments
            },
            steps,
        }
    }
}
/// Query-local successful Type projections shared across one constructor batch.
/// A source/publication change discards the complete cache before any reuse.
#[derive(Default)]
pub(super) struct ConstructorBatchEvidence {
    stamp: Option<Stamp>,
    features: HashMap<usize, super::TypeFeatures>,
    numeric_targets: HashMap<&'static str, usize>,
    relations: super::type_relations::TypeRelations,
}
fn projection_work(features: &super::TypeFeatures) -> usize {
    [
        features.owned_memberships.len(),
        features.inherited_memberships.len(),
        features.owned_feature_memberships.len(),
        features.feature_memberships.len(),
        features.features.len(),
        features.inherited_features.len(),
        features.inputs.len(),
        features.outputs.len(),
        features.directed_features.len(),
        features.end_features.len(),
        features.memberships.as_ref().map_or(0, Vec::len),
        features.members.as_ref().map_or(0, Vec::len),
    ]
    .into_iter()
    .fold(1usize, usize::saturating_add)
}
impl ConstructorBatchEvidence {
    fn align(
        &mut self,
        b: &mut super::Builder,
        steps: &mut usize,
    ) -> Result<(), ConstructorBindingIssue> {
        if self
            .stamp
            .as_ref()
            .is_some_and(|stamp| stamp.current_builder(b))
        {
            return Ok(());
        }
        charge(
            steps,
            self.features
                .capacity()
                .saturating_add(self.numeric_targets.capacity()),
        )?;
        self.relations.reset_with_budget(steps).ok_or(WorkLimit)?;
        self.features = HashMap::new();
        self.numeric_targets = HashMap::new();
        self.stamp = Some(Stamp::capture_builder(b));
        Ok(())
    }
    pub(super) fn numeric_target(
        &mut self,
        b: &mut super::Builder,
        receiver: usize,
        steps: &mut usize,
    ) -> Option<usize> {
        let operator = super::invocation_bindings::numeric_operator_name(b, receiver)?;
        self.align(b, steps).ok()?;
        if let Some(&target) = self.numeric_targets.get(operator) {
            charge(steps, 1).ok()?;
            return Some(target);
        }
        let target = super::invocation_bindings::numeric_operator_target(b, receiver, steps)?;
        self.align(b, steps).ok()?;
        self.numeric_targets.insert(operator, target);
        Some(target)
    }
    pub(super) fn features(
        &mut self,
        b: &mut super::Builder,
        callee: usize,
        steps: &mut usize,
    ) -> Result<super::TypeFeatures, ConstructorBindingIssue> {
        self.align(b, steps)?;
        if let Some(features) = self.features.get(&callee) {
            charge(steps, projection_work(features))?;
            return Ok(features.clone());
        }
        let result = b.checked_type_features_with_relations(callee, steps, &mut self.relations);
        // Even a failed projection may have prepared semantic state. Facts
        // survive only under the same before/after authority; top-level failed
        // projections themselves are never memoized.
        self.align(b, steps)?;
        let features = result.map_err(IncompleteFeatures)?;
        charge(steps, projection_work(&features))?;
        self.features.insert(callee, features.clone());
        Ok(features)
    }
}

impl super::Builder {
    pub(super) fn checked_constructor_bindings(
        &mut self,
        receiver: usize,
        steps: &mut usize,
        proposed: Option<&mut HashMap<usize, Vec<usize>>>,
    ) -> Result<ConstructorBindings, ConstructorBindingIssue> {
        self.checked_constructor_bindings_in_batch(
            receiver,
            steps,
            proposed,
            &mut ConstructorBatchEvidence::default(),
        )
    }
    pub(super) fn checked_constructor_bindings_in_batch(
        &mut self,
        receiver: usize,
        steps: &mut usize,
        mut proposed: Option<&mut HashMap<usize, Vec<usize>>>,
        batch: &mut ConstructorBatchEvidence,
    ) -> Result<ConstructorBindings, ConstructorBindingIssue> {
        charge(steps, 1)?;
        if self.elements.get(receiver).ok_or(InvalidElement)?.ty != "ConstructorExpression"
            || self.graph_format != crate::model::GraphFormat::CanonicalV3
            || self.positional_planning
        {
            return Err(UnsupportedConfiguration);
        }
        let raw = StoredStructure::for_query(self, steps).ok_or(IncompleteProvider)?;
        let callee = membership_evidence::first_unowned_member(
            self,
            &raw,
            receiver,
            "FeatureMembership",
            "Type",
            None,
            steps,
        )
        .ok_or(InvalidRelationship)?;
        let features = batch.features(self, callee, steps)?.features;
        // Callee preparation may change shared semantic state. Capture all local
        // evidence afterward and recheck the selector against this same snapshot.
        let raw = StoredStructure::for_query(self, steps).ok_or(IncompleteProvider)?;
        if membership_evidence::first_unowned_member(
            self,
            &raw,
            receiver,
            "FeatureMembership",
            "Type",
            None,
            steps,
        ) != Some(callee)
        {
            return Err(StaleEvidence);
        }
        let domains = raw
            .membership_domains(self, steps)
            .ok_or(IncompleteProvider)?;
        let inverse = raw.typing(self, steps).ok_or(IncompleteProvider)?;
        if !raw.ids_unique
            || raw.annotations_incomplete
            || inverse.sources_incomplete
            || self.metadata_associations_incomplete
            || !domains.owner_complete(receiver)
            || raw.metadata_annotation_targets.contains(&receiver)
            || self
                .metadata_of
                .get(&receiver)
                .is_some_and(|m| !m.is_empty())
            || !semantic_ownership::owned_feature_projection_complete(self, receiver)
        {
            return Err(IncompleteProvider);
        }
        let result = owned_result(self, &raw, receiver, steps).ok_or(InvalidRelationship)?;
        if !domains.owner_complete(result)
            || raw.metadata_annotation_targets.contains(&result)
            || self.metadata_of.get(&result).is_some_and(|m| !m.is_empty())
        {
            return Err(IncompleteProvider);
        }
        let stamp = Stamp::capture_builder(self);
        charge(steps, features.len())?;
        let mut public_features = Vec::new();
        for feature in features {
            let membership = self.elements[feature.0]
                .owning_relationship
                .ok_or(InvalidRelationship)?;
            let visibility = match self.elements[membership].props.get("visibility") {
                None => "public",
                Some(value) => value.as_str().ok_or(InvalidRelationship)?,
            };
            match visibility {
                "public" => public_features.push(feature),
                "private" | "protected" => {}
                _ => return Err(InvalidRelationship),
            }
        }
        let eligible: HashSet<_> = public_features.iter().map(|e| e.0).collect();
        let relationships =
            semantic_ownership::owned_relationships(self, result).ok_or(IncompleteProvider)?;
        charge(steps, relationships.len())?;
        let relationships: Vec<_> = relationships.iter().collect();
        let mut seen = HashSet::new();
        let mut mapped = HashMap::new();

        let mut position = 0;
        for relationship in relationships {
            if !seen.insert(relationship)
                || semantic_ownership::checked_relationship_carrier(self, &raw, relationship, steps)
                    != Some(Some(result))
            {
                return Err(InvalidRelationship);
            }
            let kind = self.elements[relationship].ty;
            if !conforms(kind, "FeatureMembership") {
                continue;
            }
            let parameter = membership_evidence::member(self, &raw, result, relationship, steps)
                .ok_or(InvalidRelationship)?;
            if !domains.owner_complete(parameter)
                || raw.metadata_annotation_targets.contains(&parameter)
                || self
                    .metadata_of
                    .get(&parameter)
                    .is_some_and(|m| !m.is_empty())
                || self.elements[parameter].ty != "Feature"
            {
                return Err(IncompleteProvider);
            }
            let direction = membership_evidence::parameter_direction(self, &raw, parameter, steps)
                .ok_or(InvalidRelationship)?;
            let valuation = membership_evidence::valuation(self, &raw, parameter, steps)
                .ok_or(InvalidRelationship)?;
            if kind != "ParameterMembership" || direction != Some("in") {
                return Err(UnsupportedConfiguration);
            }
            let (value_membership, value) = valuation.ok_or(UnmappedArgument)?;
            for key in ["isInitial", "isDefault"] {
                if self.elements[value_membership]
                    .props
                    .get(key)
                    .and_then(|v| v.as_bool())
                    == Some(true)
                {
                    return Err(UnsupportedConfiguration);
                }
            }
            let owned = semantic_ownership::owned_relationships(self, parameter)
                .ok_or(IncompleteProvider)?;
            charge(steps, owned.len())?;
            let owned: Vec<_> = owned.iter().collect();
            let mut target = None;
            let mut witnessed = HashSet::new();
            for rel in owned.iter().copied().chain(
                inverse
                    .relationships
                    .get(&parameter)
                    .into_iter()
                    .flatten()
                    .copied(),
            ) {
                charge(steps, 1)?;
                if !witnessed.insert(rel) {
                    continue;
                }
                let row = &self.elements[rel];
                // Extra owned features, conjugation or value-affecting metadata
                // require a broader provider; do not silently drop them.
                if conforms(row.ty, "FeatureMembership")
                    || conforms(row.ty, "Conjugation")
                    || (rel < self.explicit_len()
                        && conforms(row.ty, "Specialization")
                        && !conforms(row.ty, "Redefinition"))
                {
                    return Err(UnsupportedConfiguration);
                }
                if !conforms(row.ty, "Redefinition") {
                    continue;
                }
                if target.is_some() {
                    return Err(UnsupportedConfiguration);
                }
                if !owned.contains(&rel)
                    || semantic_ownership::checked_relationship_carrier(self, &raw, rel, steps)
                        != Some(Some(parameter))
                    || !self.static_chain_row_current(rel)
                    || !self.result_redefinition_row_current(rel)
                {
                    return Err(InvalidRelationship);
                }
                let implied = match row.props.get("isImplied") {
                    None => false,
                    Some(v) => v.as_bool().ok_or(InvalidRelationship)?,
                };
                let mapped_input = type_relations::endpoint_with_carrier(
                    self,
                    parameter,
                    Some(parameter),
                    rel,
                    &["specific", "subsettingFeature", "redefiningFeature"],
                    &["general", "subsettedFeature", "redefinedFeature"],
                    "Feature",
                    steps,
                )
                .ok_or(InvalidRelationship)?;
                if !eligible.contains(&mapped_input) {
                    return Err(UnmappedArgument);
                }
                if implied {
                    if rel < self.explicit_len()
                        || public_features.get(position) != Some(&ElementRef(mapped_input))
                        || !self.semantic_ownership.as_ref().is_some_and(|view| {
                            view.matches_suffix(self)
                                && view.generated_relationship_owner(rel) == Some(parameter)
                        })
                    {
                        return Err(UnsupportedConfiguration);
                    }
                    let plan = self.effective_dynamic_plan().ok_or(StaleEvidence)?;
                    let targets = plan
                        .positional
                        .targets
                        .get(&parameter)
                        .ok_or(UnmappedArgument)?;
                    charge(steps, targets.len().saturating_add(1))?;
                    if !plan.affected_owners.contains(&parameter)
                        || plan.incomplete_bases.contains(&result)
                        || plan.positional.incomplete.contains(&result)
                        || targets.as_slice() != [mapped_input]
                    {
                        return Err(IncompleteProvider);
                    }
                } else if rel >= self.explicit_len() {
                    return Err(InvalidRelationship);
                }
                target = Some(mapped_input);
            }
            let input = if let Some(target) = target {
                target
            } else if let Some(proposed) = proposed.as_deref_mut() {
                let target = public_features.get(position).ok_or(UnmappedArgument)?.0;
                proposed.insert(parameter, vec![target]);
                target
            } else {
                return Err(UnmappedArgument);
            };
            position += 1;
            if mapped
                .insert(
                    input,
                    ConstructorBinding {
                        feature: ElementRef(input),
                        parameter: ElementRef(parameter),
                        value: ElementRef(value),
                    },
                )
                .is_some()
            {
                return Err(DuplicateArgument);
            }
        }
        charge(steps, public_features.len())?;
        let bindings = public_features
            .iter()
            .filter_map(|i| mapped.remove(&i.0))
            .collect();
        if !stamp.current_builder(self) {
            return Err(StaleEvidence);
        }
        Ok(ConstructorBindings {
            instantiated_type: ElementRef(callee),
            result: ElementRef(result),
            features: public_features,
            bindings,
        })
    }
}

/// Canonical authored result selected through complete reciprocal ownership.
/// This is deliberately independent of binding and specialization preparation.
pub(super) fn owned_result(
    b: &super::Builder,
    raw: &StoredStructure,
    receiver: usize,
    steps: &mut usize,
) -> Option<usize> {
    charge(steps, 1).ok()?;
    if b.graph_format != crate::model::GraphFormat::CanonicalV3
        || b.elements.get(receiver)?.ty != "ConstructorExpression"
        || !raw.membership_domains(b, steps)?.owner_complete(receiver)
        || !semantic_ownership::owned_feature_projection_complete(b, receiver)
    {
        return None;
    }
    let relationships = semantic_ownership::owned_relationships(b, receiver)?;
    charge(steps, relationships.len()).ok()?;
    let mut result = None;
    let mut seen = HashSet::new();
    for relationship in relationships.iter() {
        if !seen.insert(relationship)
            || semantic_ownership::checked_relationship_carrier(b, raw, relationship, steps)?
                != Some(receiver)
        {
            return None;
        }
        if !conforms(b.elements[relationship].ty, "FeatureMembership") {
            continue;
        }
        if b.elements[relationship].ty != "ReturnParameterMembership" || result.is_some() {
            return None;
        }
        let feature = membership_evidence::member(b, raw, receiver, relationship, steps)?;
        if b.elements[feature].ty != "Feature"
            || membership_evidence::parameter_direction(b, raw, feature, steps)? != Some("out")
            || membership_evidence::valuation(b, raw, feature, steps)?.is_some()
        {
            return None;
        }
        result = Some(feature);
    }
    result
}

/// An effective omitted default, selected by checked redefinition identity.
#[derive(Clone, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub struct ConstructorDefaultBinding {
    pub feature: ElementRef,
    pub feature_with_value: ElementRef,
    pub valuation: ElementRef,
    pub value: ElementRef,
}
#[derive(Clone, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub struct ConstructorDefaultReport {
    pub defaults: Result<Vec<ConstructorDefaultBinding>, ConstructorBindingIssue>,
    pub steps: usize,
}
impl ResolvedModel {
    /// Prove omitted effective defaults separately from supplied arguments.
    /// Conflicting defaults, cycles and unsupported contributions are qualified.
    pub fn constructor_default_report(&mut self, receiver: ElementRef) -> ConstructorDefaultReport {
        let mut steps = 0;
        let defaults = (|| {
            let arguments = self
                .b
                .checked_constructor_bindings(receiver.0, &mut steps, None)?;
            self.b.checked_constructor_defaults(&arguments, &mut steps)
        })();
        ConstructorDefaultReport {
            defaults: if steps > crate::eval::MAX_STEPS {
                Err(WorkLimit)
            } else {
                defaults
            },
            steps,
        }
    }
}
impl super::Builder {
    pub(super) fn checked_constructor_defaults(
        &mut self,
        arguments: &ConstructorBindings,
        steps: &mut usize,
    ) -> Result<Vec<ConstructorDefaultBinding>, ConstructorBindingIssue> {
        self.checked_constructor_defaults_in_batch(
            arguments,
            steps,
            &mut ConstructorBatchEvidence::default(),
        )
    }
    pub(super) fn checked_constructor_defaults_in_batch(
        &mut self,
        arguments: &ConstructorBindings,
        steps: &mut usize,
        batch: &mut ConstructorBatchEvidence,
    ) -> Result<Vec<ConstructorDefaultBinding>, ConstructorBindingIssue> {
        let features = batch
            .features(self, arguments.instantiated_type.0, steps)?
            .features;
        let retained = self
            .retained_typing_edges(steps)
            .ok_or(IncompleteProvider)?;
        let raw = StoredStructure::for_query(self, steps).ok_or(IncompleteProvider)?;
        let inverse = raw.typing(self, steps).ok_or(IncompleteProvider)?;
        if !raw.ids_unique
            || raw.annotations_incomplete
            || inverse.sources_incomplete
            || self.metadata_associations_incomplete
        {
            return Err(IncompleteProvider);
        }
        let stamp = Stamp::capture_builder(self);
        charge(steps, arguments.bindings.len())?;
        let supplied: HashSet<_> = arguments.bindings.iter().map(|b| b.feature.0).collect();
        let mut defaults = Vec::new();
        let mut memo = HashMap::new();
        for feature in features {
            charge(steps, 1)?;
            if supplied.contains(&feature.0) {
                continue;
            }
            if let Some((owner, valuation, value)) = self.constructor_effective_default(
                feature.0,
                &raw,
                &retained,
                &mut memo,
                &mut HashSet::new(),
                steps,
            )? {
                defaults.push(ConstructorDefaultBinding {
                    feature,
                    feature_with_value: ElementRef(owner),
                    valuation: ElementRef(valuation),
                    value: ElementRef(value),
                });
            }
        }
        if !stamp.current_builder(self) {
            return Err(StaleEvidence);
        }
        Ok(defaults)
    }
    #[allow(clippy::too_many_arguments)]
    fn constructor_effective_default(
        &mut self,
        feature: usize,
        raw: &StoredStructure,
        retained: &super::implied::RetainedTypings,
        memo: &mut HashMap<usize, Option<(usize, usize, usize)>>,
        active: &mut HashSet<usize>,
        steps: &mut usize,
    ) -> Result<Option<(usize, usize, usize)>, ConstructorBindingIssue> {
        charge(steps, 1)?;
        if let Some(value) = memo.get(&feature) {
            return Ok(*value);
        }
        if active.len() >= super::MAX_RESOLUTION_DEPTH || !active.insert(feature) {
            return Err(IncompleteProvider);
        }
        if raw.metadata_annotation_targets.contains(&feature)
            || self
                .metadata_of
                .get(&feature)
                .is_some_and(|m| !m.is_empty())
            || !raw
                .membership_domains(self, steps)
                .ok_or(IncompleteProvider)?
                .owner_complete(feature)
        {
            return Err(IncompleteProvider);
        }
        let valuation =
            membership_evidence::valuation(self, raw, feature, steps).ok_or(InvalidRelationship)?;
        let inverse = raw.typing(self, steps).ok_or(IncompleteProvider)?;
        let owned =
            semantic_ownership::owned_relationships(self, feature).ok_or(IncompleteProvider)?;
        charge(steps, owned.len())?;
        let owned: Vec<_> = owned.iter().collect();
        let mut targets = Vec::new();
        let mut seen = HashSet::new();
        for relationship in owned.iter().copied().chain(
            inverse
                .relationships
                .get(&feature)
                .into_iter()
                .flatten()
                .copied(),
        ) {
            charge(steps, 1)?;
            if !seen.insert(relationship) {
                continue;
            }
            let kind = self.elements[relationship].ty;
            if conforms(kind, "Conjugation") {
                return Err(UnsupportedConfiguration);
            }
            if !conforms(kind, "Redefinition") {
                continue;
            }
            if !owned.contains(&relationship)
                || semantic_ownership::checked_relationship_carrier(self, raw, relationship, steps)
                    != Some(Some(feature))
                || !self.static_chain_row_current(relationship)
                || !self.result_redefinition_row_current(relationship)
            {
                return Err(InvalidRelationship);
            }
            let target = type_relations::endpoint_with_carrier(
                self,
                feature,
                Some(feature),
                relationship,
                &["specific", "subsettingFeature", "redefiningFeature"],
                &["general", "subsettedFeature", "redefinedFeature"],
                "Feature",
                steps,
            )
            .ok_or(InvalidRelationship)?;
            targets.push(target);
        }
        if let Some(implied) = retained.get(&feature) {
            charge(steps, implied.len())?;
            for &(kind, id) in implied {
                if conforms(kind, "Redefinition") {
                    targets.push(raw.element_for_uuid(self, id).ok_or(IncompleteProvider)?);
                }
            }
        }
        // A complete shared positional plan can imply redefinitions before
        // physical materialization. These identities belong to the same
        // provider used by Type.feature, never an independent lexical search.
        if let Some(plan) = self.effective_dynamic_plan() {
            if plan.positional.incomplete.contains(&feature) {
                return Err(IncompleteProvider);
            }
            if let Some(implied) = plan.positional.targets.get(&feature) {
                charge(steps, implied.len())?;
                targets.extend(implied);
            }
        } else if let Some(plan) = &self.positional_redefinitions {
            if plan.incomplete.contains(&feature) {
                return Err(IncompleteProvider);
            }
            if let Some(implied) = plan.targets.get(&feature) {
                charge(steps, implied.len())?;
                targets.extend(implied);
            }
        } else {
            return Err(IncompleteProvider);
        }
        let mut inherited = HashSet::new();
        for target in targets {
            if let Some(candidate) =
                self.constructor_effective_default(target, raw, retained, memo, active, steps)?
            {
                inherited.insert(candidate);
            }
        }
        let selected = if let Some((membership, value)) = valuation {
            self.elements[membership]
                .props
                .get("isDefault")
                .and_then(|v| v.as_bool())
                .unwrap_or(false)
                .then_some((feature, membership, value))
        } else {
            if inherited.len() > 1 {
                return Err(UnsupportedConfiguration);
            }
            inherited.into_iter().next()
        };
        active.remove(&feature);
        memo.insert(feature, selected);
        Ok(selected)
    }
}

/// Certified constructor-result obligations in the supported graph domain.
#[derive(Clone, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub struct ConstructorResult {
    pub arguments: ConstructorBindings,
    pub defaults: Vec<ConstructorDefaultBinding>,
}
#[derive(Clone, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub struct ConstructorResultReport {
    pub result: Result<ConstructorResult, ConstructorBindingIssue>,
    pub steps: usize,
}
impl ResolvedModel {
    /// Check result specialization, unique public supplied bindings and all
    /// supported omitted-default BindingConnector obligations. This does not
    /// assert unrelated expression or whole-model validation constraints.
    pub fn constructor_result_report(&mut self, receiver: ElementRef) -> ConstructorResultReport {
        let mut steps = 0;
        let result = (|| {
            let arguments = self
                .b
                .checked_constructor_bindings(receiver.0, &mut steps, None)?;
            let defaults = self
                .b
                .checked_constructor_defaults(&arguments, &mut steps)?;
            let stamp = Stamp::capture(self);
            let mut relations = type_relations::TypeRelations::default();
            if relations.specializes(
                &mut self.b,
                arguments.result.0,
                arguments.instantiated_type.0,
                &mut steps,
            ) != type_relations::RelationFact::Yes
            {
                return Err(IncompleteProvider);
            }
            for default in &defaults {
                if !super::owned_results::constructor_default_present(
                    &mut self.b,
                    arguments.result.0,
                    default,
                    &mut steps,
                ) {
                    return Err(IncompleteProvider);
                }
            }
            if !stamp.current(self) {
                return Err(StaleEvidence);
            }
            Ok(ConstructorResult {
                arguments,
                defaults,
            })
        })();
        ConstructorResultReport {
            result: if steps > crate::eval::MAX_STEPS {
                Err(WorkLimit)
            } else {
                result
            },
            steps,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        json::ClosurePolicy,
        model::{GraphFormat, Model},
    };
    const LIB: &str = "standard library package Base {classifier Anything; feature things:Anything;} standard library package Occurrences {class Occurrence specializes Base::Anything; feature occurrences:Occurrence subsets Base::things;} standard library package Performances {behavior Performance specializes Occurrences::Occurrence; function Evaluation specializes Performance {return result;} step performances:Performance subsets Occurrences::occurrences; expr evaluations:Evaluation subsets performances;}";
    fn fixture(source: &str, format: GraphFormat) -> (ResolvedModel, ElementRef) {
        let mut model = Model::with_graph_format(format);
        assert!(
            model
                .add_library_source("constructor-library.kerml", LIB)
                .diagnostics
                .is_empty()
        );
        let parsed = model.add_source("constructors.kerml", source);
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let r = ResolvedModel::build(&model);
        let expression = ElementRef(
            r.b.elements
                .iter()
                .position(|e| e.ty == "ConstructorExpression")
                .unwrap(),
        );
        (r, expression)
    }
    #[test]
    fn named_arguments_follow_public_type_features_including_undirected_and_output() {
        for arguments in ["b=2,a=1", "b=2", ""] {
            let (mut r, expression) = fixture(
                &format!(
                    "class C {{ feature a; out feature b; private feature hidden; }} feature x = new C({arguments});"
                ),
                GraphFormat::CanonicalV3,
            );
            let a = r.resolve_qualified("C::a").unwrap();
            let b = r.resolve_qualified("C::b").unwrap();
            let report = r.constructor_binding_report(expression).arguments.unwrap();
            assert_eq!(report.features, [a, b]);
            let expected = match arguments {
                "" => vec![],
                "b=2" => vec![b],
                _ => vec![a, b],
            };
            assert_eq!(
                report
                    .bindings
                    .iter()
                    .map(|b| b.feature)
                    .collect::<Vec<_>>(),
                expected
            );
            r.set_closure_policy(ClosurePolicy::Closure {
                include_implied: true,
            });
            assert_eq!(
                r.property(expression, "argument")
                    .unwrap()
                    .as_array()
                    .unwrap()
                    .len(),
                report.bindings.len()
            );
            assert_eq!(
                r.property(expression, "result").unwrap(),
                serde_json::json!({"@id":r.element_id(report.result)})
            );
            assert_eq!(
                r.property(expression, "instantiatedType").unwrap(),
                serde_json::json!({"@id":r.element_id(report.instantiated_type)})
            );
        }
    }
    #[test]
    fn inherited_features_and_omissions_keep_complete_order() {
        let (mut r, expression) = fixture(
            "class A {feature a; feature b;} class C specializes A; feature x = new C(b=2);",
            GraphFormat::CanonicalV3,
        );
        let b = r.resolve_qualified("A::b").unwrap();
        let report = r.constructor_binding_report(expression).arguments.unwrap();
        assert_eq!(report.bindings.len(), 1);
        assert_eq!(report.bindings[0].feature, b);
    }
    #[test]
    fn full_export_uses_the_same_supplied_argument_order_including_omissions() {
        for arguments in ["b=2", "b=2,a=1", ""] {
            let mut model = Model::with_graph_format(GraphFormat::CanonicalV3);
            model.add_library_source("constructor-library.kerml", LIB);
            model.add_source(
                "constructors.kerml",
                &format!("class C {{feature a; out feature b;}} feature call=new C({arguments});"),
            );
            let mut r = ResolvedModel::build(&model);
            let expression = r
                .user_elements()
                .find(|&e| r.element_type(e) == "ConstructorExpression")
                .unwrap();
            let report = r.constructor_binding_report(expression).arguments.unwrap();
            let values: Vec<_> = report
                .bindings
                .iter()
                .map(|binding| serde_json::json!({"@id":r.element_id(binding.value)}))
                .collect();
            let full = crate::full::model_to_full_json(&model);
            let row = full
                .as_array()
                .unwrap()
                .iter()
                .find(|row| row["@type"] == "ConstructorExpression")
                .unwrap();
            assert_eq!(row["argument"], serde_json::json!(values), "{arguments}");
        }
    }
    #[test]
    fn canonical_full_carrier_defaults_do_not_overwrite_explicit_payload_values() {
        let mut model = Model::with_graph_format(GraphFormat::CanonicalV3);
        model.add_source("constructors.kerml", "class C; feature call=new C();");
        let original = crate::json::model_to_compact_json(&model);
        let membership = original
            .as_array()
            .unwrap()
            .iter()
            .find(|row| row["@type"] == "ReturnParameterMembership")
            .unwrap();
        let result_id = membership["ownedRelatedElement"][0]["@id"]
            .as_str()
            .unwrap();
        for stored in [
            None,
            Some(serde_json::Value::Null),
            Some(serde_json::json!(false)),
            Some(serde_json::json!("malformed")),
        ] {
            let mut compact = original.clone();
            if let Some(value) = stored.clone() {
                compact
                    .as_array_mut()
                    .unwrap()
                    .iter_mut()
                    .find(|row| row["@id"] == result_id)
                    .unwrap()["isUnique"] = value;
            }
            let mut r = ResolvedModel::build(&model);
            let full = crate::full::resolved_compact_to_full_json(
                &mut r,
                &model,
                compact,
                crate::full::EmissionPolicy::default(),
            )
            .unwrap();
            let result = full
                .as_array()
                .unwrap()
                .iter()
                .find(|row| row["@id"] == result_id)
                .unwrap();
            assert_eq!(
                result["isUnique"],
                stored.unwrap_or(serde_json::json!(true))
            );
        }
    }
    #[test]
    fn private_duplicate_unknown_and_positional_arguments_are_qualified() {
        for arguments in ["hidden=1", "a=1,a=2", "missing=1", "1"] {
            let (mut r, expression) = fixture(
                &format!(
                    "class C {{feature a; private feature hidden;}} feature x=new C({arguments});"
                ),
                GraphFormat::CanonicalV3,
            );
            assert!(
                r.constructor_binding_report(expression).arguments.is_err(),
                "{arguments}"
            );
            assert!(r.constructor_selection_report(expression).selection.is_ok());
        }
    }
    #[test]
    fn positional_arguments_use_admitted_public_feature_order() {
        for (declarations, arguments, names) in [
            (
                "class C {private feature hidden; feature a; out feature b;}",
                "1,2",
                vec!["C::a", "C::b"],
            ),
            (
                "class A {feature a; feature b;} class C specializes A;",
                "1,2",
                vec!["A::a", "A::b"],
            ),
            ("class C {feature a; feature b;}", "1", vec!["C::a"]),
        ] {
            let (mut r, expression) = fixture(
                &format!("{declarations} feature x=new C({arguments});"),
                GraphFormat::CanonicalV3,
            );
            assert!(r.constructor_binding_report(expression).arguments.is_err());
            let expected: Vec<_> = names
                .iter()
                .map(|name| r.resolve_qualified(name).unwrap())
                .collect();
            let _ = r.implied_relationships(expression);
            let report = r.constructor_binding_report(expression).arguments.unwrap();
            assert_eq!(
                report
                    .bindings
                    .iter()
                    .map(|b| b.feature)
                    .collect::<Vec<_>>(),
                expected
            );
            assert_eq!(
                r.model_level_evaluability(expression).classification,
                crate::json::ModelLevelEvaluability::Evaluable
            );
        }
    }
    #[test]
    fn constructor_evaluability_uses_complete_shared_arguments() {
        use crate::json::ModelLevelEvaluability::{Evaluable, NotEvaluable, Unknown};
        for arguments in ["", "b=2", "b=2,a=1"] {
            let (mut r, expression) = fixture(
                &format!("class C {{feature a; feature b;}} feature x=new C({arguments});"),
                GraphFormat::CanonicalV3,
            );
            assert_eq!(
                r.model_level_evaluability(expression).classification,
                Evaluable
            );
            if let Some(binding) = r
                .constructor_binding_report(expression)
                .arguments
                .unwrap()
                .bindings
                .first()
            {
                r.b.elements[binding.value.0].ty = "CalculationUsage";
                assert_eq!(
                    r.model_level_evaluability(expression).classification,
                    NotEvaluable
                );
            }
        }
        for arguments in ["missing=1", "a=1,a=2", "1,2,3"] {
            let (mut r, expression) = fixture(
                &format!("class C {{feature a; feature b;}} feature x=new C({arguments});"),
                GraphFormat::CanonicalV3,
            );
            let _ = r.implied_relationships(expression);
            assert!(matches!(
                r.model_level_evaluability(expression).classification,
                Unknown(_)
            ));
        }
    }
    #[test]
    fn omitted_defaults_publish_checked_binding_connectors_under_result() {
        for (declarations, arguments, expected) in [
            ("class C {feature a default = 1; feature b;}", "", 1),
            (
                "class C {private feature hidden default = 1; feature a;}",
                "",
                1,
            ),
            ("class C {feature a = 1;}", "", 0),
            ("class C {feature a default = 1; feature b;}", "a=2", 0),
            (
                "class A {feature a default = 1;} class C specializes A;",
                "",
                1,
            ),
            (
                "class A {feature a default = 1;} class C specializes A {feature b redefines a;}",
                "",
                1,
            ),
            (
                "class A {feature a default = 1;} class C specializes A {feature b redefines a = 2;}",
                "",
                0,
            ),
        ] {
            let (mut r, expression) = fixture(
                &format!("{declarations} feature x=new C({arguments});"),
                GraphFormat::CanonicalV3,
            );
            let defaults = r.constructor_default_report(expression).defaults.unwrap();
            assert_eq!(defaults.len(), expected, "{declarations}");
            assert!(r.constructor_result_report(expression).result.is_err());
            let _ = r.implied_relationships(expression);
            let result = r.constructor_result_report(expression).result.unwrap();
            assert_eq!(result.defaults, defaults);
            assert_eq!(
                r.model_level_evaluability(expression).classification,
                crate::json::ModelLevelEvaluability::Evaluable
            );
            if let Some(default) = defaults.first() {
                let valuation = default.valuation.0;
                r.b.elements[valuation]
                    .props
                    .insert("isDefault", serde_json::Value::Null);
                assert!(r.constructor_default_report(expression).defaults.is_err());
                assert!(r.constructor_result_report(expression).result.is_err());
            }
        }
    }
    #[test]
    fn conflicting_and_cyclic_default_paths_are_not_first_found_guesses() {
        for declarations in [
            "class C {feature a default = 1; feature b default = 2; feature c redefines a, b;}",
            "class C {feature a redefines b; feature b redefines a;}",
        ] {
            let (mut r, expression) = fixture(
                &format!("{declarations} feature x=new C();"),
                GraphFormat::CanonicalV3,
            );
            assert!(r.constructor_default_report(expression).defaults.is_err());
            let _ = r.implied_relationships(expression);
            assert!(r.constructor_result_report(expression).result.is_err());
        }
    }
    #[test]
    fn constructor_obligations_replay_across_prepared_library_paths() {
        use crate::{libcache::LibraryCache, prepared::PreparedLibrary};
        use std::sync::Arc;
        let mut base = Model::with_graph_format(GraphFormat::CanonicalV3);
        base.add_library_source("constructor-library.kerml", LIB);
        base.record_library_cache();
        ResolvedModel::build(&base);
        let cache =
            LibraryCache::from_bytes(&base.take_recorded_library_cache().unwrap().to_bytes())
                .unwrap();
        let prepared = base.prepare_library().unwrap();
        let decoded =
            Arc::new(PreparedLibrary::from_bytes(&prepared.to_bytes(143).unwrap(), 143).unwrap());
        let mut expected = None;
        for mode in 0..4 {
            let mut m = Model::with_graph_format(GraphFormat::CanonicalV3);
            match mode {
                2 => Arc::clone(&prepared).install(&mut m).unwrap(),
                3 => Arc::clone(&decoded).install(&mut m).unwrap(),
                _ => {
                    m.add_library_source("constructor-library.kerml", LIB);
                    if mode == 1 {
                        m.set_library_cache(cache.clone());
                    }
                }
            }
            m.add_source(
                "constructors.kerml",
                "class C {feature a; feature b default = 2;} feature x=new C(1);",
            );
            let mut r = ResolvedModel::build(&m);
            let expression = r
                .elements()
                .find(|&e| r.element_type(e) == "ConstructorExpression")
                .unwrap();
            let full = crate::full::resolved_to_full_json(&mut r, &m, Default::default()).unwrap();
            let report = r.constructor_result_report(expression).result.unwrap();
            assert_eq!(report.arguments.bindings.len(), 1);
            assert_eq!(report.defaults.len(), 1);
            let ids = (
                r.element_id(report.arguments.bindings[0].feature),
                r.element_id(report.defaults[0].value),
            );
            if let Some(expected) = expected {
                assert_eq!(ids, expected);
            } else {
                expected = Some(ids);
            }
            assert_eq!(
                crate::full::resolved_to_full_json(&mut r, &m, Default::default()).unwrap(),
                full
            );
        }
    }
    #[test]
    fn constructor_batch_reuses_success_and_rejects_same_length_source_changes() {
        let (mut r, expression) = fixture(
            "class C {feature a;} feature x=new C(1);",
            GraphFormat::CanonicalV3,
        );
        let mut batch = ConstructorBatchEvidence::default();
        let mut steps = 0;
        let first =
            r.b.checked_constructor_bindings_in_batch(
                expression.0,
                &mut steps,
                Some(&mut HashMap::new()),
                &mut batch,
            )
            .unwrap();
        let cold = steps;
        steps = 0;
        assert_eq!(
            r.b.checked_constructor_bindings_in_batch(
                expression.0,
                &mut steps,
                Some(&mut HashMap::new()),
                &mut batch
            )
            .unwrap(),
            first
        );
        assert!(steps < cold);
        let member = r.b.elements[first.features[0].0]
            .owning_relationship
            .unwrap();
        r.b.elements[member]
            .props
            .insert("visibility", serde_json::json!("private"));
        assert!(
            r.b.checked_constructor_bindings_in_batch(
                expression.0,
                &mut 0,
                Some(&mut HashMap::new()),
                &mut batch
            )
            .is_err()
        );
    }
    #[test]
    fn legacy_constructor_shape_is_not_reinterpreted() {
        let (mut r, expression) = fixture(
            "class C {feature a;} feature x = new C(a=1);",
            GraphFormat::LegacyV2,
        );
        assert_eq!(
            r.constructor_binding_report(expression).arguments,
            Err(UnsupportedConfiguration)
        );
        assert_eq!(
            r.constructor_selection_report(expression).selection,
            Err(UnsupportedConfiguration)
        );
    }

    #[test]
    fn selected_result_refuses_incomplete_or_targeted_metadata() {
        for mode in 0..3 {
            let (mut r, expression) =
                fixture("class C; feature call=new C();", GraphFormat::CanonicalV3);
            let result = r
                .constructor_selection_report(expression)
                .selection
                .unwrap()
                .result;
            match mode {
                0 => r.b.metadata_associations_incomplete = true,
                1 => {
                    r.b.metadata_of.insert(expression.0, vec![expression.0]);
                }
                _ => {
                    r.b.metadata_of.insert(result.0, vec![result.0]);
                }
            }
            assert_eq!(
                r.constructor_selection_report(expression).selection,
                Err(IncompleteProvider)
            );
            r.b.metadata_associations_incomplete = false;
            r.b.metadata_of = Default::default();
            assert!(r.constructor_selection_report(expression).selection.is_ok());
        }
    }
    #[test]
    fn malformed_same_length_edits_and_work_limits_do_not_reuse_success() {
        for key in [
            "ownedMemberParameter",
            "redefinedFeature",
            "isDefault",
            "visibility",
        ] {
            let (mut r, expression) = fixture(
                "class C {feature a;} feature x = new C(a=1);",
                GraphFormat::CanonicalV3,
            );
            let report = r.constructor_binding_report(expression).arguments.unwrap();
            let binding = &report.bindings[0];
            let row = match key {
                "ownedMemberParameter" => r.b.elements[binding.parameter.0]
                    .owning_relationship
                    .unwrap(),
                "visibility" => r.b.elements[binding.feature.0].owning_relationship.unwrap(),
                _ => r.b.elements[binding.parameter.0]
                    .owned_relationships
                    .iter()
                    .copied()
                    .find(|&i| {
                        r.b.elements[i].ty
                            == if key == "isDefault" {
                                "FeatureValue"
                            } else {
                                "Redefinition"
                            }
                    })
                    .unwrap(),
            };
            r.b.elements[row].props.insert(key, serde_json::Value::Null);
            assert!(
                r.constructor_binding_report(expression).arguments.is_err(),
                "{key}"
            );
        }
        let (mut r, expression) = fixture(
            "class C {feature a;} feature x = new C(a=1);",
            GraphFormat::CanonicalV3,
        );
        assert_eq!(
            r.constructor_binding_report_with_budget(expression, crate::eval::MAX_STEPS)
                .arguments,
            Err(WorkLimit)
        );
        assert!(r.constructor_binding_report(expression).arguments.is_ok());
    }
    #[test]
    fn first_wrong_kind_selector_is_never_skipped() {
        let (mut r, expression) = fixture(
            "class C {feature a;} feature x = new C(a=1);",
            GraphFormat::CanonicalV3,
        );
        let report = r.constructor_binding_report(expression).arguments.unwrap();
        let selector = r.b.elements[expression.0]
            .owned_relationships
            .iter()
            .copied()
            .find(|&i| r.b.elements[i].ty == "Membership")
            .unwrap();
        let wrong = r.b.elements[report.result.0].owning_relationship.unwrap();
        let wrong_id = r.b.elements[wrong].id;
        r.b.elements[selector]
            .props
            .insert("memberElement", serde_json::json!({"@id":wrong_id}));
        assert!(
            r.constructor_selection_report(expression)
                .selection
                .is_err()
        );
        assert!(r.constructor_binding_report(expression).arguments.is_err());
    }
    #[test]
    fn shared_dynamic_publisher_installs_constructor_result_specialization() {
        let (mut r, expression) = fixture(
            "class C {feature a;} feature x = new C(a=1);",
            GraphFormat::CanonicalV3,
        );
        let report = r.constructor_binding_report(expression).arguments.unwrap();
        r.set_closure_policy(ClosurePolicy::Closure {
            include_implied: true,
        });
        let _ = r.implied_relationships(expression);
        let target = r.element_id(report.instantiated_type);
        let relationships = semantic_ownership::owned_relationships(&r.b, report.result.0).unwrap();
        assert!(relationships.iter().any(|i| {
            r.b.elements[i].ty == "FeatureTyping"
                && r.b.elements[i]
                    .props
                    .get("type")
                    .and_then(|v| v.as_reference())
                    == Some(target)
        }));
        assert_eq!(
            r.constructor_binding_report(expression).arguments.unwrap(),
            report
        );
    }
}
