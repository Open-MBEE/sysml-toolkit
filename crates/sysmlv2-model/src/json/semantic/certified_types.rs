//! Conditional implementation capabilities, separate from the normative catalog.
use super::PropertyError;
use crate::{
    json::{
        ClosurePolicy, DerivedValue, ElementRef, FeatureTypeIssue, FeatureTypeReport, Reference,
        ResolvedModel, implied::SupportedImpliedSpecializations,
        semantic_ownership::SemanticOwnership,
    },
    layered::Revision,
    semantic_catalog,
};
use std::sync::Arc;

/// A declaration can be attempted by the checked reader under the indicated
/// policy. This is implementation capability metadata, never a promise that all
/// receivers succeed or a replacement for the normative declaration catalog.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub struct ConditionalPropertyCapability {
    pub declaration: &'static str,
    pub requires_full_closure: bool,
}

/// Conditional proof capability for an exact effective declaration identity.
/// This accessor does not change static `derives` fidelity. SDKs should attempt `property`
/// and handle its explicit errors, not treat this metadata as certification.
pub fn conditional_property_capability(declaration: &str) -> Option<ConditionalPropertyCapability> {
    let declaration = match declaration {
        "Systems-DefinitionAndUsage-Usage-mayTimeVary" => {
            "Systems-DefinitionAndUsage-Usage-mayTimeVary"
        }
        "Systems-DefinitionAndUsage-Definition-usage" => {
            "Systems-DefinitionAndUsage-Definition-usage"
        }
        "Systems-DefinitionAndUsage-Definition-directedUsage" => {
            "Systems-DefinitionAndUsage-Definition-directedUsage"
        }
        "Core-Types-Type-input" => "Core-Types-Type-input",
        "Core-Types-Type-feature" => "Core-Types-Type-feature",
        "Core-Types-Type-featureMembership" => "Core-Types-Type-featureMembership",
        "Core-Types-Type-inheritedMembership" => "Core-Types-Type-inheritedMembership",
        "Core-Types-Type-inheritedFeature" => "Core-Types-Type-inheritedFeature",
        "Core-Types-Type-output" => "Core-Types-Type-output",
        "Core-Types-Type-directedFeature" => "Core-Types-Type-directedFeature",
        "Core-Types-Type-endFeature" => "Core-Types-Type-endFeature",
        "Kernel-Functions-Function-result" => "Kernel-Functions-Function-result",
        "Kernel-Functions-Expression-result" => "Kernel-Functions-Expression-result",
        "Kernel-Expressions-InstantiationExpression-instantiatedType" => {
            "Kernel-Expressions-InstantiationExpression-instantiatedType"
        }
        "Kernel-Expressions-InstantiationExpression-argument" => {
            "Kernel-Expressions-InstantiationExpression-argument"
        }
        "Systems-DefinitionAndUsage-Usage-definition" => {
            "Systems-DefinitionAndUsage-Usage-definition"
        }
        "Systems-Attributes-AttributeUsage-attributeDefinition" => {
            "Systems-Attributes-AttributeUsage-attributeDefinition"
        }
        "Systems-Occurrences-OccurrenceUsage-occurrenceDefinition" => {
            "Systems-Occurrences-OccurrenceUsage-occurrenceDefinition"
        }
        "Systems-Items-ItemUsage-itemDefinition" => "Systems-Items-ItemUsage-itemDefinition",
        "Systems-Parts-PartUsage-partDefinition" => "Systems-Parts-PartUsage-partDefinition",
        "Core-Features-Feature-type" => "Core-Features-Feature-type",
        "Kernel-Behaviors-Step-behavior" => "Kernel-Behaviors-Step-behavior",
        "Kernel-Functions-Expression-function" => "Kernel-Functions-Expression-function",
        _ => return None,
    };
    Some(ConditionalPropertyCapability {
        declaration,
        requires_full_closure: true,
    })
}
fn same_arc<T>(a: &Option<Arc<T>>, b: &Option<Arc<T>>) -> bool {
    match (a, b) {
        (None, None) => true,
        (Some(a), Some(b)) => Arc::ptr_eq(a, b),
        _ => false,
    }
}

/// Private query snapshot. Every semantic input that can change proof results
/// without changing rows must participate in the freshness check.
pub(in crate::json) struct Stamp {
    publication: crate::json::publication::Revision,
    rows: Revision,
    len: usize,
    explicit: usize,
    library: usize,
    ownership: Option<Arc<SemanticOwnership>>,
    metadata: Option<Arc<()>>,
    retained: Option<Arc<SupportedImpliedSpecializations>>,
    metadata_incomplete: bool,
    lookup_incomplete: bool,
    ready: bool,
    positional_ready: bool,
    policy: Option<ClosurePolicy>,
}
impl Stamp {
    pub(in crate::json) fn capture(r: &mut ResolvedModel) -> Self {
        let mut stamp = Self::capture_builder(&mut r.b);
        stamp.policy = Some(r.closure_policy());
        stamp
    }
    pub(in crate::json) fn capture_builder(b: &mut crate::json::Builder) -> Self {
        Self {
            publication: b.publication.revision(),
            rows: b.elements.observe_revision(),
            len: b.elements.len(),
            explicit: b.explicit_len(),
            library: b.lib_boundary,
            ownership: b.semantic_ownership.clone(),
            metadata: b.metadata_association_generation.clone(),
            retained: b.supported_implied.clone(),
            metadata_incomplete: b.metadata_associations_incomplete,
            lookup_incomplete: b.recorded_lookup_incomplete,
            ready: b.semantic_ready,
            positional_ready: b.positional_redefinitions.is_some(),
            policy: None,
        }
    }
    pub(in crate::json) fn current(&self, r: &ResolvedModel) -> bool {
        self.current_builder(&r.b)
            && self
                .policy
                .is_none_or(|policy| policy == r.closure_policy())
    }
    pub(in crate::json) fn current_builder(&self, b: &crate::json::Builder) -> bool {
        !b.positional_planning
            && self.publication.same_as(&b.publication.revision())
            && b.elements.revision().is_some_and(|v| self.rows.same_as(v))
            && self.len == b.elements.len()
            && self.explicit == b.explicit_len()
            && self.library == b.lib_boundary
            && same_arc(&self.ownership, &b.semantic_ownership)
            && same_arc(&self.metadata, &b.metadata_association_generation)
            && same_arc(&self.retained, &b.supported_implied)
            && self.metadata_incomplete == b.metadata_associations_incomplete
            && self.lookup_incomplete == b.recorded_lookup_incomplete
            && self.ready == b.semantic_ready
            && self.positional_ready == b.positional_redefinitions.is_some()
    }
}
struct Cached {
    receiver: ElementRef,
    stamp: Stamp,
    report: FeatureTypeReport,
}
struct CachedFeatures {
    receiver: ElementRef,
    stamp: Stamp,
    projections: crate::json::TypeFeatures,
}
#[derive(Default)]
pub(super) struct CheckedRow {
    namespaces: crate::json::operations::namespaces::NamespaceRow,
    cached: Option<Cached>,
    features: Option<CachedFeatures>,
    steps: usize,
}
impl CheckedRow {
    pub(in crate::json) fn read_namespace(
        &mut self,
        r: &mut ResolvedModel,
        receiver: ElementRef,
        declaration: &'static str,
    ) -> Result<DerivedValue, PropertyError> {
        if crate::json::type_features::supported_root(r.element_type(receiver))
            && matches!(
                declaration,
                "Root-Namespaces-Namespace-membership" | "Root-Namespaces-Namespace-member"
            )
        {
            if r.closure_policy()
                != (ClosurePolicy::Closure {
                    include_implied: true,
                })
            {
                return Err(PropertyError::Approximate);
            }
            return self.read_features(r, receiver, declaration);
        }
        self.namespaces
            .property(r, receiver, declaration, &mut self.steps)
    }
    fn ensure_features(
        &mut self,
        r: &mut ResolvedModel,
        receiver: ElementRef,
    ) -> Result<(), crate::json::TypeInputIssue> {
        self.steps = self.steps.saturating_add(1);
        if self.steps > crate::eval::MAX_STEPS {
            return Err(crate::json::TypeInputIssue::WorkLimit);
        }
        if !self
            .features
            .as_ref()
            .is_some_and(|c| c.receiver == receiver && c.stamp.current(r))
        {
            self.features = None;
            let report = r.type_feature_report_with_budget(receiver, self.steps);
            self.steps = report.steps;
            let projections = report.projections?;
            self.features = Some(CachedFeatures {
                receiver,
                stamp: Stamp::capture(r),
                projections,
            });
        }
        Ok(())
    }
    fn read_features(
        &mut self,
        r: &mut ResolvedModel,
        receiver: ElementRef,
        declaration: &str,
    ) -> Result<DerivedValue, PropertyError> {
        let error = |issue| {
            if declaration == "Core-Types-Type-input" {
                PropertyError::IncompleteTypeInput(issue)
            } else {
                PropertyError::IncompleteTypeFeatures(issue)
            }
        };
        self.ensure_features(r, receiver).map_err(error)?;
        let p = &self
            .features
            .as_ref()
            .expect("complete current certificate")
            .projections;
        let refs = match declaration {
            "Core-Types-Type-input" => &p.inputs,
            "Core-Types-Type-output" => &p.outputs,
            "Core-Types-Type-directedFeature" => &p.directed_features,
            "Core-Types-Type-endFeature" => &p.end_features,
            "Core-Types-Type-feature" => &p.features,
            "Core-Types-Type-featureMembership" => &p.feature_memberships,
            "Core-Types-Type-inheritedFeature" => &p.inherited_features,
            "Core-Types-Type-inheritedMembership" => &p.inherited_memberships,
            "Root-Namespaces-Namespace-membership" => {
                p.memberships.as_ref().map_err(|e| error(*e))?
            }
            "Root-Namespaces-Namespace-member" => p.members.as_ref().map_err(|e| error(*e))?,
            _ => unreachable!("audited Type sequence declaration"),
        };
        self.steps = self.steps.saturating_add(refs.len().saturating_mul(12));
        if self.steps > crate::eval::MAX_STEPS {
            return Err(error(crate::json::TypeInputIssue::WorkLimit));
        }
        Ok(DerivedValue::References(
            refs.iter().copied().map(Reference::Element).collect(),
        ))
    }
    fn charge(&mut self, amount: usize) -> Result<(), PropertyError> {
        self.steps = self.steps.saturating_add(amount);
        if self.steps > crate::eval::MAX_STEPS {
            Err(PropertyError::IncompleteTypeProjection(
                FeatureTypeIssue::WorkLimit,
            ))
        } else {
            Ok(())
        }
    }
    /// An owned source endpoint uses local carrier evidence, not inheritance
    /// closure. Its work participates in the same strict-export row budget.
    pub(super) fn read_owned_source(
        &mut self,
        r: &mut ResolvedModel,
        e: ElementRef,
        effective: &semantic_catalog::PropertySpec,
    ) -> Option<Result<serde_json::Value, PropertyError>> {
        if effective.id == "Root-Elements-Element-ownedRelationship" {
            return Some(self.owned_relationships(r, e));
        }
        if effective.id == "Core-Features-Feature-isConstant" {
            if let Some(report) = r.canonical_end_constant_with_budget(e, self.steps) {
                self.steps = report.steps;
                return Some(
                    report
                        .value
                        .map(serde_json::Value::Bool)
                        .map_err(PropertyError::IncompleteUsageVariability),
                );
            }
        }
        if effective.id != "Core-Features-TypeFeaturing-featureOfType" {
            return None;
        }
        let source =
            crate::json::type_relations::type_featuring_source(&mut r.b, e.0, &mut self.steps);
        Some(if self.steps > crate::eval::MAX_STEPS {
            Err(PropertyError::NotComputed)
        } else {
            source
                .map(|id| serde_json::json!({"@id":id.to_string()}))
                .ok_or_else(|| {
                    PropertyError::InvalidValue("unproved TypeFeaturing source endpoint".into())
                })
        })
    }

    /// The relationships present in the published model are structural data.
    /// Reading them does not assert that every required implied family exists.
    fn owned_relationships(
        &mut self,
        r: &mut ResolvedModel,
        owner: ElementRef,
    ) -> Result<serde_json::Value, PropertyError> {
        use crate::json::{publication, semantic_ownership, structural_index::StoredStructure};
        if r.b.ensure_semantic_graph() != publication::Status::Ready {
            return Err(PropertyError::Approximate);
        }
        r.sync_semantic_publication();
        let raw = StoredStructure::for_query(&mut r.b, &mut self.steps)
            .ok_or(PropertyError::Approximate)?;
        if !raw.ids_unique {
            return Err(PropertyError::InvalidValue(
                "duplicate element identity".into(),
            ));
        }
        let rows = semantic_ownership::owned_relationships(&r.b, owner.0)
            .ok_or(PropertyError::Approximate)?;
        self.steps = self.steps.saturating_add(rows.len().saturating_mul(12));
        if self.steps > crate::eval::MAX_STEPS {
            return Err(PropertyError::Approximate);
        }
        let mut seen = std::collections::HashSet::new();
        let mut values = Vec::with_capacity(rows.len());
        for relationship in rows.iter() {
            if !seen.insert(relationship)
                || semantic_ownership::checked_relationship_carrier(
                    &r.b,
                    &raw,
                    relationship,
                    &mut self.steps,
                ) != Some(Some(owner.0))
            {
                return Err(PropertyError::InvalidValue(
                    "inconsistent owned relationship carrier".into(),
                ));
            }
            values.push(
                serde_json::json!({"@id": r.element_id(ElementRef(relationship)).to_string()}),
            );
        }
        Ok(serde_json::Value::Array(values))
    }

    pub(super) fn read(
        &mut self,
        r: &mut ResolvedModel,
        e: ElementRef,
        name: &str,
    ) -> Option<Result<DerivedValue, PropertyError>> {
        let (requested, effective) = semantic_catalog::property(r.element_type(e), name)?;
        let effective = effective?;
        self.read_declared(r, e, requested, effective)
    }
    pub(super) fn read_declared(
        &mut self,
        r: &mut ResolvedModel,
        e: ElementRef,
        requested: &semantic_catalog::PropertySpec,
        effective: &semantic_catalog::PropertySpec,
    ) -> Option<Result<DerivedValue, PropertyError>> {
        if matches!(
            effective.id,
            "Root-Namespaces-Namespace-importedMembership"
                | "Root-Namespaces-Namespace-membership"
                | "Root-Namespaces-Namespace-member"
        ) && (matches!(
            r.element_type(e),
            "Namespace" | "Package" | "LibraryPackage"
        ) || crate::json::type_features::supported_root(r.element_type(e)))
        {
            return Some(self.read_namespace(r, e, effective.id));
        }
        conditional_property_capability(effective.id)?;
        // New plain-Type capabilities do not change the established error
        // contract for unsupported subclasses. Type.input predates this domain
        // expansion and retains its existing typed qualification.
        if (effective.id.starts_with("Core-Types-Type-")
            || matches!(
                effective.id,
                "Systems-DefinitionAndUsage-Definition-usage"
                    | "Systems-DefinitionAndUsage-Definition-directedUsage"
            ))
            && effective.id != "Core-Types-Type-input"
            && !crate::json::type_features::supported_root(r.element_type(e))
        {
            return None;
        }
        if matches!(
            effective.id,
            "Kernel-Functions-Expression-result"
                | "Kernel-Expressions-InstantiationExpression-instantiatedType"
        ) && (r.element_type(e) != "ConstructorExpression"
            || r.b.graph_format != crate::model::GraphFormat::CanonicalV3)
        {
            return None;
        }
        Some(self.read_known(r, e, requested, effective))
    }
    fn read_known(
        &mut self,
        r: &mut ResolvedModel,
        e: ElementRef,
        requested: &semantic_catalog::PropertySpec,
        effective: &semantic_catalog::PropertySpec,
    ) -> Result<DerivedValue, PropertyError> {
        if r.closure_policy()
            != (ClosurePolicy::Closure {
                include_implied: true,
            })
        {
            return Err(PropertyError::Approximate);
        }
        if effective.id == "Systems-DefinitionAndUsage-Usage-mayTimeVary" {
            let report = r.usage_variability_report_with_budget(e, self.steps);
            self.steps = report.steps;
            return report
                .value
                .map(DerivedValue::Bool)
                .map_err(PropertyError::IncompleteUsageVariability);
        }
        if matches!(
            effective.id,
            "Kernel-Functions-Expression-result"
                | "Kernel-Expressions-InstantiationExpression-instantiatedType"
        ) {
            let report = r.constructor_selection_report_with_budget(e, self.steps);
            self.steps = report.steps.saturating_add(12);
            if self.steps > crate::eval::MAX_STEPS {
                return Err(PropertyError::IncompleteConstructorBindings(
                    crate::json::ConstructorBindingIssue::WorkLimit,
                ));
            }
            let selection = report
                .selection
                .map_err(PropertyError::IncompleteConstructorBindings)?;
            let selected = if effective.id == "Kernel-Functions-Expression-result" {
                selection.result
            } else {
                selection.instantiated_type
            };
            validate_references(r, effective, &[selected])?;
            validate_references(r, requested, &[selected])?;
            return Ok(DerivedValue::Reference(Reference::Element(selected)));
        }
        if effective.id == "Kernel-Functions-Function-result" {
            if r.element_type(e) != "Function" {
                return Err(PropertyError::IncompleteFunctionResult(
                    crate::json::TypeInputIssue::UnsupportedConfiguration,
                ));
            }
            self.ensure_features(r, e)
                .map_err(PropertyError::IncompleteFunctionResult)?;
            let features = &self
                .features
                .as_ref()
                .expect("complete current certificate")
                .projections
                .features;
            self.steps = self.steps.saturating_add(features.len()).saturating_add(12);
            if self.steps > crate::eval::MAX_STEPS {
                return Err(PropertyError::IncompleteFunctionResult(
                    crate::json::TypeInputIssue::WorkLimit,
                ));
            }
            let result = features
                .iter()
                .copied()
                .find(|f| {
                    r.b.elements[f.0].owning_relationship.is_some_and(|m| {
                        crate::metaclass::conforms(r.b.elements[m].ty, "ReturnParameterMembership")
                    })
                })
                .ok_or(PropertyError::MissingRequiredValue)?;
            validate_references(r, effective, &[result])?;
            validate_references(r, requested, &[result])?;
            return Ok(DerivedValue::Reference(Reference::Element(result)));
        }
        if effective.id == "Kernel-Expressions-InstantiationExpression-argument" {
            if r.element_type(e) == "ConstructorExpression"
                && r.b.graph_format == crate::model::GraphFormat::CanonicalV3
            {
                let report = r.constructor_binding_report_with_budget(e, self.steps);
                self.steps = report.steps;
                let args = report
                    .arguments
                    .map_err(PropertyError::IncompleteConstructorBindings)?;
                self.steps = self
                    .steps
                    .saturating_add(args.bindings.len().saturating_mul(12));
                if self.steps > crate::eval::MAX_STEPS {
                    return Err(PropertyError::IncompleteConstructorBindings(
                        crate::json::ConstructorBindingIssue::WorkLimit,
                    ));
                }
                let refs: Vec<_> = args.bindings.into_iter().map(|b| b.value).collect();
                validate_references(r, effective, &refs)?;
                validate_references(r, requested, &refs)?;
                return Ok(DerivedValue::References(
                    refs.into_iter().map(Reference::Element).collect(),
                ));
            }
            let report = r.invocation_binding_report_with_budget(e, self.steps);
            self.steps = report.steps;
            let args = report
                .arguments
                .map_err(PropertyError::IncompleteInvocationBindings)?;
            self.steps = self
                .steps
                .saturating_add(args.bindings.len().saturating_mul(12));
            if self.steps > crate::eval::MAX_STEPS {
                return Err(PropertyError::IncompleteInvocationBindings(
                    crate::json::InvocationBindingIssue::WorkLimit,
                ));
            }
            let refs: Vec<_> = args.bindings.into_iter().map(|b| b.value).collect();
            validate_references(r, effective, &refs)?;
            validate_references(r, requested, &refs)?;
            return Ok(DerivedValue::References(
                refs.into_iter().map(Reference::Element).collect(),
            ));
        }
        if matches!(
            effective.id,
            "Systems-DefinitionAndUsage-Definition-usage"
                | "Systems-DefinitionAndUsage-Definition-directedUsage"
        ) {
            let base = if effective.name == "usage" {
                "Core-Types-Type-feature"
            } else {
                "Core-Types-Type-directedFeature"
            };
            // These normative subsets filter the complete inherited sequence,
            // never an owned-only inventory or a member's separate type proof.
            let DerivedValue::References(refs) = self.read_features(r, e, base)? else {
                unreachable!("certified Type sequences contain local handles")
            };
            let handles: Vec<_> = refs
                .into_iter()
                .filter_map(|reference| match reference {
                    Reference::Element(member) if r.is_kind(member, "Usage") => Some(member),
                    Reference::Element(_) => None,
                    _ => unreachable!("certified local handles"),
                })
                .collect();
            validate_references(r, effective, &handles)?;
            validate_references(r, requested, &handles)?;
            return Ok(DerivedValue::References(
                handles.into_iter().map(Reference::Element).collect(),
            ));
        }
        if effective.id.starts_with("Core-Types-Type-") {
            let value = self.read_features(r, e, effective.id)?;
            if let DerivedValue::References(refs) = &value {
                let handles: Vec<_> = refs
                    .iter()
                    .map(|reference| match reference {
                        Reference::Element(e) => *e,
                        _ => unreachable!("certified local handles"),
                    })
                    .collect();
                validate_references(r, effective, &handles)?;
                validate_references(r, requested, &handles)?;
            }
            return Ok(value);
        }
        self.charge(1)?;
        if r.b.positional_planning {
            return Err(PropertyError::IncompleteTypeProjection(
                FeatureTypeIssue::UnsupportedProjection,
            ));
        }
        if !self
            .cached
            .as_ref()
            .is_some_and(|v| v.receiver == e && v.stamp.current(r))
        {
            self.cached = None;
            let report = r.feature_type_report_with_budget(e, self.steps);
            self.steps = report.steps;
            self.charge(0)?;
            let stamp = Stamp::capture(r);
            self.cached = Some(Cached {
                receiver: e,
                stamp,
                report,
            });
        }
        let report = &self
            .cached
            .as_ref()
            .expect("established current report")
            .report;
        let refs: Result<&[ElementRef], FeatureTypeIssue> = match effective.id {
            "Core-Features-Feature-type"
            | "Systems-DefinitionAndUsage-Usage-definition"
            | "Systems-Attributes-AttributeUsage-attributeDefinition"
            | "Systems-Occurrences-OccurrenceUsage-occurrenceDefinition"
            | "Systems-Items-ItemUsage-itemDefinition"
            | "Systems-Parts-PartUsage-partDefinition" => {
                report.types.as_ref().map(Vec::as_slice).map_err(|e| *e)
            }
            "Kernel-Behaviors-Step-behavior" => {
                report.behavior.as_ref().map(Vec::as_slice).map_err(|e| *e)
            }
            "Kernel-Functions-Expression-function" => report
                .function
                .as_ref()
                .map(|v| v.as_slice())
                .map_err(|e| *e),
            _ => unreachable!("audited capability identity"),
        };
        let refs = refs.map_err(PropertyError::IncompleteTypeProjection)?;
        if (effective.upper == Some(1) || requested.upper == Some(1)) && refs.len() > 1 {
            return Err(PropertyError::InvalidValue(
                "multiple values for a single-valued redefinition".into(),
            ));
        }

        // Report output, effective/requested validation and JSON reference
        // conversion all have bounded passes over fixed-length UUID identities.
        // Charge before cloning or serializing even when the report is cached.
        let amount = refs.len().saturating_mul(12).saturating_add(1);
        let used = self.steps.saturating_add(amount);
        if used > crate::eval::MAX_STEPS {
            self.steps = used;
            return Err(PropertyError::IncompleteTypeProjection(
                FeatureTypeIssue::WorkLimit,
            ));
        }
        self.steps = used;
        // Item and Part definitions subset the complete type collection;
        // the other Usage declarations redefine it and must validate every type.
        let subset_kind = match effective.id {
            "Systems-Items-ItemUsage-itemDefinition" => Some("Structure"),
            "Systems-Parts-PartUsage-partDefinition" => Some("PartDefinition"),
            _ => None,
        };
        let refs: Vec<_> = refs
            .iter()
            .copied()
            .filter(|e| {
                subset_kind.is_none_or(|kind| crate::metaclass::conforms(r.element_type(*e), kind))
            })
            .collect();
        validate_references(r, effective, &refs)?;
        validate_references(r, requested, &refs)?;
        if requested.upper == Some(1) {
            Ok(refs
                .first()
                .map(|&e| DerivedValue::Reference(Reference::Element(e)))
                .unwrap_or(DerivedValue::Null))
        } else {
            Ok(DerivedValue::References(
                refs.into_iter().map(Reference::Element).collect(),
            ))
        }
    }
}

/// Certified local handles avoid the independent ResolvedModel by_id map.
/// This enforces the same reference cardinality, uniqueness and target-kind
/// constraints as JSON property validation without a cold whole-model rebuild.
fn validate_references(
    r: &ResolvedModel,
    spec: &semantic_catalog::PropertySpec,
    refs: &[ElementRef],
) -> Result<(), PropertyError> {
    if refs.len() < spec.lower {
        return Err(PropertyError::MissingRequiredValue);
    }
    if spec.upper.is_some_and(|upper| refs.len() > upper) {
        return Err(PropertyError::InvalidValue(
            "multiple values for a single-valued redefinition".into(),
        ));
    }
    let mut seen = std::collections::HashSet::new();
    for target in refs {
        let element =
            r.b.elements
                .get(target.0)
                .ok_or_else(|| PropertyError::InvalidValue("missing certified reference".into()))?;
        if spec.unique && !seen.insert(element.id) {
            return Err(PropertyError::InvalidValue(
                "duplicate value in a unique property".into(),
            ));
        }
        if !crate::metaclass::conforms(element.ty, spec.target) {
            return Err(PropertyError::InvalidValue(format!(
                "expected {}",
                spec.target
            )));
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        json::{Derived, Derives, derives},
        model::Model,
    };
    const LIB: &str = "standard library package Base {classifier Anything; feature things:Anything;} standard library package Occurrences {class Occurrence specializes Base::Anything; feature occurrences:Occurrence subsets Base::things;} standard library package Performances {behavior Performance specializes Occurrences::Occurrence; function Evaluation specializes Performance; step performances:Performance subsets Occurrences::occurrences; expr evaluations:Evaluation subsets performances;}";
    fn fixture(source: &str) -> ResolvedModel {
        let mut m = Model::new();
        assert!(
            m.add_library_source("certified-lib.kerml", LIB)
                .diagnostics
                .is_empty()
        );
        assert!(
            m.add_source("certified-user.kerml", source)
                .diagnostics
                .is_empty()
        );
        ResolvedModel::build(&m)
    }
    fn full(r: &mut ResolvedModel) {
        r.set_closure_policy(ClosurePolicy::Closure {
            include_implied: true,
        });
    }
    #[test]
    fn result_and_argument_output_budget_errors_keep_their_report_family() {
        let mut r = fixture("function F {in a; return r;} feature call=F(a=1);");
        full(&mut r);
        let f = r.resolve_qualified("F").unwrap();
        let call = ElementRef(
            r.b.elements
                .iter()
                .position(|e| e.ty == "InvocationExpression")
                .unwrap(),
        );
        assert!(r.function_result_report(f).result.is_ok());
        let used = r.function_result_report(f).steps;
        assert!(
            r.function_result_report_with_budget(f, crate::eval::MAX_STEPS - used - 6)
                .result
                .is_ok()
        );
        let mut row = CheckedRow {
            steps: crate::eval::MAX_STEPS - used - 6,
            ..Default::default()
        };
        assert_eq!(
            row.read(&mut r, f, "result"),
            Some(Err(PropertyError::IncompleteFunctionResult(
                crate::json::TypeInputIssue::WorkLimit
            )))
        );
        assert!(r.invocation_binding_report(call).arguments.is_ok());
        let used = r.invocation_binding_report(call).steps;
        assert!(
            r.invocation_binding_report_with_budget(call, crate::eval::MAX_STEPS - used - 6)
                .arguments
                .is_ok()
        );
        let mut row = CheckedRow {
            steps: crate::eval::MAX_STEPS - used - 6,
            ..Default::default()
        };
        assert_eq!(
            row.read(&mut r, call, "argument"),
            Some(Err(PropertyError::IncompleteInvocationBindings(
                crate::json::InvocationBindingIssue::WorkLimit
            )))
        );
        assert!(r.property(f, "result").is_ok());
        assert!(r.property(call, "argument").is_ok());
    }
    #[test]
    fn input_checked_row_budget_is_cumulative_and_retryable() {
        let mut r = fixture("function F { in a; }");
        full(&mut r);
        let f = r.resolve_qualified("F").unwrap();
        let mut row = CheckedRow::default();
        assert!(row.read(&mut r, f, "input").unwrap().is_ok());
        let used = row.steps;
        assert!(row.read(&mut r, f, "input").unwrap().is_ok());
        assert!(row.steps > used);
        row.steps = crate::eval::MAX_STEPS;
        assert_eq!(
            row.read(&mut r, f, "input"),
            Some(Err(PropertyError::IncompleteTypeInput(
                crate::json::TypeInputIssue::WorkLimit
            )))
        );
        assert!(r.property(f, "input").is_ok());
    }
    #[test]
    fn usage_aliases_share_checked_row_work_without_legacy_type_errors() {
        let mut model = Model::new();
        model.add_source("usage.sysml", "ref x;");
        let mut r = ResolvedModel::build(&model);
        full(&mut r);
        let x = r.resolve_qualified("x").unwrap();
        let mut row = CheckedRow::default();
        assert_eq!(
            row.read(&mut r, x, "mayTimeVary"),
            Some(Ok(DerivedValue::Bool(false)))
        );
        let used = row.steps;
        assert_eq!(
            row.read(&mut r, x, "isVariable"),
            Some(Ok(DerivedValue::Bool(false)))
        );
        assert!(row.steps > used);
        row.steps = crate::eval::MAX_STEPS;
        assert_eq!(
            row.read(&mut r, x, "isVariable"),
            Some(Err(PropertyError::IncompleteUsageVariability(
                crate::json::UsageVariabilityIssue::WorkLimit
            )))
        );
        assert_eq!(r.property(x, "mayTimeVary"), Ok(serde_json::json!(false)));
    }

    #[test]
    fn warm_checked_row_refuses_an_in_progress_positional_sentinel() {
        let mut r = fixture(
            "function F specializes Performances::Evaluation; expr e:F subsets Performances::evaluations;",
        );
        full(&mut r);
        let e = r.resolve_qualified("e").unwrap();
        let mut row = CheckedRow::default();
        assert!(row.read(&mut r, e, "function").unwrap().is_ok());
        let plan = r.b.positional_redefinitions.replace(Default::default());
        r.b.positional_planning = true;
        assert!(!row.cached.as_ref().unwrap().stamp.current(&r));
        assert_eq!(
            row.read(&mut r, e, "function").unwrap(),
            Err(PropertyError::IncompleteTypeProjection(
                FeatureTypeIssue::UnsupportedProjection
            ))
        );
        r.b.positional_planning = false;
        r.b.positional_redefinitions = plan;
        assert!(row.read(&mut r, e, "function").unwrap().is_ok());
    }

    #[test]
    fn checked_reads_certify_full_policy_and_preserve_compatibility_with_qualified_fidelity() {
        let mut r = fixture(
            "function F specializes Performances::Evaluation; expr e:F subsets Performances::evaluations;",
        );
        let e = r.resolve_qualified("e").unwrap();
        let f = r.resolve_qualified("F").unwrap();
        let baseline = r.derived(e, "type");
        let rows = r.elements().count();
        let ids: Vec<_> = r.user_elements().map(|e| r.element_id(e)).collect();
        assert_eq!(derives("Expression", "type"), Derives::Passthrough);
        for policy in [
            ClosurePolicy::Passthrough,
            ClosurePolicy::Closure {
                include_implied: false,
            },
        ] {
            r.set_closure_policy(policy);
            assert_eq!(r.property(e, "type"), Err(PropertyError::Approximate));
            assert_eq!(
                r.derived_exact(e, "function"),
                Err(PropertyError::Approximate)
            );
            assert_eq!(r.closure_policy(), policy);
        }
        full(&mut r);
        let reference = serde_json::json!({"@id":r.element_id(f).to_string()});
        assert_eq!(
            r.property(e, "type"),
            Ok(serde_json::json!([reference.clone()]))
        );
        assert_eq!(r.property(e, "function"), Ok(reference.clone()));
        assert_eq!(
            r.property(e, "behavior"),
            Ok(serde_json::json!([reference]))
        );
        assert_eq!(
            r.derived_exact(e, "function"),
            Ok(DerivedValue::Reference(Reference::Element(f)))
        );
        assert_eq!(
            r.derived_exact(e, "behavior"),
            Ok(DerivedValue::References(vec![Reference::Element(f)]))
        );
        assert_eq!(r.derived(e, "type"), baseline);
        assert_eq!(r.elements().count(), rows);
        assert_eq!(
            r.user_elements()
                .map(|e| r.element_id(e))
                .collect::<Vec<_>>(),
            ids
        );
        assert!(
            conditional_property_capability("Kernel-Functions-Expression-function")
                .unwrap()
                .requires_full_closure
        );
        assert!(conditional_property_capability("function").is_none());
        assert!(matches!(r.derived(e, "function"), Derived::Value(_)));
    }
    #[test]
    fn effective_function_multiplicity_governs_behavior_alias_but_not_complete_feature_type() {
        let mut r = fixture(
            "function F specializes Performances::Evaluation; function G specializes Performances::Evaluation; expr e:F,G subsets Performances::evaluations;",
        );
        full(&mut r);
        let e = r.resolve_qualified("e").unwrap();
        assert!(r.property(e, "type").is_ok());
        assert_eq!(
            r.property(e, "function"),
            Err(PropertyError::IncompleteTypeProjection(
                FeatureTypeIssue::InvalidFunctionMultiplicity
            ))
        );
        assert_eq!(
            r.derived_exact(e, "function"),
            Err(PropertyError::IncompleteTypeProjection(
                FeatureTypeIssue::InvalidFunctionMultiplicity
            ))
        );
        for name in ["function", "behavior"] {
            assert_eq!(
                r.property(e, name),
                Err(PropertyError::IncompleteTypeProjection(
                    FeatureTypeIssue::InvalidFunctionMultiplicity
                ))
            );
            assert_eq!(
                r.derived_exact(e, name),
                Err(PropertyError::IncompleteTypeProjection(
                    FeatureTypeIssue::InvalidFunctionMultiplicity
                ))
            );
        }
    }
    #[test]
    fn checked_export_reports_missing_evidence_without_changing_compatibility() {
        // Generic Expression/Step ancestry supplies both Feature roles even
        // when the source and the canonical evaluations omit their subsetting.
        let mut intact = Model::new();
        let library = LIB.replace(
            "expr evaluations:Evaluation subsets performances;",
            "expr evaluations:Evaluation;",
        );
        assert_ne!(library, LIB);
        assert!(
            intact
                .add_library_source("intact.kerml", &library)
                .diagnostics
                .is_empty()
        );
        assert!(
            intact
                .add_source(
                    "complete.kerml",
                    "function F specializes Performances::Evaluation; expr complete:F;"
                )
                .diagnostics
                .is_empty()
        );
        let mut positive = ResolvedModel::build(&intact);
        full(&mut positive);
        let evaluations = positive
            .resolve_qualified("Performances::evaluations")
            .unwrap()
            .0;
        let performances = positive
            .resolve_qualified("Performances::performances")
            .unwrap()
            .0;
        assert_eq!(
            crate::json::type_relations::TypeRelations::default().specializes(
                &mut positive.b,
                evaluations,
                performances,
                &mut 0
            ),
            crate::json::type_relations::RelationFact::Yes
        );
        let complete = positive.resolve_qualified("complete").unwrap();
        let complete_id = positive.element_id(complete);
        let positive_issues = positive.to_full_json_strict().unwrap_err().issues;
        assert!(!positive_issues.iter().any(|i| i.element_id == complete_id
            && matches!(i.property.as_str(), "type" | "function" | "behavior")));

        // Remove the canonical Step Feature entirely, including its authored
        // reference from evaluations. Only the required implied family is
        // missing; no invalid authored endpoint obscures that qualification.
        let library = LIB
            .replace(
                "step performances:Performance subsets Occurrences::occurrences;",
                "",
            )
            .replace(
                "expr evaluations:Evaluation subsets performances;",
                "expr evaluations:Evaluation;",
            );
        assert_ne!(library, LIB);
        let mut model = Model::new();
        assert!(
            model
                .add_library_source("broken-evaluation-base.kerml", &library)
                .diagnostics
                .is_empty()
        );
        assert!(model.add_source("missing-export.kerml",
            "function F specializes Performances::Evaluation; expr missing:F; feature call=F();"
        ).diagnostics.is_empty());
        let mut r = ResolvedModel::build(&model);
        full(&mut r);
        assert!(r.resolve_qualified("Performances::evaluations").is_some());
        assert!(r.resolve_qualified("Performances::performances").is_none());
        assert!(r.resolve_qualified("Performances::Performance").is_some());
        let missing = r.resolve_qualified("missing").unwrap();
        let before_type = r.property(missing, "type");
        let before_function = r.property(missing, "function");
        let before_export = r.to_full_json_strict();
        let compatibility_type = r.derived(missing, "type");
        assert_eq!(
            r.property(missing, "type"),
            Err(PropertyError::IncompleteTypeProjection(
                FeatureTypeIssue::MissingRequiredFamilies
            ))
        );
        let call = r.resolve_qualified("call").unwrap();
        let invocation = r.members_via(call, "FeatureValue")[0];
        assert!(matches!(
            r.property(invocation, "function"),
            Err(PropertyError::IncompleteTypeProjection(_))
        ));
        let missing_id = r.element_id(missing);
        let issues = r.to_full_json_strict().unwrap_err().issues;
        assert!(issues.iter().any(|i| i.element_id == missing_id
            && i.property == "type"
            && matches!(i.reason, PropertyError::IncompleteTypeProjection(_))));
        assert!(
            !issues.is_empty(),
            "other unsupported properties still refuse whole export"
        );
        assert_eq!(r.property(missing, "type"), before_type);
        assert_eq!(r.property(missing, "function"), before_function);
        assert_eq!(r.to_full_json_strict(), before_export);
        assert_eq!(r.derived(missing, "type"), compatibility_type);
    }
    #[test]
    fn ordered_type_row_shares_one_current_certificate_across_components() {
        let mut r = fixture("function F {in a; out b; return answer;}");
        full(&mut r);
        let f = r.resolve_qualified("F").unwrap();
        let a = r.resolve_qualified("F::a").unwrap();
        let mut row = CheckedRow::default();
        assert!(row.read(&mut r, f, "feature").unwrap().is_ok());
        let first = row.steps;
        for name in [
            "featureMembership",
            "input",
            "output",
            "endFeature",
            "inheritedMembership",
            "inheritedFeature",
            "result",
        ] {
            assert!(row.read(&mut r, f, name).unwrap().is_ok(), "{name}");
        }
        assert!(
            row.read(&mut r, f, "directedFeature").is_none(),
            "Behavior parameter override remains qualified"
        );
        assert!(
            row.read_namespace(&mut r, f, "Root-Namespaces-Namespace-membership")
                .is_ok()
        );
        assert!(
            row.steps - first < 500,
            "one row must reuse its complete certificate"
        );
        r.b.set(a.0, "direction", serde_json::json!("out"));
        assert_eq!(
            row.read(&mut r, f, "input").unwrap(),
            Ok(DerivedValue::References(vec![]))
        );
        r.b.set(a.0, "direction", serde_json::json!(false));
        assert!(matches!(
            row.read(&mut r, f, "feature").unwrap(),
            Err(PropertyError::IncompleteTypeFeatures(_))
        ));
        r.b.set(a.0, "direction", serde_json::json!("in"));
        assert!(row.read(&mut r, f, "feature").unwrap().is_ok());
        row.steps = crate::eval::MAX_STEPS;
        assert_eq!(
            row.read(&mut r, f, "input").unwrap(),
            Err(PropertyError::IncompleteTypeInput(
                crate::json::TypeInputIssue::WorkLimit
            ))
        );
        assert!(
            CheckedRow::default()
                .read(&mut r, f, "feature")
                .unwrap()
                .is_ok()
        );
    }
    #[test]
    fn row_cache_reuses_one_proof_and_refuses_same_length_or_metadata_changes() {
        let mut r = fixture(
            "function F specializes Performances::Evaluation; expr e:F subsets Performances::evaluations;",
        );
        full(&mut r);
        let e = r.resolve_qualified("e").unwrap();
        let mut row = CheckedRow::default();
        assert!(row.read(&mut r, e, "type").unwrap().is_ok());
        let first_steps = row.steps;
        assert!(row.read(&mut r, e, "function").unwrap().is_ok());
        assert!(row.steps - first_steps < 100, "same row reuses report");
        let relation = r.b.elements[e.0]
            .owned_relationships
            .iter()
            .copied()
            .find(|&i| r.b.elements[i].ty == "FeatureTyping")
            .unwrap();
        let original = r.b.elements[relation].props.clone();
        r.b.elements[relation].props.insert(
            "target",
            serde_json::json!([{"@id":uuid::Uuid::new_v4().to_string()}]),
        );
        assert!(matches!(
            row.read(&mut r, e, "type").unwrap(),
            Err(PropertyError::IncompleteTypeProjection(_))
        ));
        r.b.elements[relation].props = original;
        assert!(row.read(&mut r, e, "type").unwrap().is_ok());
        r.b.metadata_associations_incomplete = true;
        r.b.metadata_association_generation = Some(Arc::new(()));
        assert!(matches!(
            row.read(&mut r, e, "type").unwrap(),
            Err(PropertyError::IncompleteTypeProjection(_))
        ));
        r.b.metadata_associations_incomplete = false;
        r.b.metadata_association_generation = Some(Arc::new(()));
        assert!(row.read(&mut r, e, "type").unwrap().is_ok());
        row.steps = crate::eval::MAX_STEPS;
        assert_eq!(
            row.read(&mut r, e, "function").unwrap(),
            Err(PropertyError::IncompleteTypeProjection(
                FeatureTypeIssue::WorkLimit
            ))
        );
        assert!(
            CheckedRow::default()
                .read(&mut r, e, "function")
                .unwrap()
                .is_ok()
        );
    }
    #[test]
    fn cold_large_read_obeys_remaining_budget_without_initializing_legacy_uuid_map() {
        let mut source = String::from(
            "function F specializes Performances::Evaluation; expr e:F subsets Performances::evaluations;",
        );
        for i in 0..10_000 {
            source.push_str(&format!(" feature unrelated{i};"));
        }
        let mut r = fixture(&source);
        full(&mut r);
        let e = r.resolve_qualified("e").unwrap();
        r.by_id = std::sync::Arc::default();
        r.by_id_built_for = usize::MAX;
        let mut row = CheckedRow {
            steps: crate::eval::MAX_STEPS - 10,
            ..CheckedRow::default()
        };
        assert_eq!(
            row.read(&mut r, e, "function").unwrap(),
            Err(PropertyError::IncompleteTypeProjection(
                FeatureTypeIssue::WorkLimit
            ))
        );
        assert!(r.by_id.is_empty());
        assert_eq!(r.by_id_built_for, usize::MAX);
        assert!(r.property(e, "function").is_ok());
        assert!(r.by_id.is_empty());
        assert_eq!(r.by_id_built_for, usize::MAX);
    }
    #[test]
    fn same_length_uuid_remap_uses_certified_handles_even_with_stale_legacy_index() {
        let mut r = fixture(
            "function F specializes Performances::Evaluation; expr e:F subsets Performances::evaluations; package Spare;",
        );
        full(&mut r);
        let e = r.resolve_qualified("e").unwrap();
        let f = r.resolve_qualified("F").unwrap();
        let spare = r.resolve_qualified("Spare").unwrap();
        let mut row = CheckedRow::default();
        assert!(row.read(&mut r, e, "function").unwrap().is_ok());
        r.ensure_by_id();
        let old_index = r.by_id.clone();
        let size = r.b.elements.len();
        let target_id = r.element_id(spare);
        r.override_ids(&std::collections::HashMap::from([
            (r.element_id(f), target_id),
            (target_id, uuid::Uuid::new_v4()),
        ]));
        assert_eq!(r.b.elements.len(), size);
        r.by_id = old_index;
        r.by_id_built_for = size;
        assert_eq!(r.by_id.get(&target_id), Some(&spare.0));
        assert_eq!(
            row.read(&mut r, e, "function").unwrap(),
            Ok(DerivedValue::Reference(Reference::Element(f)))
        );
        assert_eq!(
            r.property(e, "function"),
            Ok(serde_json::json!({"@id":target_id.to_string()}))
        );
        assert_eq!(
            r.by_id.get(&target_id),
            Some(&spare.0),
            "new path must not query or rebuild this separate stale map"
        );
    }
}

#[cfg(test)]
mod owned_source_tests {
    use super::*;
    use crate::model::Model;
    use serde_json::{Value, json};

    fn fixture(source: &str) -> ResolvedModel {
        let mut model = Model::new();
        assert!(
            model
                .add_source("source.kerml", source)
                .diagnostics
                .is_empty()
        );
        ResolvedModel::build(&model)
    }
    fn relation(r: &ResolvedModel) -> ElementRef {
        r.user_elements()
            .find(|&e| r.element_type(e) == "TypeFeaturing")
            .unwrap()
    }
    fn aliases(r: &mut ResolvedModel, e: ElementRef, source: Value) {
        assert_eq!(r.property(e, "featureOfType"), Ok(source.clone()));
        assert_eq!(r.property(e, "source"), Ok(json!([source])));
    }
    #[test]
    fn structural_relationship_reads_refuse_duplicate_owners_and_exhausted_work() {
        let mut r = fixture("class A; feature x : A;");
        let x = r.resolve_qualified("x").unwrap();
        let baseline = r.property(x, "ownedRelationship").unwrap();
        assert!(!baseline.as_array().unwrap().is_empty());
        let relationship = r.b.elements[x.0].owned_relationships[0];
        r.b.elements[x.0].owned_relationships.push(relationship);
        assert!(r.property(x, "ownedRelationship").is_err());

        let mut r = fixture("class A; feature x : A;");
        let x = r.resolve_qualified("x").unwrap();
        let mut row = CheckedRow {
            steps: crate::eval::MAX_STEPS,
            ..Default::default()
        };
        assert!(row.owned_relationships(&mut r, x).is_err());
    }
    #[test]
    fn sparse_and_standalone_source_aliases_are_exact_under_every_policy() {
        for source in [
            "class A; feature x featured by A;",
            "class A; feature x; featuring x by A;",
        ] {
            let mut r = fixture(source);
            let e = relation(&r);
            let x = r.resolve_qualified("x").unwrap();
            let expected = json!({"@id":r.element_id(x).to_string()});
            let old = r.element_properties(e);
            let ids: Vec<_> = r.user_elements().map(|e| r.element_id(e)).collect();
            for policy in [
                ClosurePolicy::Passthrough,
                ClosurePolicy::Closure {
                    include_implied: false,
                },
                ClosurePolicy::Closure {
                    include_implied: true,
                },
            ] {
                r.set_closure_policy(policy);
                aliases(&mut r, e, expected.clone());
                assert_eq!(r.element_properties(e), old);
                let id = r.element_id(e);
                if let Err(report) = r.to_full_json_strict() {
                    assert!(!report.issues.iter().any(|issue| issue.element_id == id
                        && matches!(issue.property.as_str(), "source" | "featureOfType")));
                }
            }
            assert_eq!(
                ids,
                r.user_elements()
                    .map(|e| r.element_id(e))
                    .collect::<Vec<_>>()
            );
        }
    }
    #[test]
    fn present_bad_aliases_and_invalid_carriers_never_fall_back() {
        for (key, value) in [
            ("featureOfType", Value::Null),
            ("featureOfType", json!(false)),
            ("source", json!([])),
            ("source", json!([{"@ref":"x"}])),
            (
                "source",
                json!({"@id":"00000000-0000-0000-0000-000000000001"}),
            ),
            ("relatedElement", json!([])),
            ("owningRelatedElement", Value::Null),
            ("owningFeatureOfType", Value::Null),
        ] {
            let mut r = fixture("class A; feature x featured by A;");
            let e = relation(&r);
            assert!(r.property(e, "source").is_ok());
            r.b.set(e.0, key, value);
            for name in ["source", "featureOfType"] {
                assert!(r.property(e, name).is_err(), "{key}/{name}");
            }
        }
        for kind in 0..5 {
            let mut r = fixture("class A; class B; feature x featured by A; feature y;");
            let e = relation(&r);
            let x = r.resolve_qualified("x").unwrap();
            let y = r.resolve_qualified("y").unwrap();
            let a = r.resolve_qualified("A").unwrap();
            match kind {
                0 => {
                    let id = r.element_id(y);
                    r.b.set(e.0, "featureOfType", json!({"@id":id.to_string()}));
                    r.b.set(e.0, "source", json!([{"@id":r.element_id(x).to_string()}]));
                }
                1 => {
                    let id = r.element_id(a);
                    r.b.set(e.0, "featureOfType", json!({"@id":id.to_string()}));
                }
                2 => {
                    r.b.elements[y.0].owned_relationships = vec![e.0].into();
                }
                3 => {
                    r.b.elements[y.0].id = r.element_id(x);
                }
                _ => {
                    r.b.elements[x.0].ty = "Package";
                }
            }
            assert!(r.property(e, "featureOfType").is_err(), "case {kind}");
        }
    }
    #[test]
    fn generic_aliases_external_ids_and_same_length_mutation_are_revalidated() {
        let mut r = fixture("class A; class B; feature x; feature y; featuring x by A;");
        let e = relation(&r);
        let x = r.resolve_qualified("x").unwrap();
        let y = r.resolve_qualified("y").unwrap();
        let a = r.resolve_qualified("A").unwrap();
        let b = r.resolve_qualified("B").unwrap();
        let xid = json!({"@id":r.element_id(x).to_string()});
        let yid = json!({"@id":r.element_id(y).to_string()});
        aliases(&mut r, e, xid.clone());
        // Shape-preserving source edit must not reuse the previous answer.
        r.b.set(e.0, "featureOfType", yid.clone());
        aliases(&mut r, e, yid.clone());
        r.b.set(e.0, "source", json!([yid]));
        r.b.set(e.0, "target", json!([{"@id":r.element_id(a).to_string()}]));
        assert!(r.property(e, "source").is_ok());
        r.b.set(e.0, "target", json!([{"@id":r.element_id(b).to_string()}]));
        // Opposite target evidence does not define the source's identity.
        assert!(r.property(e, "source").is_ok());
        let mut props = r.b.elements[e.0].props.to_json();
        props.remove("featureOfType");
        props.remove("featuringType");
        let mut replacement = crate::properties::Properties::new();
        for (key, value) in props {
            replacement.insert(&key, value);
        }
        r.b.elements[e.0].props = replacement;
        // Both endpoints stored only under generic singleton-array aliases.
        let expected = json!({"@id":r.element_id(y).to_string()});
        aliases(&mut r, e, expected);
        let external = json!({"@id":"fe1c5e00-959e-4b3b-9512-b0ae7ed3799d"});
        r.b.set(e.0, "source", json!([external.clone()]));
        aliases(&mut r, e, external);
    }
    #[test]
    fn unrelated_target_absence_or_resolution_does_not_hide_known_source() {
        for value in [
            None,
            Some(json!({"@ref":"Missing"})),
            Some(Value::Null),
            Some(json!(false)),
        ] {
            let mut r = fixture("class A; feature x featured by A;");
            let e = relation(&r);
            let x = r.resolve_qualified("x").unwrap();
            let expected = json!({"@id":r.element_id(x).to_string()});
            let mut props = r.b.elements[e.0].props.to_json();
            props.remove("featuringType");
            let mut replacement = crate::properties::Properties::new();
            for (key, value) in props {
                replacement.insert(&key, value);
            }
            r.b.elements[e.0].props = replacement;
            if let Some(value) = value {
                r.b.set(e.0, "featuringType", value);
            }
            aliases(&mut r, e, expected);
        }
    }
    #[test]
    fn related_element_target_tail_does_not_define_source_identity() {
        for tail in [
            vec![],
            vec![json!({"@ref":"Missing"})],
            vec![Value::Null, json!(false)],
        ] {
            let mut r = fixture("class A; feature x featured by A;");
            let e = relation(&r);
            let x = r.resolve_qualified("x").unwrap();
            let source = json!({"@id":r.element_id(x).to_string()});
            let mut related = vec![source.clone()];
            related.extend(tail);
            r.b.set(e.0, "relatedElement", json!(related));
            aliases(&mut r, e, source);
        }
    }
    #[test]
    fn row_budget_accumulates_alias_reads_and_exhaustion_is_retryable() {
        let mut r = fixture("class A; feature x featured by A;");
        let e = relation(&r);
        let (_, spec) = semantic_catalog::property("TypeFeaturing", "featureOfType").unwrap();
        let spec = spec.unwrap();
        let mut row = CheckedRow::default();
        assert!(row.read_owned_source(&mut r, e, spec).unwrap().is_ok());
        let first = row.steps;
        assert!(row.read_owned_source(&mut r, e, spec).unwrap().is_ok());
        assert!(row.steps > first);
        row.steps = crate::eval::MAX_STEPS;
        assert_eq!(
            row.read_owned_source(&mut r, e, spec),
            Some(Err(PropertyError::NotComputed))
        );
        assert!(r.property(e, "source").is_ok());
        r.b.positional_planning = true;
        assert!(r.property(e, "source").is_err());
        r.b.positional_planning = false;
        assert!(r.property(e, "source").is_ok());
    }
    #[test]
    fn source_projection_replays_across_all_library_representations() {
        use crate::{libcache::LibraryCache, prepared::PreparedLibrary};
        use std::sync::Arc;
        let mut library = Model::new();
        library.add_library_source("lib.kerml", "standard library package L {class A;}");
        library.record_library_cache();
        ResolvedModel::build(&library);
        let cache =
            LibraryCache::from_bytes(&library.take_recorded_library_cache().unwrap().to_bytes())
                .unwrap();
        let prepared = library.prepare_library().unwrap();
        let decoded =
            Arc::new(PreparedLibrary::from_bytes(&prepared.to_bytes(61).unwrap(), 61).unwrap());
        let mut expected = None;
        for mode in 0..4 {
            let mut model = Model::new();
            match mode {
                2 => Arc::clone(&prepared).install(&mut model).unwrap(),
                3 => Arc::clone(&decoded).install(&mut model).unwrap(),
                _ => {
                    model.add_library_source("lib.kerml", "standard library package L {class A;}");
                    if mode == 1 {
                        model.set_library_cache(cache.clone());
                    }
                }
            }
            model.add_source("source.kerml", "feature x featured by L::A;");
            let mut r = ResolvedModel::build(&model);
            let e = relation(&r);
            let x = r.resolve_qualified("x").unwrap();
            let ids: Vec<_> = r.user_elements().map(|e| r.element_id(e)).collect();
            if let Some(expected) = &expected {
                assert_eq!(&ids, expected);
            } else {
                expected = Some(ids);
            }
            let expected = json!({"@id":r.element_id(x).to_string()});
            aliases(&mut r, e, expected);
        }
    }
}

#[cfg(test)]
#[path = "definition_usage_tests.rs"]
mod definition_usage_tests;
