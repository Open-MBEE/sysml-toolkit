//! Repository adapter with a bounded structural-context readiness
//! certificate. Invocation and owned-result families remain explicitly outside it.
use super::{Comparison, Evidence, Incomplete, Inputs, Projection};
use crate::json::{
    Builder,
    provider_completeness::ProviderCompleteness,
    semantic_ownership,
    structural_index::{StoredStructure, StoredTyping},
    type_relations::{CompositionOwner, RelationFact, TypeRelations, endpoint_with_carrier},
};
use crate::metaclass::conforms;
use std::{
    collections::{HashMap, HashSet},
    sync::Arc,
};

pub(super) struct RepositoryTyping<'a> {
    builder: &'a mut Builder,
    contextual_active: HashSet<usize>,
    contextual_owners: HashMap<usize, CompositionOwner>,
    structure: Arc<StoredStructure>,
    typing: Arc<StoredTyping>,
    ownership: Option<Arc<semantic_ownership::SemanticOwnership>>,
    metadata_generation: Option<Arc<()>>,
    publication: crate::json::publication::Revision,
    relations: TypeRelations,
    providers: ProviderCompleteness,
    retained: Arc<crate::json::implied::RetainedTypings>,
    retained_plan: Option<Arc<crate::json::implied::SupportedImpliedSpecializations>>,
}
fn charge(steps: &mut usize, amount: usize) -> Result<(), Incomplete> {
    *steps = steps.saturating_add(amount);
    if *steps > crate::eval::MAX_STEPS {
        Err(Incomplete::Budget)
    } else {
        Ok(())
    }
}
impl<'a> RepositoryTyping<'a> {
    pub(super) fn new(builder: &'a mut Builder, steps: &mut usize) -> Result<Self, Incomplete> {
        if builder.positional_planning {
            return Err(Incomplete::UnsupportedProjection);
        }
        let retained = builder.retained_typing_edges(steps).ok_or({
            if *steps > crate::eval::MAX_STEPS {
                Incomplete::Budget
            } else {
                Incomplete::UnsupportedProjection
            }
        })?;
        let structure = StoredStructure::for_query(builder, steps).ok_or({
            if *steps > crate::eval::MAX_STEPS {
                Incomplete::Budget
            } else {
                Incomplete::InvalidRelationship
            }
        })?;
        if !structure.ids_unique {
            return Err(Incomplete::InvalidElement);
        }
        let typing = structure.typing(builder, steps).ok_or({
            if *steps > crate::eval::MAX_STEPS {
                Incomplete::Budget
            } else {
                Incomplete::InvalidRelationship
            }
        })?;
        let retained_plan = builder.supported_implied.clone();
        let ownership = builder.semantic_ownership.clone();
        let metadata_generation = builder.metadata_association_generation.clone();
        let publication = builder.publication.revision();
        Ok(Self {
            contextual_active: HashSet::new(),
            contextual_owners: HashMap::new(),
            publication,
            builder,
            ownership,
            metadata_generation,
            structure,
            typing,
            retained,
            retained_plan,
            relations: TypeRelations::default(),
            providers: ProviderCompleteness::default(),
        })
    }
    pub(super) fn project(&mut self, feature: usize, steps: &mut usize) -> Projection {
        if self.contextual_active.len() > crate::json::MAX_RESOLUTION_DEPTH
            || !self.contextual_active.insert(feature)
        {
            return Projection {
                candidates: Vec::new(),
                graph_issue: Some(Incomplete::UnsupportedProjection),
                required_issue: None,
                steps: *steps,
            };
        }
        let result = super::project(
            self,
            feature,
            steps,
            crate::eval::MAX_STEPS,
            crate::json::MAX_RESOLUTION_DEPTH,
        );
        self.contextual_active.remove(&feature);
        result
    }
    fn current(&self) -> bool {
        let ownership_current = match (&self.ownership, &self.builder.semantic_ownership) {
            (None, None) => true,
            (Some(stored), Some(current)) => Arc::ptr_eq(stored, current),
            _ => false,
        };
        let metadata_current = match (
            &self.metadata_generation,
            &self.builder.metadata_association_generation,
        ) {
            (None, None) => true,
            (Some(stored), Some(current)) => Arc::ptr_eq(stored, current),
            _ => false,
        };
        let retained_current = match (&self.retained_plan, &self.builder.supported_implied) {
            (None, None) => true,
            (Some(old), Some(current)) => Arc::ptr_eq(old, current),
            _ => false,
        };
        self.structure.is_current(self.builder)
            && ownership_current
            && metadata_current
            && retained_current
            && self
                .publication
                .same_as(&self.builder.publication.revision())
    }
    fn carrier(&self, relationship: usize, steps: &mut usize) -> Result<Option<usize>, Incomplete> {
        let result = semantic_ownership::checked_relationship_carrier(
            self.builder,
            &self.structure,
            relationship,
            steps,
        );
        result.ok_or(Incomplete::InvalidRelationship)
    }
    fn endpoint(
        &mut self,
        source: usize,
        relation: usize,
        kind: &str,
        steps: &mut usize,
    ) -> Result<usize, Incomplete> {
        if !self.builder.static_chain_row_current(relation) {
            return Err(Incomplete::UnsupportedProjection);
        }
        let carrier = self.carrier(relation, steps)?;
        endpoint_with_carrier(
            self.builder,
            source,
            carrier,
            relation,
            &[
                "specific",
                "typedFeature",
                "subsettingFeature",
                "redefiningFeature",
                "referencingFeature",
                "crossingFeature",
            ],
            &[
                "general",
                "type",
                "subsettedFeature",
                "redefinedFeature",
                "referencedFeature",
                "crossedFeature",
            ],
            kind,
            steps,
        )
        .ok_or({
            if *steps > crate::eval::MAX_STEPS {
                Incomplete::Budget
            } else {
                Incomplete::InvalidRelationship
            }
        })
    }
    fn owned_relationships(
        &self,
        feature: usize,
        steps: &mut usize,
    ) -> Result<Vec<usize>, Incomplete> {
        let rows = semantic_ownership::owned_relationships(self.builder, feature)
            .ok_or(Incomplete::InvalidRelationship)?;
        charge(steps, rows.len())?;
        let relationships = rows.iter().collect::<Vec<_>>();
        let mut seen = HashSet::new();
        for &relationship in &relationships {
            if !seen.insert(relationship) || self.carrier(relationship, steps)? != Some(feature) {
                return Err(Incomplete::InvalidRelationship);
            }
        }
        Ok(relationships)
    }
    /// An intentionally narrow but complete applicability audit for obligations
    /// that can change this Feature's typing closure. Every required path is
    /// checked later against the collected graph; this never adds an edge.
    fn requirements(
        &mut self,
        feature: usize,
        owned: &[usize],
        typings: &[usize],
        original: Option<usize>,
        steps: &mut usize,
    ) -> Result<(Vec<usize>, Vec<usize>), Incomplete> {
        let mut owner_types = None;
        let element = &self.builder.elements[feature];
        if conforms(element.ty, "OccurrenceUsage")
            && element.props.get("isComposite").and_then(|v| v.as_bool()) == Some(true)
        {
            let owner = self
                .relations
                .owning_type(self.builder, feature, steps)
                .ok_or(Incomplete::InvalidRelationship)?;
            if let Some(owner) =
                owner.filter(|&owner| conforms(self.builder.elements[owner].ty, "Feature"))
            {
                charge(steps, 1)?;
                let certificate = if let Some(certificate) = self.contextual_owners.get(&owner) {
                    *certificate
                } else {
                    // The complete owner projection uses the same stored graph,
                    // canonical obligations and budget. Recursion through owner
                    // typing dependencies is bounded and never cached partially.
                    let projection = self.project(owner, steps);
                    if let Some(issue) = projection.graph_issue.or(projection.required_issue) {
                        return Err(issue);
                    }
                    charge(steps, projection.candidates.len())?;
                    let certificate = CompositionOwner {
                        object: projection
                            .candidates
                            .iter()
                            .any(|&ty| conforms(self.builder.elements[ty].ty, "Structure")),
                        occurrence: projection
                            .candidates
                            .iter()
                            .any(|&ty| conforms(self.builder.elements[ty].ty, "Class")),
                    };
                    self.contextual_owners.insert(owner, certificate);
                    certificate
                };
                owner_types = Some(certificate);
            }
        }
        self.relations
            .feature_requirements(
                self.builder,
                feature,
                owned,
                typings,
                original,
                owner_types,
                steps,
            )
            .map_err(|error| match error {
                super::super::type_relations::FeatureRequirementsFailure::Unsupported => {
                    Incomplete::MissingRequiredFamilies
                }
                super::super::type_relations::FeatureRequirementsFailure::InvalidRelationship => {
                    Incomplete::InvalidRelationship
                }
            })
    }
}
impl Evidence for RepositoryTyping<'_> {
    fn inputs(&mut self, feature: usize, steps: &mut usize) -> Result<Inputs, Incomplete> {
        charge(steps, 1)?;
        if !self.current()
            || (!self.builder.dynamic_evidence_current(feature)
                || !self.builder.result_redefinition_evidence_current(feature))
        {
            return Err(Incomplete::UnsupportedProjection);
        }
        if !conforms(
            self.builder
                .elements
                .get(feature)
                .ok_or(Incomplete::InvalidElement)?
                .ty,
            "Feature",
        ) {
            return Err(Incomplete::InvalidElement);
        }
        let owned = self.owned_relationships(feature, steps)?;
        // Existing checked conjugation helper validates owned cardinality,
        // identity and scalar/generic aliases. No private normalization graph.
        let original = self
            .relations
            .owned_conjugation(self.builder, feature, steps)
            .ok_or(Incomplete::InvalidRelationship)?;
        let inverse = self
            .typing
            .relationships
            .get(&feature)
            .map_or(&[][..], Vec::as_slice);
        charge(steps, inverse.len())?;
        let inverse = inverse.to_vec();
        let mut typings = Vec::new();
        let mut features = Vec::new();
        let mut graph_issue = self
            .typing
            .sources_incomplete
            .then_some(Incomplete::InvalidRelationship);
        for relationship in inverse {
            let kind = self.builder.elements[relationship].ty;
            if conforms(kind, "FeatureTyping") {
                typings.push(self.endpoint(feature, relationship, "Type", steps)?);
            } else if original.is_none()
                && conforms(kind, "Subsetting")
                && !conforms(kind, "CrossSubsetting")
            {
                features.push(self.endpoint(feature, relationship, "Feature", steps)?);
            }
        }
        if let Some(original) = original {
            if conforms(self.builder.elements[original].ty, "Feature") {
                features.push(original);
            }
        } else {
            let mut last = None;
            for &relationship in &owned {
                if !conforms(self.builder.elements[relationship].ty, "FeatureChaining") {
                    continue;
                }
                let carrier = self.carrier(relationship, steps)?;
                // Every link is validated, not just the last surviving target.
                last = Some(
                    endpoint_with_carrier(
                        self.builder,
                        feature,
                        carrier,
                        relationship,
                        &["featureChained"],
                        &["chainingFeature"],
                        "Feature",
                        steps,
                    )
                    .ok_or(Incomplete::InvalidRelationship)?,
                );
            }
            if let Some(last) = last {
                features.push(last);
            }
        }
        let retained = self.retained.get(&feature).map_or(&[][..], Vec::as_slice);
        charge(steps, retained.len())?;
        for &(kind, id) in retained {
            if original.is_some() && !conforms(kind, "FeatureTyping") {
                continue;
            }
            if conforms(kind, "CrossSubsetting") {
                continue;
            }
            let Some(target) = self.builder.element_index_of_uuid(id) else {
                graph_issue.get_or_insert(Incomplete::ExternalEndpoint);
                continue;
            };
            let expected = if conforms(kind, "FeatureTyping") {
                "Type"
            } else {
                "Feature"
            };
            if !conforms(self.builder.elements[target].ty, expected) {
                graph_issue.get_or_insert(Incomplete::InvalidElement);
                continue;
            }
            if expected == "Type" {
                typings.push(target);
            } else {
                features.push(target);
            }
        }
        if original.is_none()
            && (self.builder.is_parameter(feature)
                || self.builder.elements[feature]
                    .props
                    .get("isEnd")
                    .and_then(|value| value.as_bool())
                    == Some(true))
        {
            // Reuse stabilized positional evidence. This path never starts an
            // unbudgeted planning pass or turns an absent table into empty.
            let ready = self
                .builder
                .elem_scope
                .get(&feature)
                .copied()
                .is_some_and(|scope| self.providers.scope(self.builder, scope, steps));
            let owner = self
                .relations
                .owning_type(self.builder, feature, steps)
                .ok_or(Incomplete::InvalidRelationship)?;
            if !ready
                || self
                    .builder
                    .effective_positional_redefinitions()
                    .is_none_or(|plan| owner.is_some_and(|owner| plan.incomplete.contains(&owner)))
            {
                graph_issue.get_or_insert(Incomplete::UnsupportedProjection);
            } else {
                let targets = self
                    .builder
                    .effective_positional_redefinitions()
                    .unwrap()
                    .targets
                    .get(&feature)
                    .map_or(&[][..], Vec::as_slice);
                charge(steps, targets.len())?;
                for &target in targets {
                    if !self
                        .builder
                        .elements
                        .get(target)
                        .is_some_and(|e| conforms(e.ty, "Feature"))
                    {
                        graph_issue.get_or_insert(Incomplete::InvalidElement);
                    } else {
                        features.push(target);
                    }
                }
            }
        }
        let requirements = self.requirements(feature, &owned, &typings, original, steps);
        let (required_features, required_typings, required_issue) = match requirements {
            Ok((features, typings)) => (features, typings, None),
            Err(Incomplete::Budget) => return Err(Incomplete::Budget),
            Err(issue) => (Vec::new(), Vec::new(), Some(issue)),
        };
        charge(steps, 0)?;
        Ok(Inputs {
            typings,
            features,
            graph_issue,
            required_issue,
            required_features,
            required_typings,
        })
    }
    fn specializes(&mut self, specific: usize, general: usize, steps: &mut usize) -> Comparison {
        if !self.current() {
            return Comparison::Unknown;
        }
        match self
            .relations
            .specializes(self.builder, specific, general, steps)
        {
            RelationFact::Yes => Comparison::Yes,
            RelationFact::No => Comparison::No,
            RelationFact::Unknown => Comparison::Unknown,
        }
    }
    fn is_behavior(&self, element: usize) -> bool {
        self.builder
            .elements
            .get(element)
            .is_some_and(|e| conforms(e.ty, "Behavior"))
    }
    fn is_function(&self, element: usize) -> bool {
        self.builder
            .elements
            .get(element)
            .is_some_and(|e| conforms(e.ty, "Function"))
    }
}
#[cfg(test)]
mod readiness_lifecycle_tests {
    use super::*;
    use crate::{json::ResolvedModel, model::Model};
    #[test]
    fn metadata_snapshot_change_refuses_old_proof_and_repair_retries_fresh() {
        let library = "standard library package Base {classifier Anything; feature things:Anything;} standard library package Occurrences {class Occurrence specializes Base::Anything; feature occurrences:Occurrence subsets Base::things;} standard library package Performances {behavior Performance specializes Occurrences::Occurrence; function Evaluation specializes Performance; step performances:Performance subsets Occurrences::occurrences; expr evaluations:Evaluation subsets performances;}";
        let mut model = Model::new();
        assert!(
            model
                .add_library_source("bases.kerml", library)
                .diagnostics
                .is_empty()
        );
        assert!(model.add_source("source.kerml","function F specializes Performances::Evaluation; expr e:F subsets Performances::evaluations;").diagnostics.is_empty());
        let mut r = ResolvedModel::build(&model);
        let feature = r.resolve_qualified("e").unwrap().0;
        let function = r.resolve_qualified("F").unwrap().0;
        let mut proof = RepositoryTyping::new(&mut r.b, &mut 0).unwrap();
        assert_eq!(
            proof.project(feature, &mut 0).function(&proof),
            Ok(Some(function))
        );
        // Reconstructing an equivalent retained table still revokes the old
        // snapshot: unchanged rows/Boolean readiness are not its authority.
        proof.builder.supported_implied = None;
        proof.builder.retained_typing_edges(&mut 0).unwrap();
        assert!(!proof.current());
        assert!(proof.project(feature, &mut 0).function(&proof).is_err());
        drop(proof);
        let mut proof = RepositoryTyping::new(&mut r.b, &mut 0).unwrap();
        assert_eq!(
            proof.project(feature, &mut 0).function(&proof),
            Ok(Some(function))
        );
        proof.builder.metadata_associations_incomplete = true;
        proof.builder.metadata_association_generation = Some(Arc::new(()));
        assert!(!proof.current());
        assert!(proof.project(feature, &mut 0).function(&proof).is_err());
        drop(proof);
        let mut unproved = RepositoryTyping::new(&mut r.b, &mut 0).unwrap();
        let incomplete = unproved.project(feature, &mut 0);
        assert_eq!(
            incomplete.required_issue,
            Some(Incomplete::MissingRequiredFamilies)
        );
        assert!(
            incomplete.function(&unproved).is_err(),
            "metadata also qualifies specialization negatives"
        );
        unproved.builder.metadata_associations_incomplete = false;
        unproved.builder.metadata_association_generation = Some(Arc::new(()));
        drop(unproved);
        let mut repaired = RepositoryTyping::new(&mut r.b, &mut 0).unwrap();
        assert_eq!(
            repaired.project(feature, &mut 0).function(&repaired),
            Ok(Some(function))
        );
    }
}
