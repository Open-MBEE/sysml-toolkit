//! Repository adapter. Compatibility derived booleans and execution are untouched.
#[cfg(test)]
use super::super::structural_index::Carrier;
use super::super::{
    Builder, ElementRef, ResolvedModel,
    type_relations::{RelationFact, TypeRelations},
};
use super::super::{semantic_ownership, structural_index::StoredStructure};
use super::*;
use crate::metaclass::conforms;
use std::sync::Arc;
use uuid::Uuid;
/// Forward the report's remaining budget into readers bounded by MAX_STEPS.
/// This preserves smaller private proof limits before the reader allocates.
fn structural_read<T>(
    budget: &mut Budget,
    read: impl FnOnce(&mut usize) -> Option<T>,
) -> Evidence<T> {
    budget.charge(0)?;
    let limit = budget.limit.min(crate::eval::MAX_STEPS);
    let offset = crate::eval::MAX_STEPS - limit;
    let mut steps = offset.saturating_add(budget.used);
    let result = read(&mut steps);
    budget.used = steps.saturating_sub(offset);
    budget.charge(0)?;
    if steps > crate::eval::MAX_STEPS {
        return Err(WorkLimit);
    }
    result.ok_or(MissingOrMalformedMembership)
}

use ModelLevelEvaluabilityUnknown::*;

impl ResolvedModel {
    /// Classify the normative model-level eligibility rule using bounded,
    /// checked relationship evidence. Unknown is never a compatibility fallback.
    /// This is distinct from execution and its EvaluationReport: Evaluable
    /// expressions can still fail with Unbound, DivisionByZero, etc. The query
    /// does not certify complete model validity or required library ancestry.
    ///
    /// The first supported scope covers literal/null/metadata leaves, ordinary
    /// kernel feature references, and directly provable general-expression
    /// branches. Complete callee argument mapping, derived featuring/snapshot
    /// contexts, and inherited input/result direction remain explicit Unknown.
    /// The legacy `isModelLevelEvaluable` derived boolean is unchanged.
    pub fn model_level_evaluability(
        &mut self,
        expression: ElementRef,
    ) -> ModelLevelEvaluabilityReport {
        self.model_level_evaluability_with_budget(expression, 0)
    }
    pub(in crate::json) fn model_level_evaluability_with_budget(
        &mut self,
        expression: ElementRef,
        initial: usize,
    ) -> ModelLevelEvaluabilityReport {
        let mut proof = Proof::new(
            RepositoryEvidence::new(self),
            crate::eval::MAX_STEPS,
            super::super::MAX_RESOLUTION_DEPTH,
        );
        proof.budget.used = initial;
        proof.report(expression.0)
    }
}

/// One complete identity/carrier index per query. No name-based membership or
/// feature-value fallback is used; malformed graph entries remain visible.
struct StoredGraph {
    publication: crate::json::publication::Revision,
    ids: Arc<crate::layered::IdMap<Uuid, usize>>,
    structure: Arc<StoredStructure>,
    ownership: Option<Arc<semantic_ownership::SemanticOwnership>>,
}
impl StoredGraph {
    fn build(model: &mut ResolvedModel, budget: &mut Budget) -> Evidence<Self> {
        let structure = structural_read(budget, |steps| {
            StoredStructure::for_query(&mut model.b, steps)
        })?;
        if !structure.ids_unique {
            return Err(InvalidElement);
        }
        // The shared getter installs this exact immutable UUID projection.
        let ids = Arc::clone(model.b.id_index.as_ref().ok_or(InvalidElement)?);
        let b = &model.b;
        let (generic_from, generic_to) =
            match (&model.b.implied, &b.semantic_ownership, b.implied_from) {
                (None, None, None) => (b.elements.len(), b.elements.len()),
                (Some(table), Some(view), Some(from))
                    if table.from == from
                        && from <= table.owned_results_from
                        && table.owned_results_from <= b.elements.len()
                        && view.matches_suffix(b) =>
                {
                    (from, table.owned_results_from)
                }
                _ => return Err(MissingOrMalformedMembership),
            };
        // Reuse the raw immutable topology. Validate the effective carrier
        // certificate without allocating another whole-model carrier vector.
        budget.charge(b.elements.len())?;
        for (index, element) in b.elements.iter().enumerate() {
            let carrier = if conforms(element.ty, "Relationship") {
                structural_read(budget, |steps| {
                    semantic_ownership::checked_relationship_carrier(b, &structure, index, steps)
                })?
            } else {
                // Ordinary generated Features are children, never relationship
                // carriers. Projection cannot repair malformed raw ownership.
                if structure.carrier(b, index) != Some(None) {
                    return Err(MissingOrMalformedMembership);
                }
                None
            };
            // The old generic prefix consists solely of childless relationships
            // carried by authored rows. The newer owned-result tail has a
            // different certified shape, so do not relax or apply this prefix
            // certificate merely because both families share an ownership view.
            if (generic_from..generic_to).contains(&index)
                && (carrier.is_none_or(|owner| owner >= generic_from)
                    || !conforms(element.ty, "Relationship")
                    || element.owning_relationship.is_some()
                    || !element.children.is_empty()
                    || !element.owned_relationships.is_empty())
            {
                return Err(MissingOrMalformedMembership);
            }
        }
        Ok(Self {
            publication: b.publication.revision(),
            ids,
            structure,
            ownership: b.semantic_ownership.clone(),
        })
    }
    fn current(&self, b: &Builder) -> bool {
        self.publication.same_as(&b.publication.revision())
            && self.structure.is_current(b)
            && match (&self.ownership, &b.semantic_ownership) {
                (None, None) => true,
                (Some(stored), Some(current)) => Arc::ptr_eq(stored, current),
                _ => false,
            }
    }
    fn relationships(
        &self,
        b: &Builder,
        owner: usize,
        budget: &mut Budget,
    ) -> Evidence<Vec<usize>> {
        if !self.current(b) {
            return Err(MissingOrMalformedMembership);
        }
        b.elements.get(owner).ok_or(InvalidElement)?;
        let relationships = semantic_ownership::owned_relationships(b, owner)
            .ok_or(MissingOrMalformedMembership)?;
        budget.charge(relationships.len())?;
        for relationship in relationships.iter() {
            if structural_read(budget, |steps| {
                semantic_ownership::checked_relationship_carrier(
                    b,
                    &self.structure,
                    relationship,
                    steps,
                )
            })? != Some(owner)
            {
                return Err(MissingOrMalformedMembership);
            }
        }
        Ok(relationships.iter().collect())
    }
    fn member(
        &self,
        b: &Builder,
        owner: usize,
        membership: usize,
        budget: &mut Budget,
    ) -> Evidence<usize> {
        if !self.current(b) {
            return Err(MissingOrMalformedMembership);
        }
        structural_read(budget, |steps| {
            super::super::membership_evidence::member(b, &self.structure, owner, membership, steps)
        })
    }
    fn features(
        &self,
        b: &Builder,
        owner: usize,
        budget: &mut Budget,
    ) -> Evidence<Vec<(usize, usize)>> {
        if !semantic_ownership::owned_feature_projection_complete(b, owner) {
            return Err(UnsupportedExpression);
        }
        if !structural_read(budget, |steps| self.structure.membership_domains(b, steps))?
            .owner_complete(owner)
        {
            return Err(MissingOrMalformedMembership);
        }
        let mut features = Vec::new();
        for rel in self.relationships(b, owner, budget)? {
            if !conforms(b.elements[rel].ty, "FeatureMembership") {
                continue;
            }
            let feature = self.member(b, owner, rel, budget)?;
            if !conforms(b.elements[feature].ty, "Feature") {
                return Err(MissingOrMalformedMembership);
            }
            features.push((rel, feature));
        }
        Ok(features)
    }
    fn first_member(
        &self,
        b: &Builder,
        owner: usize,
        excluded_kind: &str,
        kind: Option<&str>,
        budget: &mut Budget,
    ) -> Evidence<usize> {
        for rel in self.relationships(b, owner, budget)? {
            let ty = b.elements[rel].ty;
            if conforms(ty, "Membership") && !conforms(ty, excluded_kind) {
                let member = self.member(b, owner, rel, budget)?;
                if kind.is_some_and(|kind| !conforms(b.elements[member].ty, kind)) {
                    return Err(MissingOrMalformedMembership);
                }
                return Ok(member);
            }
        }
        Err(MissingOrMalformedMembership)
    }
    fn valuation(
        &self,
        b: &Builder,
        feature: usize,
        budget: &mut Budget,
    ) -> Evidence<Option<usize>> {
        if !self.current(b) {
            return Err(MissingOrMalformedValuation);
        }
        structural_read(budget, |steps| {
            super::super::membership_evidence::valuation(b, &self.structure, feature, steps)
                .map(|v| v.map(|(_, expression)| expression))
        })
        .map_err(|reason| {
            if reason == WorkLimit {
                reason
            } else {
                MissingOrMalformedValuation
            }
        })
    }
}
struct RepositoryEvidence<'a> {
    model: &'a mut ResolvedModel,
    graph: Option<StoredGraph>,
    relations: TypeRelations,
    self_target: Option<Option<usize>>,
}
impl<'a> RepositoryEvidence<'a> {
    fn new(model: &'a mut ResolvedModel) -> Self {
        Self {
            model,
            graph: None,
            relations: TypeRelations::default(),
            self_target: None,
        }
    }
    fn prepare(&mut self, budget: &mut Budget) -> Evidence<()> {
        if let Some(graph) = &self.graph {
            // Rebuilding only topology would retain stale TypeRelations/core
            // memo facts. An interrupted proof must instead be retried fresh.
            if !graph.current(&self.model.b) {
                return Err(MissingOrMalformedMembership);
            }
        } else {
            self.graph = Some(StoredGraph::build(self.model, budget)?);
        }
        budget.charge(1)
    }
    fn self_conformance(&mut self, referent: usize, budget: &mut Budget) -> ModelLevelEvaluability {
        if self.self_target.is_none() {
            if let Err(reason) = budget.charge(self.model.b.lib_qnames.len()) {
                return Unknown(reason);
            }
            let mut target = None;
            let mut ambiguous = false;
            for (id, name) in &self.model.b.lib_qnames {
                if name.as_slice() == ["Base", "Anything", "self"] {
                    match self
                        .graph
                        .as_ref()
                        .and_then(|graph| graph.ids.get(id))
                        .copied()
                    {
                        Some(element)
                            if element < self.model.b.lib_boundary
                                && conforms(self.model.b.elements[element].ty, "Feature") =>
                        {
                            if target.is_some_and(|old| old != element) {
                                ambiguous = true;
                            }
                            target = Some(element);
                        }
                        _ => ambiguous = true,
                    }
                }
            }
            self.self_target = Some(if ambiguous { None } else { target });
        }
        let Some(Some(target)) = self.self_target else {
            return Unknown(IncompleteSelfConformance);
        };
        match structural_read(budget, |steps| {
            Some(
                self.relations
                    .specializes(&mut self.model.b, referent, target, steps),
            )
        }) {
            Ok(RelationFact::Yes) => Yes,
            Ok(RelationFact::No) => No,
            Ok(RelationFact::Unknown) => Unknown(IncompleteSelfConformance),
            Err(reason) => Unknown(reason),
        }
    }
}
impl EvidenceProvider for RepositoryEvidence<'_> {
    fn kind(&mut self, node: usize, budget: &mut Budget) -> Evidence<Kind> {
        budget.charge(1)?;
        let e = self.model.b.elements.get(node).ok_or(InvalidElement)?;
        if !conforms(e.ty, "Expression") {
            return Err(InvalidElement);
        }
        if conforms(e.ty, "CalculationUsage") || conforms(e.ty, "ConstraintUsage") {
            return Ok(Kind::Forbidden);
        }
        if conforms(e.ty, "LiteralExpression")
            || matches!(e.ty, "NullExpression" | "MetadataAccessExpression")
        {
            return Ok(Kind::Leaf);
        }
        if e.ty == "FeatureReferenceExpression" {
            return Ok(Kind::Reference);
        }
        if conforms(e.ty, "ConstructorExpression") {
            return Ok(Kind::Constructor);
        }
        if conforms(e.ty, "InvocationExpression") {
            return Ok(Kind::Invocation);
        }
        if matches!(e.ty, "Expression" | "BooleanExpression") {
            return Ok(Kind::General);
        }
        Err(UnsupportedExpression)
    }
    fn leaf(&mut self, node: usize, budget: &mut Budget) -> Evidence<()> {
        if self.model.b.elements[node].ty == "MetadataAccessExpression" {
            self.prepare(budget)?;
            self.graph.as_ref().unwrap().first_member(
                &self.model.b,
                node,
                "FeatureMembership",
                None,
                budget,
            )?;
        }
        Ok(())
    }
    fn reference(&mut self, node: usize, budget: &mut Budget) -> Evidence<ReferenceEvidence> {
        self.prepare(budget)?;
        let referent = self.graph.as_ref().unwrap().first_member(
            &self.model.b,
            node,
            "ParameterMembership",
            Some("Feature"),
            budget,
        )?;
        let self_conformance = self.self_conformance(referent, budget);
        let metadata_owner = match structural_read(budget, |steps| {
            self.relations
                .owning_type(&mut self.model.b, referent, steps)
        }) {
            Ok(Some(owner))
                if conforms(self.model.b.elements[owner].ty, "Metaclass")
                    || conforms(self.model.b.elements[owner].ty, "MetadataFeature") =>
            {
                Yes
            }
            Ok(_) => No,
            Err(reason) => Unknown(reason),
        };
        let unfeatured = match structural_read(budget, |steps| {
            self.relations
                .audited_featuring_domain(&mut self.model.b, &[referent], steps)
        }) {
            Ok(true) => match structural_read(budget, |steps| {
                self.relations
                    .featuring_types(&mut self.model.b, referent, steps)
            }) {
                Ok(types) if types.is_empty() => Yes,
                Ok(_) => No,
                Err(WorkLimit) => Unknown(WorkLimit),
                Err(_) => Unknown(IncompleteFeaturing),
            },
            Err(WorkLimit) => Unknown(WorkLimit),
            _ => Unknown(IncompleteFeaturing),
        };
        let valuation = self
            .graph
            .as_ref()
            .unwrap()
            .valuation(&self.model.b, referent, budget);
        Ok(ReferenceEvidence {
            referent,
            self_conformance,
            expression: conforms(self.model.b.elements[referent].ty, "Expression"),
            metadata_owner,
            unfeatured,
            valuation,
        })
    }
    fn call(
        &mut self,
        node: usize,
        constructor: bool,
        budget: &mut Budget,
    ) -> Evidence<CallEvidence> {
        let mut numeric_callee = None;
        let supplied =
            if constructor && self.model.b.graph_format == crate::model::GraphFormat::CanonicalV3 {
                let mut issue = IncompleteArgumentMapping;
                let mapping = structural_read(budget, |steps| {
                    let report = self
                        .model
                        .constructor_binding_report_with_budget(ElementRef(node), *steps);
                    *steps = report.steps;
                    match report.arguments {
                        Ok(arguments) => {
                            Some(arguments.bindings.into_iter().map(|b| b.value.0).collect())
                        }
                        Err(super::super::ConstructorBindingIssue::InvalidRelationship) => {
                            issue = MissingOrMalformedValuation;
                            None
                        }
                        Err(_) => None,
                    }
                })
                .map_err(|reason| if reason == WorkLimit { reason } else { issue });
                Some(mapping)
            } else if !constructor
                && self
                    .model
                    .b
                    .elements
                    .get(node)
                    .is_some_and(|e| matches!(e.ty, "InvocationExpression" | "OperatorExpression"))
            {
                let mut issue = IncompleteArgumentMapping;
                let mapping = structural_read(budget, |steps| {
                    let report = self
                        .model
                        .invocation_binding_report_with_budget(ElementRef(node), *steps);
                    *steps = report.steps;
                    match report.arguments {
                        Ok(arguments) => {
                            if self.model.b.elements[node].ty == "OperatorExpression" {
                                numeric_callee = Some(arguments.callee);
                            }
                            Some(arguments.bindings.into_iter().map(|b| b.value.0).collect())
                        }
                        Err(super::super::InvocationBindingIssue::InvalidRelationship) => {
                            issue = MissingOrMalformedValuation;
                            None
                        }
                        Err(_) => None,
                    }
                })
                .map_err(|reason| if reason == WorkLimit { reason } else { issue });
                Some(mapping)
            } else {
                None
            };
        self.prepare(budget)?;
        // Operator/trigger overrides need a unique designated-name resolver;
        // the older ordered compatibility lookup is not complete evidence.
        if (conforms(self.model.b.elements[node].ty, "OperatorExpression")
            && numeric_callee.is_none())
            || self.model.b.elements[node].ty == "TriggerInvocationExpression"
        {
            return Err(IncompleteCallee);
        }
        if numeric_callee.is_none() {
            self.graph
                .as_ref()
                .unwrap()
                .first_member(
                    &self.model.b,
                    node,
                    "FeatureMembership",
                    Some(if constructor { "Type" } else { "Function" }),
                    budget,
                )
                .map_err(|reason| {
                    if reason == WorkLimit {
                        reason
                    } else {
                        IncompleteCallee
                    }
                })?;
        }
        // InstantiatedType membership is not Expression.function evidence.
        // The latter redefines Step.behavior and follows the effective Feature
        // typing graph. Missing required invocation typing, inherited types,
        // or conflicting explicit typing must not turn a user callee into a
        // decisive negative. The constructor rule has no function conjunct.
        let function = if constructor {
            Yes
        } else if let Some(callee) = numeric_callee {
            budget.charge(self.model.b.elements.len())?;
            if self
                .model
                .function_is_model_level_evaluable(&super::super::Reference::Element(callee))
            {
                Yes
            } else {
                Unknown(IncompleteCallee)
            }
        } else {
            Unknown(IncompleteCallee)
        };
        // Inspect every owned parameter value before the mapping boundary;
        // neither excess arguments nor absent FeatureValue members disappear.
        // Complete call mapping remains a shared-provider prerequisite: no
        // private positional fallback or execution-only mapper is introduced.
        let graph = self.graph.as_ref().unwrap();
        let mut arguments = supplied.unwrap_or(Err(IncompleteArgumentMapping));
        for (membership, parameter) in graph.features(&self.model.b, node, budget)? {
            if !conforms(self.model.b.elements[membership].ty, "ParameterMembership")
                || conforms(
                    self.model.b.elements[membership].ty,
                    "ReturnParameterMembership",
                )
            {
                continue;
            }
            if let Err(reason) = graph
                .valuation(&self.model.b, parameter, budget)
                .and_then(|value| value.ok_or(MissingOrMalformedValuation))
            {
                arguments = Err(reason);
                break;
            }
        }
        Ok(CallEvidence {
            function,
            arguments,
        })
    }
    fn general(&mut self, node: usize, budget: &mut Budget) -> Evidence<GeneralEvidence> {
        self.prepare(budget)?;
        let graph = self.graph.as_ref().unwrap();
        let mut all_implied = Yes;
        for rel in graph.relationships(&self.model.b, node, budget)? {
            let relation = &self.model.b.elements[rel];
            if !conforms(relation.ty, "Specialization") {
                continue;
            }
            let implied = match relation.props.get("isImplied") {
                None => No,
                Some(value) => match value.as_bool() {
                    Some(true) => Yes,
                    Some(false) => No,
                    None => Unknown(UnsupportedExpression),
                },
            };
            all_implied = and(all_implied, implied);
        }
        if all_implied == No {
            return Ok(GeneralEvidence {
                all_specializations_implied: No,
                owned_features: Ok(Vec::new()),
            });
        }
        let source = graph.features(&self.model.b, node, budget)?;
        let returns = source
            .iter()
            .filter(|(membership, _)| {
                conforms(
                    self.model.b.elements[*membership].ty,
                    "ReturnParameterMembership",
                )
            })
            .count();
        let mut features = Vec::new();
        for (membership, feature) in source {
            // directionOf uses the stored direction when this Feature is
            // reciprocally owned by the receiver, before inherited conjugation.
            let owned_input = structural_read(budget, |steps| {
                super::super::membership_evidence::parameter_direction(
                    &self.model.b,
                    &graph.structure,
                    feature,
                    steps,
                )
            });
            let owned_input = match owned_input {
                Ok(direction) => direction == Some("in"),
                Err(WorkLimit) => return Err(WorkLimit),
                Err(_) => false,
            };
            let input_or_result = if owned_input
                || (returns == 1
                    && conforms(
                        self.model.b.elements[membership].ty,
                        "ReturnParameterMembership",
                    )) {
                Yes
            } else {
                Unknown(UnsupportedDirectionOrResult)
            };
            let no_owned_features = match graph.features(&self.model.b, feature, budget) {
                Ok(features) if features.is_empty() => Yes,
                Ok(_) => No,
                Err(reason) => Unknown(reason),
            };
            let no_valuation = match graph.valuation(&self.model.b, feature, budget) {
                Ok(None) => Yes,
                Ok(Some(_)) => No,
                Err(reason) => Unknown(reason),
            };
            let result_expression = if conforms(
                self.model.b.elements[membership].ty,
                "ResultExpressionMembership",
            ) {
                if conforms(self.model.b.elements[feature].ty, "Expression") {
                    Ok(Some(feature))
                } else {
                    Err(MissingOrMalformedMembership)
                }
            } else {
                Ok(None)
            };
            features.push(OwnedFeatureEvidence {
                input_or_result,
                no_owned_features,
                no_valuation,
                result_expression,
            });
        }
        Ok(GeneralEvidence {
            all_specializations_implied: all_implied,
            owned_features: Ok(features),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::model::Model;
    fn fixture() -> ResolvedModel {
        let mut model = Model::new();
        model.add_library_source(
            "functions.kerml",
            "package DataFunctions {function '+' {in a; in b; return result;}}",
        );
        model.add_source(
            "proof.kerml",
            "feature target=1; feature read=target; feature call=DataFunctions::'+'(1,2);",
        );
        assert!(!model.has_errors());
        ResolvedModel::build(&model)
    }
    fn value(r: &mut ResolvedModel, feature: &str) -> (usize, usize, usize) {
        let owner = r.resolve_qualified(feature).unwrap().0;
        let rel = r.b.elements[owner]
            .owned_relationships
            .iter()
            .copied()
            .find(|&rel| conforms(r.b.elements[rel].ty, "FeatureValue"))
            .unwrap();
        (owner, rel, r.b.elements[rel].children[0])
    }
    #[test]
    fn owned_general_inputs_use_exact_in_direction_and_complete_valuations() {
        for (declaration, expected) in [
            ("in a;", Yes),
            ("inout a;", Unknown(UnsupportedDirectionOrResult)),
            ("out a;", Unknown(UnsupportedDirectionOrResult)),
            ("in a=1;", No),
            ("in a {feature nested;}", No),
        ] {
            let mut m = Model::new();
            let parsed = m.add_source(
                "general.kerml",
                &format!("expr e {{{declaration} return r;}}"),
            );
            assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
            let mut r = ResolvedModel::build(&m);
            let e = r.resolve_qualified("e").unwrap();
            assert_eq!(
                r.model_level_evaluability(e).classification,
                expected,
                "{declaration}"
            );
        }
        for key in ["direction", "owningType", "owningFeatureMembership"] {
            let mut m = Model::new();
            m.add_source("general.kerml", "expr e {in a; return r;}");
            let mut r = ResolvedModel::build(&m);
            let e = r.resolve_qualified("e").unwrap();
            let a = r.resolve_qualified("e::a").unwrap().0;
            let membership = r.b.elements[a].owning_relationship.unwrap();
            let row = if key == "owningType" { membership } else { a };
            r.b.elements[row].props.insert(key, serde_json::Value::Null);
            assert!(
                matches!(r.model_level_evaluability(e).classification, Unknown(_)),
                "{key}"
            );
        }
    }
    #[test]
    fn checked_arguments_can_prove_negative_without_inventing_function_eligibility() {
        let mut m = Model::new();
        m.add_library_source("library.kerml", "standard library package Base {classifier Anything; feature things:Anything;} standard library package Occurrences {class Occurrence specializes Base::Anything; feature occurrences:Occurrence subsets Base::things;} standard library package Performances {behavior Performance specializes Occurrences::Occurrence; function Evaluation specializes Performance {return result;} step performances:Performance subsets Occurrences::occurrences; expr evaluations:Evaluation subsets performances;}");
        m.add_source(
            "named.kerml",
            "function F {in a; return r;} feature call=F(a=1);",
        );
        let mut r = ResolvedModel::build(&m);
        let (_, _, call) = value(&mut r, "call");
        let call = ElementRef(call);
        let binding = r
            .invocation_binding_report(call)
            .arguments
            .unwrap()
            .bindings
            .remove(0);
        assert!(matches!(
            r.model_level_evaluability(call).classification,
            Unknown(_)
        ));
        r.b.elements[binding.value.0].ty = "CalculationUsage";
        assert_eq!(r.model_level_evaluability(call).classification, No);
    }
    #[test]
    fn instantiated_user_function_does_not_certify_expression_function() {
        for conflicting_typing in [false, true] {
            let mut model = Model::new();
            model.add_library_source(
                "functions.kerml",
                "package DataFunctions {function '+' {in a; in b; return result;}}",
            );
            model.add_source(
                "proof.kerml",
                "function User {return result;} feature call=User();",
            );
            assert!(!model.has_errors());
            let mut r = ResolvedModel::build(&model);
            let (_, _, call) = value(&mut r, "call");
            if conflicting_typing {
                let target = r.resolve_qualified("DataFunctions::'+'").unwrap().0;
                let relation =
                    r.b.new_relationship("FeatureTyping", call, "different-function");
                let source_id = r.b.elements[call].id;
                let target_id = r.b.elements[target].id;
                r.b.set(
                    relation,
                    "typedFeature",
                    super::super::super::id_ref(source_id),
                );
                r.b.set(relation, "type", super::super::super::id_ref(target_id));
            }
            assert!(matches!(
                r.model_level_evaluability(ElementRef(call)).classification,
                Unknown(_)
            ));
        }
    }

    #[test]
    fn missing_valuation_child_cannot_become_an_absent_valuation() {
        let mut r = fixture();
        let (_, _, read) = value(&mut r, "read");
        let (_, rel, _) = value(&mut r, "target");
        r.b.elements[rel].children.make_mut().clear();
        assert!(matches!(
            r.model_level_evaluability(ElementRef(read)).classification,
            Unknown(_)
        ));
    }
    #[test]
    fn contradictory_valuation_target_and_duplicate_values_are_unknown() {
        for duplicate in [false, true] {
            let mut r = fixture();
            let (_, _, read) = value(&mut r, "read");
            let (owner, rel, _) = value(&mut r, "target");
            if duplicate {
                r.b.new_relationship("FeatureValue", owner, "extra");
            } else {
                let wrong = r.b.elements[owner].id;
                r.b.set(
                    rel,
                    "ownedMemberElement",
                    super::super::super::id_ref(wrong),
                );
            }
            assert!(matches!(
                r.model_level_evaluability(ElementRef(read)).classification,
                Unknown(_)
            ));
        }
    }
    #[test]
    fn broken_argument_member_remains_visible_as_unknown() {
        let mut r = fixture();
        let (_, _, call) = value(&mut r, "call");
        let parameter = r.b.elements[call]
            .owned_relationships
            .iter()
            .copied()
            .find(|&rel| r.b.elements[rel].ty == "ParameterMembership")
            .map(|rel| r.b.elements[rel].children[0])
            .unwrap();
        let valuation = r.b.elements[parameter]
            .owned_relationships
            .iter()
            .copied()
            .find(|&rel| conforms(r.b.elements[rel].ty, "FeatureValue"))
            .unwrap();
        r.b.elements[valuation].children.make_mut().clear();
        assert!(matches!(
            r.model_level_evaluability(ElementRef(call)).classification,
            Unknown(_)
        ));
    }
    #[test]
    fn contradictory_generic_relationship_arrays_cannot_hide_behind_named_slots() {
        for key in ["source", "target", "ownedRelatedElement", "relatedElement"] {
            let mut r = fixture();
            let (_, _, read) = value(&mut r, "read");
            let (_, valuation, _) = value(&mut r, "target");
            let wrong = r.b.elements[read].id;
            r.b.elements[valuation]
                .props
                .insert(key, serde_json::json!([{"@id":wrong.to_string()}]));
            assert!(
                matches!(
                    r.model_level_evaluability(ElementRef(read)).classification,
                    Unknown(_)
                ),
                "{key}"
            );
        }
    }

    #[test]
    fn foreign_stored_carrier_cannot_prove_an_unfeatured_reference() {
        let mut r = fixture();
        let (_, _, read) = value(&mut r, "read");
        let target = r.resolve_qualified("target").unwrap().0;
        let membership = r.b.elements[target].owning_relationship.unwrap();
        let wrong = r.b.elements[read].id;
        r.b.set(
            membership,
            "owningRelatedElement",
            super::super::super::id_ref(wrong),
        );
        assert!(matches!(
            r.model_level_evaluability(ElementRef(read)).classification,
            Unknown(_)
        ));
    }
    #[test]
    fn trusted_implied_carriers_validate_present_aliases_without_authored_flag_exemptions() {
        let mut model = Model::new();
        model.add_library_source("bases.kerml",
            "standard library package Base {classifier Anything;} standard library package Occurrences {class Occurrence specializes Base::Anything;}");
        model.add_source(
            "source.kerml",
            "class A; feature target=1; feature read=target;",
        );
        let mut r = ResolvedModel::build(&model);
        let a = r.resolve_qualified("A").unwrap();
        let generated = r.implied_relationships(a)[0];
        let owner_id = r.element_id(a);
        r.b.elements[generated.0].props.insert(
            "owningRelatedElement",
            super::super::super::id_ref(owner_id),
        );
        let mut budget = Budget {
            used: 0,
            limit: crate::eval::MAX_STEPS,
        };
        let graph = StoredGraph::build(&mut r, &mut budget).unwrap();
        assert!(graph.current(&r.b));
        assert_eq!(
            graph.structure.raw_carrier(&r.b, generated.0),
            Some(Carrier::Missing)
        );
        let (_, _, read) = value(&mut r, "read");
        assert_eq!(
            r.model_level_evaluability(ElementRef(read)).classification,
            Yes
        );
        let wrong = r.b.elements[read].id;
        r.b.elements[generated.0]
            .props
            .insert("owningRelatedElement", super::super::super::id_ref(wrong));
        assert!(
            StoredGraph::build(
                &mut r,
                &mut Budget {
                    used: 0,
                    limit: crate::eval::MAX_STEPS
                }
            )
            .is_err()
        );
        r.b.elements[generated.0].props.insert(
            "owningRelatedElement",
            super::super::super::id_ref(owner_id),
        );
        let (_, valuation, _) = value(&mut r, "target");
        r.b.elements[valuation]
            .props
            .insert("isImplied", serde_json::json!(true));
        r.b.elements[valuation]
            .props
            .insert("owningRelatedElement", super::super::super::id_ref(wrong));
        assert!(matches!(
            r.model_level_evaluability(ElementRef(read)).classification,
            Unknown(_)
        ));
    }
    #[test]
    fn relation_readers_obey_the_report_remaining_budget_and_retry_fresh() {
        let mut r = fixture();
        let feature = r.resolve_qualified("target").unwrap().0;
        let mut relations = TypeRelations::default();
        let mut empty = Budget { used: 0, limit: 0 };
        assert_eq!(
            structural_read(&mut empty, |steps| relations
                .owning_type(&mut r.b, feature, steps)),
            Err(WorkLimit)
        );
        let mut fresh = Budget {
            used: 0,
            limit: crate::eval::MAX_STEPS,
        };
        assert_eq!(
            structural_read(&mut fresh, |steps| relations
                .owning_type(&mut r.b, feature, steps)),
            Ok(None)
        );
        let mut empty_again = Budget { used: 0, limit: 0 };
        assert_eq!(
            structural_read(&mut empty_again, |steps| Some(
                relations.specializes(&mut r.b, feature, feature, steps)
            )),
            Err(WorkLimit)
        );
        let mut fresh_again = Budget {
            used: 0,
            limit: crate::eval::MAX_STEPS,
        };
        assert_eq!(
            structural_read(&mut fresh_again, |steps| Some(
                relations.specializes(&mut r.b, feature, feature, steps)
            )),
            Ok(RelationFact::Yes)
        );
    }
    #[test]
    fn reports_share_raw_identity_and_carrier_index_without_duplicate_allocations() {
        let mut r = fixture();
        let mut budget = Budget {
            used: 0,
            limit: crate::eval::MAX_STEPS,
        };
        let first = StoredGraph::build(&mut r, &mut budget).unwrap();
        let second = StoredGraph::build(
            &mut r,
            &mut Budget {
                used: 0,
                limit: crate::eval::MAX_STEPS,
            },
        )
        .unwrap();
        assert!(Arc::ptr_eq(&first.ids, &second.ids));
        assert!(Arc::ptr_eq(&first.structure, &second.structure));
        assert!(Arc::ptr_eq(&first.ids, r.b.id_index.as_ref().unwrap()));
        assert!(first.current(&r.b));
    }
    #[test]
    fn same_length_row_mutation_refuses_the_old_proof_and_fresh_query_retries() {
        let mut r = fixture();
        let (_, valuation, _) = value(&mut r, "target");
        let owner = r.resolve_qualified("target").unwrap().0;
        let mut proof = RepositoryEvidence::new(&mut r);
        proof
            .prepare(&mut Budget {
                used: 0,
                limit: crate::eval::MAX_STEPS,
            })
            .unwrap();
        let original = proof.model.b.elements[valuation].props.clone();
        proof.model.b.elements[valuation]
            .props
            .insert("isImplied", serde_json::json!(false));
        assert_eq!(
            proof.prepare(&mut Budget {
                used: 0,
                limit: crate::eval::MAX_STEPS
            }),
            Err(MissingOrMalformedMembership)
        );
        assert_eq!(
            proof.graph.as_ref().unwrap().relationships(
                &proof.model.b,
                owner,
                &mut Budget {
                    used: 0,
                    limit: crate::eval::MAX_STEPS
                }
            ),
            Err(MissingOrMalformedMembership)
        );
        proof.model.b.elements[valuation].props = original;
        assert_eq!(
            proof.prepare(&mut Budget {
                used: 0,
                limit: crate::eval::MAX_STEPS
            }),
            Err(MissingOrMalformedMembership)
        );
        drop(proof);
        let mut fresh = RepositoryEvidence::new(&mut r);
        assert!(
            fresh
                .prepare(&mut Budget {
                    used: 0,
                    limit: crate::eval::MAX_STEPS
                })
                .is_ok()
        );
    }
    #[test]
    fn shared_graph_respects_cold_warm_small_budget_and_fresh_retry() {
        let mut r = fixture();
        r.b.stored_structure = None;
        r.b.id_index = None;
        assert!(matches!(
            StoredGraph::build(&mut r, &mut Budget { used: 0, limit: 0 }),
            Err(WorkLimit)
        ));
        assert!(r.b.stored_structure.is_none());
        let good = StoredGraph::build(
            &mut r,
            &mut Budget {
                used: 0,
                limit: crate::eval::MAX_STEPS,
            },
        )
        .unwrap();
        assert!(matches!(
            StoredGraph::build(&mut r, &mut Budget { used: 0, limit: 1 }),
            Err(WorkLimit)
        ));
        let retry = StoredGraph::build(
            &mut r,
            &mut Budget {
                used: 0,
                limit: crate::eval::MAX_STEPS,
            },
        )
        .unwrap();
        assert!(Arc::ptr_eq(&good.structure, &retry.structure));
    }
    #[test]
    fn mid_report_generic_materialization_requires_fresh_query() {
        let mut model = Model::new();
        model.add_library_source("bases.kerml","standard library package Base {classifier Anything;} standard library package Occurrences {class Occurrence specializes Base::Anything;}");
        model.add_source(
            "query.kerml",
            "class A; feature target=1; feature read=target;",
        );
        let mut r = ResolvedModel::build(&model);
        let a = r.resolve_qualified("A").unwrap();
        let mut proof = RepositoryEvidence::new(&mut r);
        proof
            .prepare(&mut Budget {
                used: 0,
                limit: crate::eval::MAX_STEPS,
            })
            .unwrap();
        assert!(!proof.model.implied_relationships(a).is_empty());
        assert_eq!(
            proof.prepare(&mut Budget {
                used: 0,
                limit: crate::eval::MAX_STEPS
            }),
            Err(MissingOrMalformedMembership)
        );
        drop(proof);
        assert!(
            StoredGraph::build(
                &mut r,
                &mut Budget {
                    used: 0,
                    limit: crate::eval::MAX_STEPS
                }
            )
            .is_ok()
        );
    }

    #[test]
    fn generated_result_carriers_and_members_share_the_semantic_view() {
        let mut r = fixture();
        let (_, _, expression) = value(&mut r, "read");
        r.ensure_implied();
        let result =
            r.b.semantic_ownership
                .as_ref()
                .unwrap()
                .result(expression)
                .unwrap();
        let mut budget = Budget {
            used: 0,
            limit: crate::eval::MAX_STEPS,
        };
        let graph = StoredGraph::build(&mut r, &mut budget).unwrap();
        let rows = graph.relationships(&r.b, expression, &mut budget).unwrap();
        assert_eq!(
            rows.iter().filter(|&&row| row == result.membership).count(),
            1
        );
        let bindings: Vec<_> = rows
            .iter()
            .copied()
            .filter(|&row| r.b.elements[row].ty == "OwningMembership")
            .collect();
        assert_eq!(bindings.len(), 1);
        let binding = graph
            .member(&r.b, expression, bindings[0], &mut budget)
            .unwrap();
        assert_eq!(r.b.elements[binding].ty, "BindingConnector");
        assert_eq!(
            graph.member(&r.b, expression, result.membership, &mut budget),
            Ok(result.feature)
        );
        assert_eq!(
            graph.features(&r.b, expression, &mut budget),
            Err(UnsupportedExpression),
            "local result/binding does not certify complete connector ancestry or featuring"
        );
        assert!(
            graph
                .features(&r.b, result.feature, &mut budget)
                .unwrap()
                .is_empty()
        );
        r.b.elements[result.membership].owning_relationship = Some(result.membership);
        assert!(
            StoredGraph::build(&mut r, &mut budget).is_err(),
            "a generated relationship cannot acquire contradictory child ownership"
        );
    }

    #[test]
    fn small_adapter_budget_does_not_poison_a_fresh_query() {
        let mut r = fixture();
        r.ensure_implied();
        let mut exhausted = Budget { used: 0, limit: 1 };
        assert!(matches!(
            StoredGraph::build(&mut r, &mut exhausted),
            Err(WorkLimit)
        ));
        assert!(exhausted.used > exhausted.limit);
        let mut fresh = Budget {
            used: 0,
            limit: crate::eval::MAX_STEPS,
        };
        assert!(StoredGraph::build(&mut r, &mut fresh).is_ok());
        let mut warm_tiny = Budget { used: 0, limit: 1 };
        assert!(matches!(
            StoredGraph::build(&mut r, &mut warm_tiny),
            Err(WorkLimit)
        ));
    }

    #[test]
    fn authored_carrier_failure_is_not_repaired_by_the_generated_view() {
        let mut r = fixture();
        let (_, _, expression) = value(&mut r, "read");
        r.ensure_implied();
        let authored = r.b.elements[expression].owned_relationships[0];
        let wrong = r.b.elements[expression].id;
        // It is already carried by the expression. A contradictory generic
        // source alias is checked by member(), never overwritten by projection.
        let member =
            r.b.semantic_ownership
                .as_ref()
                .unwrap()
                .result(expression)
                .unwrap()
                .feature;
        let wrong_owner = r.b.elements[member].id;
        r.b.elements[authored].props.insert(
            "owningRelatedElement",
            serde_json::json!({"@id":wrong_owner.to_string()}),
        );
        r.b.elements[authored]
            .props
            .insert("isImplied", serde_json::json!(true));
        assert!(
            StoredGraph::build(
                &mut r,
                &mut Budget {
                    used: 0,
                    limit: crate::eval::MAX_STEPS
                }
            )
            .is_err()
        );
        r.b.elements[authored].props.insert(
            "owningRelatedElement",
            serde_json::json!({"@id":wrong.to_string()}),
        );
        assert!(
            StoredGraph::build(
                &mut r,
                &mut Budget {
                    used: 0,
                    limit: crate::eval::MAX_STEPS
                }
            )
            .is_ok()
        );
    }

    #[test]
    fn replacing_a_result_tail_invalidates_query_local_carrier_evidence() {
        let mut r = fixture();
        let (_, _, expression) = value(&mut r, "read");
        r.ensure_implied();
        let mut budget = Budget {
            used: 0,
            limit: crate::eval::MAX_STEPS,
        };
        let old = StoredGraph::build(&mut r, &mut budget).unwrap();
        r.discard_owned_result_tail();
        r.ensure_implied();
        assert!(!old.current(&r.b));
        assert_eq!(
            old.relationships(&r.b, expression, &mut budget),
            Err(MissingOrMalformedMembership)
        );
        let fresh = StoredGraph::build(&mut r, &mut budget).unwrap();
        let result =
            r.b.semantic_ownership
                .as_ref()
                .unwrap()
                .result(expression)
                .unwrap();
        assert_eq!(
            fresh.member(&r.b, expression, result.membership, &mut budget),
            Ok(result.feature)
        );
    }

    #[test]
    fn repository_evidence_refuses_mid_report_publication_instead_of_reusing_proofs() {
        let mut r = fixture();
        let mut provider = RepositoryEvidence::new(&mut r);
        let mut budget = Budget {
            used: 0,
            limit: crate::eval::MAX_STEPS,
        };
        provider.prepare(&mut budget).unwrap();
        provider.model.ensure_implied();
        assert_eq!(
            provider.prepare(&mut budget),
            Err(MissingOrMalformedMembership)
        );
        // A new report gets a new graph and all new relation memos.
        let mut fresh = RepositoryEvidence::new(provider.model);
        fresh
            .prepare(&mut Budget {
                used: 0,
                limit: crate::eval::MAX_STEPS,
            })
            .unwrap();
    }
    #[test]
    fn generic_prefix_cannot_acquire_owned_children_or_nested_rows() {
        for child_array in [true, false] {
            let mut model = Model::new();
            model.add_library_source("generic.kerml", "standard library package Base {classifier Anything;} standard library package Occurrences {class Occurrence specializes Base::Anything;}");
            model.add_source(
                "source.kerml",
                "class A; class B specializes A; feature target=1; feature read=target;",
            );
            let mut r = ResolvedModel::build(&model);
            let a = r.resolve_qualified("A").unwrap();
            let generated = r.implied_relationships(a)[0];
            if child_array {
                r.b.elements[generated.0].children.push(a.0);
            } else {
                // Relocate an authored relationship consistently: the raw
                // carrier remains unique and agrees with its scalar alias.
                // Only the generic parent's childless-shape proof rejects it.
                let b = r.resolve_qualified("B").unwrap().0;
                let nested = r.b.elements[b]
                    .owned_relationships
                    .iter()
                    .copied()
                    .find(|&rel| conforms(r.b.elements[rel].ty, "Subclassification"))
                    .unwrap();
                r.b.elements[b]
                    .owned_relationships
                    .make_mut()
                    .retain(|&rel| rel != nested);
                r.b.elements[generated.0].owned_relationships.push(nested);
                let owner_id = r.b.elements[generated.0].id;
                r.b.elements[nested].props.insert(
                    "owningRelatedElement",
                    serde_json::json!({"@id": owner_id.to_string()}),
                );
                let mut steps = 0;
                let raw = StoredStructure::for_query(&mut r.b, &mut steps).unwrap();
                assert_eq!(raw.carrier(&r.b, nested), Some(Some(generated.0)));
                assert_eq!(
                    semantic_ownership::checked_relationship_carrier(
                        &r.b, &raw, nested, &mut steps
                    ),
                    Some(Some(generated.0))
                );
            }
            assert!(matches!(
                StoredGraph::build(
                    &mut r,
                    &mut Budget {
                        used: 0,
                        limit: crate::eval::MAX_STEPS
                    }
                ),
                Err(MissingOrMalformedMembership)
            ));
        }
    }
}
