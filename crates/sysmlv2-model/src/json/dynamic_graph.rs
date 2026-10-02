//! One accepted dynamic family, published with the independently admitted result tail.
use super::{
    Builder, Elem,
    dynamic_invocations::{self, Refusal},
    publication,
    semantic_batch::Plan,
    semantic_ownership::SemanticOwnership,
};
use crate::properties::Properties;
use std::{
    collections::{HashMap, HashSet},
    sync::{Arc, OnceLock},
};
use uuid::Uuid;

#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) enum Outcome {
    NotApplicable,
    Declined(Refusal),
    Accepted,
}
#[derive(Clone)]
pub(super) struct Snapshot {
    pub epoch: publication::Revision,
    pub plan: Option<Arc<Plan>>,
    pub outcome: Outcome,
    metadata: Option<Arc<()>>,
    rows: crate::layered::Revision,
    names: crate::layered::Revision,
    pub typing: OnceLock<Arc<super::implied::RetainedTypings>>,
    pub local_featuring: Option<Arc<HashSet<usize>>>,
    pub local_featuring_outcome: Outcome,
    pub result_redefinition: Option<Arc<super::result_redefinition::Evidence>>,
    pub result_redefinition_outcome: Outcome,
}
impl Snapshot {
    pub(super) fn new(
        b: &mut Builder,
        epoch: publication::Revision,
        rows: crate::layered::Revision,
        plan: Result<Option<Plan>, Refusal>,
    ) -> Self {
        let (plan, outcome) = match plan {
            Ok(Some(plan)) => (Some(Arc::new(plan)), Outcome::Accepted),
            Ok(None) => (None, Outcome::NotApplicable),
            Err(reason) => (None, Outcome::Declined(reason)),
        };
        Self {
            epoch,
            rows,
            names: b.lib_qnames.observe_revision(),
            plan,
            outcome,
            metadata: b.metadata_association_generation.clone(),
            typing: OnceLock::new(),
            local_featuring: None,
            local_featuring_outcome: Outcome::NotApplicable,
            result_redefinition: None,
            result_redefinition_outcome: Outcome::NotApplicable,
        }
    }
    pub(super) fn with_local(mut self, result: Result<HashSet<usize>, Refusal>) -> Self {
        match result {
            Ok(owners) if !owners.is_empty() => {
                self.local_featuring = Some(Arc::new(owners));
                self.local_featuring_outcome = Outcome::Accepted;
            }
            Ok(_) => {}
            Err(reason) => self.local_featuring_outcome = Outcome::Declined(reason),
        }
        self
    }
    pub(super) fn with_result_redefinition(
        mut self,
        result: Result<super::result_redefinition::Evidence, Refusal>,
    ) -> Self {
        match result {
            Ok(evidence) if !evidence.sources.is_empty() => {
                self.result_redefinition = Some(Arc::new(evidence));
                self.result_redefinition_outcome = Outcome::Accepted;
            }
            Ok(_) => {}
            Err(reason) => self.result_redefinition_outcome = Outcome::Declined(reason),
        }
        self
    }
    pub(super) fn result_redefinition_current(&self, b: &Builder) -> bool {
        self.result_redefinition_outcome == Outcome::Accepted && self.current(b)
    }
    /// These edges depend only on certified generated ownership and row defaults,
    /// not on dynamic callee admission or metadata associations.
    pub(super) fn local_current(&self, b: &Builder) -> bool {
        self.local_featuring_outcome == Outcome::Accepted && self.rows_current(b)
    }
    fn rows_current(&self, b: &Builder) -> bool {
        self.epoch.same_as(&b.publication.revision())
            && b.elements
                .revision()
                .is_some_and(|now| now.same_as(&self.rows))
    }
    pub(super) fn current(&self, b: &Builder) -> bool {
        b.lib_qnames
            .revision()
            .is_some_and(|now| now.same_as(&self.names))
            && b.elements
                .revision()
                .is_some_and(|now| now.same_as(&self.rows))
            && self.epoch.same_as(&b.publication.revision())
            && match (&self.metadata, &b.metadata_association_generation) {
                (None, None) => true,
                (Some(a), Some(z)) => Arc::ptr_eq(a, z),
                _ => false,
            }
    }
}
impl Builder {
    /// Observation only. Construction routines retain their explicit static inputs.
    pub(super) fn effective_dynamic_plan(&self) -> Option<&Plan> {
        if self.static_planning {
            return None;
        }
        let snapshot = self.dynamic_graph.as_ref()?;
        (snapshot.current(self) && snapshot.outcome == Outcome::Accepted)
            .then_some(snapshot.plan.as_deref())
            .flatten()
    }

    /// Stale generated rows remain addressable for identity compatibility, but
    /// cannot supply new checked semantic evidence for an affected owner.
    pub(super) fn dynamic_evidence_current(&self, owner: usize) -> bool {
        if self.static_planning {
            return true;
        }
        let Some(snapshot) = &self.dynamic_graph else {
            return true;
        };
        let affected = snapshot
            .plan
            .as_ref()
            .is_some_and(|plan| plan.affected_owners.contains(&owner));
        !affected || (snapshot.current(self) && snapshot.outcome == Outcome::Accepted)
    }

    pub(super) fn local_featuring_evidence_current(&self, owner: usize) -> bool {
        let Some(snapshot) = &self.dynamic_graph else {
            return true;
        };
        !snapshot
            .local_featuring
            .as_ref()
            .is_some_and(|owners| owners.contains(&owner))
            || snapshot.local_current(self)
    }

    pub(super) fn result_redefinition_evidence_current(&self, source: usize) -> bool {
        self.dynamic_graph.as_ref().is_none_or(|snapshot| {
            !snapshot
                .result_redefinition
                .as_ref()
                .is_some_and(|e| e.sources.contains(&source))
                || snapshot.result_redefinition_current(self)
        })
    }
    pub(super) fn result_redefinition_row_current(&self, row: usize) -> bool {
        self.dynamic_graph.as_ref().is_none_or(|snapshot| {
            !snapshot
                .result_redefinition
                .as_ref()
                .is_some_and(|e| e.relationships.contains(&row))
                || snapshot.result_redefinition_current(self)
        })
    }
    pub(super) fn effective_positional_redefinitions(
        &self,
    ) -> Option<&super::positional::PositionalRedefinitions> {
        self.effective_dynamic_plan()
            .map(|p| &p.positional)
            .or_else(|| {
                self.positional_redefinitions
                    .as_ref()
                    .filter(|_| self.supported_chain_evidence_current())
            })
    }
    pub(super) fn dynamic_typing_edges(
        &self,
        steps: &mut usize,
    ) -> Option<Arc<super::implied::RetainedTypings>> {
        let plan = self.effective_dynamic_plan()?;
        let snapshot = self.dynamic_graph.as_ref()?;
        *steps = steps.saturating_add(1);
        if *steps > crate::eval::MAX_STEPS {
            return None;
        }
        if let Some(value) = snapshot.typing.get() {
            return Some(Arc::clone(value));
        }
        *steps = steps
            .saturating_add(plan.static_prefix.rows.len())
            .saturating_add(plan.tail.len());
        if *steps > crate::eval::MAX_STEPS {
            return None;
        }
        let mut values = super::implied::RetainedTypings::new();
        for edge in plan.static_prefix.rows.iter().chain(&plan.tail) {
            if crate::metaclass::conforms(edge.kind, "FeatureTyping")
                || crate::metaclass::conforms(edge.kind, "Subsetting")
            {
                values
                    .entry(edge.owner)
                    .or_default()
                    .push((edge.kind, edge.target));
            }
        }
        let _ = snapshot.typing.set(Arc::new(values));
        snapshot.typing.get().cloned()
    }
    pub(super) fn prepare_dynamic_graph(
        &mut self,
        reserved: &HashSet<Uuid>,
        steps: &mut usize,
        produced_prefix: Option<Arc<super::semantic_batch::StaticPrefix>>,
    ) -> Result<Option<Plan>, Refusal> {
        *steps = steps.saturating_add(self.explicit_len());
        if *steps > crate::eval::MAX_STEPS {
            return Err(Refusal::WorkLimit);
        }
        if !self.elements.iter().take(self.explicit_len()).any(|e| {
            e.ty == "InvocationExpression"
                || (self.graph_format == crate::model::GraphFormat::CanonicalV3
                    && matches!(e.ty, "ConstructorExpression" | "OperatorExpression"))
        }) {
            return Ok(None);
        }
        for (_, parts) in &self.lib_qnames {
            *steps = steps.saturating_add(1);
            for part in parts {
                *steps = steps.saturating_add(part.len());
            }
            if *steps > crate::eval::MAX_STEPS {
                return Err(Refusal::WorkLimit);
            }
        }
        for name in self.external_implied_names.keys() {
            *steps = steps.saturating_add(name.len().saturating_add(1));
            if *steps > crate::eval::MAX_STEPS {
                return Err(Refusal::WorkLimit);
            }
        }
        let names: HashMap<_, _> = self
            .lib_qnames
            .iter()
            .map(|(id, parts)| (parts.join("::"), *id))
            .chain(
                self.external_implied_names
                    .iter()
                    .map(|(name, id)| (name.clone(), *id)),
            )
            .collect();
        let metadata = self.metadata_association_generation.clone();
        let mut positional_workspace = super::positional::PositionalWorkspace::default();
        let prefix = if let Some(prefix) = produced_prefix {
            // This is a same-transaction producer value, never a reconstructed
            // cache. Capture below still checks every physical recipe/identity.
            if !self.physical_static_authority_current() {
                return Err(Refusal::Stale);
            }
            prefix
        } else {
            self.static_specialization_prefix_with_workspace(
                &names,
                self.external_implied_names.is_empty(),
                Some(steps),
                &mut positional_workspace,
            )
            .ok_or(Refusal::WorkLimit)?
        };
        let boundary = self.implied.as_ref().map(|t| t.owned_results_from);
        let prefix = dynamic_invocations::capture_static_prefix(self, prefix, boundary, steps)?;
        let plan = dynamic_invocations::prepare_with_workspace(
            self,
            prefix,
            reserved,
            boundary,
            steps,
            &mut positional_workspace,
        )?;
        let current = match (&metadata, &self.metadata_association_generation) {
            (None, None) => true,
            (Some(a), Some(z)) => Arc::ptr_eq(a, z),
            _ => false,
        };
        if !current {
            return Err(Refusal::Stale);
        }
        Ok(Some(plan))
    }
}

/// Pure row construction. All indices and carriers are validated before the
/// private view is changed. The caller discards this private staging on failure.
pub(super) fn stage_dynamic_rows(
    b: &Builder,
    plan: &Plan,
    start: usize,
    ownership: &mut SemanticOwnership,
    steps: &mut usize,
) -> Result<Vec<Elem>, Refusal> {
    let mut rows = Vec::new();
    for edge in &plan.tail {
        *steps = steps.saturating_add(16);
        if *steps > crate::eval::MAX_STEPS {
            return Err(Refusal::WorkLimit);
        }
        if edge.owner >= b.explicit_len() || b.elements[edge.owner].id != edge.owner_id {
            return Err(Refusal::Stale);
        }
        let mut props = Properties::new();
        props.insert("isImplied", serde_json::json!(true));
        props.insert(
            "owningRelatedElement",
            serde_json::json!({"@id":edge.owner_id.to_string()}),
        );
        props.insert(
            edge.source_key,
            serde_json::json!({"@id":edge.owner_id.to_string()}),
        );
        props.insert(
            edge.target_key,
            serde_json::json!({"@id":edge.target.to_string()}),
        );
        ownership
            .register(start + rows.len(), Some(edge.owner), edge.owner, true)
            .ok_or(Refusal::Stale)?;
        rows.push(Elem {
            ty: edge.kind,
            id: edge.id,
            path: String::new(),
            path_parent: None,
            props,
            owned_relationships: Default::default(),
            children: Default::default(),
            owning_relationship: None,
        });
    }
    Ok(rows)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        json::{ElementRef, ResolvedModel},
        model::Model,
    };
    fn fixture(source: &str) -> ResolvedModel {
        let mut model = Model::new();
        model.add_source("dynamic-graph.kerml", source);
        assert!(!model.has_errors());
        ResolvedModel::build(&model)
    }
    #[test]
    fn one_snapshot_exposes_dynamic_callee_and_positional_edges() {
        let mut r = fixture("function F {in p; return result;} feature call=F(1);");
        let f = r.resolve_qualified("F").unwrap();
        let p = r.resolve_qualified("F::p").unwrap();
        let call = r
            .user_elements()
            .find(|&e| r.element_type(e) == "InvocationExpression")
            .unwrap();
        assert!(r.b.dynamic_graph.is_none());
        r.implied_relationships(call);
        let snapshot = r.b.dynamic_graph.clone().unwrap();
        assert_eq!(snapshot.outcome, Outcome::Accepted);
        assert!(snapshot.epoch.same_as(&r.b.publication.revision()));
        let plan = snapshot.plan.as_ref().unwrap();
        assert!(
            r.b.value_context_bases(call.0, &mut 0)
                .unwrap()
                .contains(&f.0)
        );
        assert!(
            plan.tail
                .iter()
                .any(|e| e.owner == call.0 && e.target == r.element_id(f))
        );
        let parameter = plan
            .tail
            .iter()
            .find(|e| e.kind == "Redefinition" && e.target == r.element_id(p))
            .unwrap()
            .owner;
        assert!(
            r.b.cardinality_positional_targets(parameter, &mut 0)
                .unwrap()
                .contains(&p.0)
        );
        let count = r.b.elements.len();
        r.implied_relationships(call);
        assert_eq!(r.b.elements.len(), count);
        assert!(Arc::ptr_eq(&snapshot, r.b.dynamic_graph.as_ref().unwrap()));
        assert!(matches!(
            r.model_level_evaluability(call).classification,
            crate::json::ModelLevelEvaluability::Unknown(_)
        ));
    }
    #[test]
    fn dynamic_decline_preserves_independent_result_and_binding_rows() {
        let mut r = fixture("feature n; feature read=n; feature bad=Missing();");
        let reference = r
            .user_elements()
            .find(|&e| r.element_type(e) == "FeatureReferenceExpression")
            .unwrap();
        r.implied_relationships(reference);
        let snapshot = r.b.dynamic_graph.as_ref().unwrap();
        assert!(matches!(snapshot.outcome, Outcome::Declined(_)));
        assert!(snapshot.plan.is_none());
        let view = r.b.semantic_ownership.as_ref().unwrap();
        assert!(view.result(reference.0).is_some());
        assert_eq!(
            r.b.elements
                .iter()
                .filter(|e| e.ty == "BindingConnector")
                .count(),
            1
        );
        assert_eq!(
            r.b.elements.len() - r.b.implied.as_ref().unwrap().owned_results_from,
            14
        );
    }
    #[test]
    fn explicit_dynamic_and_result_ids_keep_handles_and_logical_endpoints() {
        let mut r = fixture(
            "function F {in p; return result;} feature n; feature read=n; feature call=F(1);",
        );
        let call = r
            .user_elements()
            .find(|&e| r.element_type(e) == "InvocationExpression")
            .unwrap();
        let reference = r
            .user_elements()
            .find(|&e| r.element_type(e) == "FeatureReferenceExpression")
            .unwrap();
        let f = r.resolve_qualified("F").unwrap();
        r.implied_relationships(call);
        let snapshot = r.b.dynamic_graph.clone().unwrap();
        assert_eq!(snapshot.outcome, Outcome::Accepted);
        let dynamic_id = snapshot.plan.as_ref().unwrap().tail[0].id;
        let dynamic_handle = r.element_by_id(&dynamic_id.to_string()).unwrap();
        let result =
            r.b.semantic_ownership
                .as_ref()
                .unwrap()
                .result(reference.0)
                .unwrap()
                .feature;
        let result_id = r.b.elements[result].id;
        let old_f = r.element_id(f);
        let new_dynamic = Uuid::new_v5(&Uuid::NAMESPACE_OID, b"explicit dynamic relationship");
        let new_result = Uuid::new_v5(&Uuid::NAMESPACE_OID, b"explicit generated result");
        let new_f = Uuid::new_v5(&Uuid::NAMESPACE_OID, b"explicit callee");
        let before = r.b.elements.len();
        assert_eq!(
            r.override_ids(&HashMap::from([
                (dynamic_id, new_dynamic),
                (result_id, new_result),
                (old_f, new_f)
            ]))
            .len(),
            3
        );
        assert_eq!(r.b.elements.len(), before);
        assert_eq!(r.element_id(dynamic_handle), new_dynamic);
        assert_eq!(r.b.elements[result].id, new_result);
        let current = r.b.dynamic_graph.as_ref().unwrap();
        assert!(!Arc::ptr_eq(&snapshot, current));
        assert!(current.epoch.same_as(&r.b.publication.revision()));
        assert!(
            current
                .plan
                .as_ref()
                .unwrap()
                .tail
                .iter()
                .any(|e| e.id == new_dynamic)
        );
        assert!(
            current
                .plan
                .as_ref()
                .unwrap()
                .tail
                .iter()
                .any(|e| e.target == new_f)
        );
        r.implied_relationships(call);
        assert_eq!(r.b.elements.len(), before);
        assert_eq!(r.element_id(dynamic_handle), new_dynamic);
    }

    #[test]
    fn proof_held_before_publication_refuses_after_epoch_change() {
        let mut r = fixture("feature a; function F {return result;} feature call=F();");
        let a = r.resolve_qualified("a").unwrap();
        let mut proof = super::super::type_relations::TypeRelations::default();
        assert_eq!(proof.owning_type(&mut r.b, a.0, &mut 0), Some(None));
        let call =
            r.b.elements
                .iter()
                .position(|e| e.ty == "InvocationExpression")
                .unwrap();
        r.implied_relationships(ElementRef(call));
        assert_eq!(proof.owning_type(&mut r.b, a.0, &mut 0), None);
        assert_eq!(
            super::super::type_relations::TypeRelations::default()
                .owning_type(&mut r.b, a.0, &mut 0),
            Some(None)
        );
    }
}

impl Builder {
    /// Name tables affect held proofs, but an existing physical implied graph
    /// intentionally retains the Builder names from its first materialization.
    pub(super) fn library_names_changed(&mut self, preserve: bool, was_current: bool) {
        let epoch = publication::Revision::next();
        if preserve {
            if let Some(previous) = self.dynamic_graph.as_ref() {
                let mut next = previous.as_ref().clone();
                next.epoch = epoch.clone();
                if !was_current && next.plan.is_some() {
                    next.outcome = Outcome::Declined(Refusal::Stale);
                }
                self.dynamic_graph = Some(Arc::new(next));
            }
        } else {
            self.dynamic_graph = None;
        }
        self.publication.install(epoch);
    }
    /// ID overrides preserve physical rows/handles. Only immutable recipes are
    /// replaced; explicit generated IDs are never re-derived from their owner.
    pub(super) fn remap_dynamic_graph(
        &mut self,
        ids: &HashMap<Uuid, Uuid>,
        admissible: bool,
        local_admissible: bool,
        result_admissible: bool,
    ) {
        let Some(previous) = self.dynamic_graph.clone() else {
            self.publication.published();
            return;
        };
        fn graph(
            values: &HashMap<Uuid, Vec<Uuid>>,
            ids: &HashMap<Uuid, Uuid>,
        ) -> HashMap<Uuid, Vec<Uuid>> {
            values
                .iter()
                .map(|(s, t)| {
                    (
                        *ids.get(s).unwrap_or(s),
                        t.iter().map(|id| *ids.get(id).unwrap_or(id)).collect(),
                    )
                })
                .collect()
        }
        fn edge(edge: &mut super::semantic_batch::Edge, ids: &HashMap<Uuid, Uuid>) {
            edge.id = *ids.get(&edge.id).unwrap_or(&edge.id);
            edge.owner_id = *ids.get(&edge.owner_id).unwrap_or(&edge.owner_id);
            edge.target = *ids.get(&edge.target).unwrap_or(&edge.target);
        }
        let unique = self.literal_identities_unique(None) == Some(true);
        let plan = if let Some(old) = &previous.plan {
            let mut plan = old.as_ref().clone();
            let mut prefix = plan.static_prefix.as_ref().clone();
            for item in &mut prefix.rows {
                edge(item, ids);
            }
            prefix.specializations = graph(&prefix.specializations, ids);
            plan.static_prefix = Arc::new(prefix);
            for item in &mut plan.tail {
                edge(item, ids);
            }
            plan.specializations = graph(&plan.specializations, ids);
            Ok(Some(plan))
        } else {
            match &previous.outcome {
                Outcome::Declined(reason) => Err(reason.clone()),
                _ => Ok(None),
            }
        };
        let epoch = publication::Revision::next();
        let rows = self.elements.observe_revision();
        let mut snapshot = Snapshot::new(self, epoch.clone(), rows, plan);
        snapshot.local_featuring = previous.local_featuring.clone();
        snapshot.local_featuring_outcome = previous.local_featuring_outcome.clone();
        if snapshot.local_featuring.is_some() && (!local_admissible || !unique) {
            snapshot.local_featuring_outcome = Outcome::Declined(if unique {
                Refusal::Stale
            } else {
                Refusal::Collision
            });
        }
        snapshot.result_redefinition = previous.result_redefinition.clone();
        snapshot.result_redefinition_outcome = previous.result_redefinition_outcome.clone();
        if snapshot.result_redefinition.is_some() && (!result_admissible || !unique) {
            snapshot.result_redefinition_outcome = Outcome::Declined(if unique {
                Refusal::Stale
            } else {
                Refusal::Collision
            });
        }
        if !admissible || !unique {
            snapshot.outcome = Outcome::Declined(if unique {
                Refusal::Stale
            } else {
                Refusal::Collision
            });
        }
        self.dynamic_graph = Some(Arc::new(snapshot));
        self.publication.install(epoch);
    }
}

pub(super) fn stage_dynamic_adjacency(
    plan: &Plan,
    steps: &mut usize,
) -> Result<HashMap<Uuid, Vec<Uuid>>, Refusal> {
    *steps = steps.saturating_add(plan.specializations.capacity());
    if *steps > crate::eval::MAX_STEPS {
        return Err(Refusal::WorkLimit);
    }
    for targets in plan.specializations.values() {
        *steps = steps.saturating_add(targets.len());
        if *steps > crate::eval::MAX_STEPS {
            return Err(Refusal::WorkLimit);
        }
    }
    Ok(plan.specializations.clone())
}

#[cfg(test)]
mod replay_tests {
    use super::*;
    use crate::{
        json::{ClosurePolicy, ElementRef, ResolvedModel},
        libcache::LibraryCache,
        model::Model,
        prepared::PreparedLibrary,
    };
    const LIB: &str = "standard library package Base {classifier Anything; feature things:Anything;} standard library package Occurrences {class Occurrence specializes Base::Anything; feature occurrences:Occurrence subsets Base::things;} standard library package Performances {behavior Performance specializes Occurrences::Occurrence; function Evaluation specializes Performance; step performances:Performance subsets Occurrences::occurrences; expr evaluations:Evaluation subsets performances;}";
    const USER: &str =
        "function F {in p; return result;} feature n; feature read=n; feature call=F(1);";
    #[test]
    fn shared_dynamic_snapshot_replays_and_does_not_publish_during_preparation() {
        let mut base = Model::new();
        base.add_library_source("bases.kerml", LIB);
        base.record_library_cache();
        ResolvedModel::build(&base);
        let cache =
            LibraryCache::from_bytes(&base.take_recorded_library_cache().unwrap().to_bytes())
                .unwrap();
        let prepared = base.prepare_library().unwrap();
        let decoded =
            Arc::new(PreparedLibrary::from_bytes(&prepared.to_bytes(82).unwrap(), 82).unwrap());
        let mut expected = None;
        for mode in 0..4 {
            let mut model = Model::new();
            match mode {
                2 => Arc::clone(&prepared).install(&mut model).unwrap(),
                3 => Arc::clone(&decoded).install(&mut model).unwrap(),
                _ => {
                    model.add_library_source("bases.kerml", LIB);
                    if mode == 1 {
                        model.set_library_cache(cache.clone());
                    }
                }
            }
            model.add_source("dynamic.kerml", USER);
            assert!(!model.has_errors());
            let compact = crate::json::model_to_compact_json(&model);
            let mut r = ResolvedModel::build(&model);
            assert!(r.b.dynamic_graph.is_none());
            assert!(r.b.implied.is_none());
            let source_ids: Vec<_> = r.user_elements().map(|e| r.element_id(e)).collect();
            let call = r
                .user_elements()
                .find(|&e| r.element_type(e) == "InvocationExpression")
                .unwrap();
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
                r.implied_relationships(call);
                assert_eq!(
                    r.b.dynamic_graph.as_ref().unwrap().outcome,
                    Outcome::Accepted
                );
            }
            let rows: Vec<_> =
                r.b.elements
                    .iter()
                    .skip(r.b.implied.as_ref().unwrap().from)
                    .map(|e| (e.id, e.ty, e.props.to_json()))
                    .collect();
            if let Some(expected) = &expected {
                assert_eq!(&rows, expected);
            } else {
                expected = Some(rows);
            }
            assert_eq!(
                source_ids,
                r.user_elements()
                    .map(|e| r.element_id(e))
                    .collect::<Vec<_>>()
            );
            assert_eq!(compact, crate::json::model_to_compact_json(&model));
        }
    }
    #[test]
    fn identity_binding_gain_rebuilds_common_tail_and_keeps_static_handles() {
        let target = Uuid::new_v5(&Uuid::NAMESPACE_OID, b"dynamic bound callee");
        let mut model = Model::new();
        model.add_library_source("bases.kerml", LIB);
        model.add_source("binding.kerml",&format!("function F {{in p;return result;}} feature n; feature read=n; feature call='{target}'(1);"));
        assert!(!model.has_errors());
        let mut r = ResolvedModel::build(&model);
        let f = r.resolve_qualified("F").unwrap();
        let call = r
            .user_elements()
            .find(|&e| r.element_type(e) == "InvocationExpression")
            .unwrap();
        r.implied_relationships(call);
        assert!(matches!(
            r.b.dynamic_graph.as_ref().unwrap().outcome,
            Outcome::Declined(_)
        ));
        let boundary = r.b.implied.as_ref().unwrap().owned_results_from;
        let stable: Vec<_> = r.b.elements.iter().take(boundary).map(|e| e.id).collect();
        let old_f = r.element_id(f);
        r.override_ids(&HashMap::from([(old_f, target)]));
        let old_epoch = r.b.publication.revision();
        assert!(r.bind_id_spelled_references().contains(&target));
        assert!(!old_epoch.same_as(&r.b.publication.revision()));
        assert!(r.b.dynamic_graph.is_none());
        assert_eq!(r.b.elements.len(), boundary);
        for (index, expected) in stable.into_iter().enumerate() {
            assert_eq!(
                r.element_id(ElementRef(index)),
                if expected == old_f { target } else { expected }
            );
        }
        r.implied_relationships(call);
        assert_eq!(
            r.b.dynamic_graph.as_ref().unwrap().outcome,
            Outcome::Accepted
        );
        assert!(
            r.b.value_context_bases(call.0, &mut 0)
                .unwrap()
                .contains(&f.0)
        );
        assert_eq!(
            r.b.elements
                .iter()
                .filter(|e| e.ty == "BindingConnector")
                .count(),
            1
        );
    }
}

#[cfg(test)]
mod freshness_tests {
    use super::*;
    use crate::{
        json::{
            ResolvedModel,
            type_relations::{RelationFact, TypeRelations},
        },
        model::Model,
    };
    fn fixture(source: &str) -> ResolvedModel {
        let mut m = Model::new();
        m.add_source("fresh.kerml", source);
        assert!(!m.has_errors());
        ResolvedModel::build(&m)
    }
    #[test]
    fn completed_positional_reads_share_dynamic_owner_guards_without_static_preparation() {
        let mut r = fixture("function F {in p;} feature call=F(1);");
        let p = r.resolve_qualified("F::p").unwrap().0;
        let f = r.resolve_qualified("F").unwrap().0;
        let invocation = r
            .user_elements()
            .find(|&e| r.element_type(e) == "InvocationExpression")
            .unwrap();
        r.implied_relationships(invocation);
        assert!(r.b.effective_dynamic_plan().is_some());
        r.b.positional_redefinitions = None;
        r.b.supported_implied = None;
        let before = r.b.elements.observe_revision();
        assert!(r.b.completed_positional_targets(p).is_some());
        assert!(r.b.semantic_inheritance_bases(p, true, &mut 0).is_some());
        assert!(r.b.positional_redefinitions.is_none());
        assert!(r.b.supported_implied.is_none());
        let snapshot = Arc::make_mut(r.b.dynamic_graph.as_mut().unwrap());
        let plan = Arc::make_mut(snapshot.plan.as_mut().unwrap());
        plan.positional.incomplete.insert(f);
        assert!(r.b.completed_positional_targets(p).is_none());
        assert!(r.b.cardinality_positional_targets(p, &mut 0).is_none());
        assert!(r.b.semantic_inheritance_bases(p, true, &mut 0).is_none());
        assert!(r.b.positional_redefinitions.is_none());
        assert!(r.b.supported_implied.is_none());
        assert!(r.b.elements.revision().unwrap().same_as(&before));
    }

    #[test]
    fn loaded_name_only_change_revokes_accepted_dynamic_static_dependencies() {
        let mut r = fixture("function F {in p;} feature call=F(1);");
        let invocation = r
            .user_elements()
            .find(|&e| r.element_type(e) == "InvocationExpression")
            .unwrap();
        r.implied_relationships(invocation);
        assert!(r.b.effective_dynamic_plan().is_some());
        assert!(r.b.retained_typing_edges(&mut 0).is_some());
        let rows = r.b.elements.observe_revision();
        r.b.lib_qnames
            .push((Uuid::new_v4(), vec!["changed loaded name evidence".into()]));
        assert!(r.b.elements.revision().unwrap().same_as(&rows));
        r.b.supported_implied = None;
        r.b.positional_redefinitions = None;
        assert!(r.b.effective_dynamic_plan().is_none());
        assert!(!r.b.dynamic_evidence_current(invocation.0));
        assert!(r.b.dynamic_typing_edges(&mut 0).is_none());
    }
    #[test]
    fn unrelated_positional_cycle_remains_incomplete_after_dynamic_acceptance() {
        let mut r = fixture(
            "class Cycle specializes Cycle {in p;} function F {return result;} feature call=F();",
        );
        let p = r.resolve_qualified("Cycle::p").unwrap();
        assert!(r.b.value_context_bases(p.0, &mut 0).is_none());
        let call = r
            .user_elements()
            .find(|&e| r.element_type(e) == "InvocationExpression")
            .unwrap();
        r.implied_relationships(call);
        assert_eq!(
            r.b.dynamic_graph.as_ref().unwrap().outcome,
            Outcome::Accepted
        );
        assert!(r.b.value_context_bases(p.0, &mut 0).is_none());
    }
    #[test]
    fn stale_metadata_cannot_be_recertified_by_identity_override() {
        let mut r = fixture("feature a; function F {in p;return result;} feature call=F(1);");
        let f = r.resolve_qualified("F").unwrap();
        let a = r.resolve_qualified("a").unwrap();
        let call = r
            .user_elements()
            .find(|&e| r.element_type(e) == "InvocationExpression")
            .unwrap();
        r.implied_relationships(call);
        assert_eq!(
            TypeRelations::default().specializes(&mut r.b, call.0, f.0, &mut 0),
            RelationFact::Yes
        );
        let mut held = TypeRelations::default();
        assert_eq!(
            held.specializes(&mut r.b, call.0, f.0, &mut 0),
            RelationFact::Yes
        );
        let count = r.b.elements.len();
        r.b.metadata_association_generation = Some(Arc::new(()));
        assert_eq!(
            held.specializes(&mut r.b, call.0, f.0, &mut 0),
            RelationFact::Unknown
        );
        assert_eq!(
            TypeRelations::default().specializes(&mut r.b, call.0, f.0, &mut 0),
            RelationFact::Unknown
        );
        let old = r.element_id(f);
        let next = Uuid::new_v5(&Uuid::NAMESPACE_OID, b"stale override");
        r.override_ids(&HashMap::from([(old, next)]));
        assert_eq!(r.b.elements.len(), count);
        assert!(matches!(
            r.b.dynamic_graph.as_ref().unwrap().outcome,
            Outcome::Declined(Refusal::Stale)
        ));
        assert!(r.b.dynamic_graph.as_ref().unwrap().plan.is_some());
        assert_eq!(
            TypeRelations::default().specializes(&mut r.b, call.0, f.0, &mut 0),
            RelationFact::Unknown
        );
        assert_eq!(
            TypeRelations::default().owning_type(&mut r.b, a.0, &mut 0),
            Some(None)
        );
        assert!(r.b.value_context_bases(call.0, &mut 0).is_none());
        r.implied_relationships(call);
        assert_eq!(r.b.elements.len(), count);
    }
    #[test]
    fn same_length_mutation_invalidates_new_and_memoized_positive_proofs() {
        let mut r = fixture("function F {return result;} feature call=F();");
        let f = r.resolve_qualified("F").unwrap();
        let call = r
            .user_elements()
            .find(|&e| r.element_type(e) == "InvocationExpression")
            .unwrap();
        r.implied_relationships(call);
        let mut proof = TypeRelations::default();
        assert_eq!(
            proof.specializes(&mut r.b, call.0, f.0, &mut 0),
            RelationFact::Yes
        );
        // A value-preserving write must still revoke the row revision.
        let id = r.element_id(call);
        r.b.elements[call.0].id = id;
        assert_eq!(
            proof.specializes(&mut r.b, call.0, f.0, &mut 0),
            RelationFact::Unknown
        );
        assert_eq!(
            TypeRelations::default().specializes(&mut r.b, call.0, f.0, &mut 0),
            RelationFact::Unknown
        );
    }
    #[test]
    fn changed_name_table_preserves_frozen_graph_and_invalidates_held_proofs() {
        let mut r = fixture("function F {return result;} feature call=F();");
        let f = r.resolve_qualified("F").unwrap();
        let call = r
            .user_elements()
            .find(|&e| r.element_type(e) == "InvocationExpression")
            .unwrap();
        r.implied_relationships(call);
        let ids: Vec<_> = r.b.elements.iter().map(|e| e.id).collect();
        let mut proof = TypeRelations::default();
        assert_eq!(
            proof.specializes(&mut r.b, call.0, f.0, &mut 0),
            RelationFact::Yes
        );
        r.set_library_names(&HashMap::from([(
            Uuid::new_v5(&Uuid::NAMESPACE_OID, b"new names").to_string(),
            vec!["New".into(), "Name".into()],
        )]));
        assert!(r.b.effective_dynamic_plan().is_some());
        assert_eq!(
            proof.specializes(&mut r.b, call.0, f.0, &mut 0),
            RelationFact::Unknown
        );
        assert_eq!(
            TypeRelations::default().specializes(&mut r.b, call.0, f.0, &mut 0),
            RelationFact::Yes
        );
        assert_eq!(ids, r.b.elements.iter().map(|e| e.id).collect::<Vec<_>>());
    }
}

#[cfg(test)]
mod lookup_tests {
    use super::*;
    use crate::{
        json::{
            ResolvedModel,
            type_relations::{RelationFact, TypeRelations},
        },
        model::Model,
    };
    #[test]
    fn scoped_feature_callee_uses_identity_without_fabricating_invocation_scope() {
        let mut m = Model::new();
        m.add_source("lookup.kerml","class A {feature old;} class B specializes A {feature renamed redefines old;} feature callee {feature nested;} feature call=callee();");
        assert!(!m.has_errors());
        let mut r = ResolvedModel::build(&m);
        let callee = r.resolve_qualified("callee").unwrap();
        let call = r
            .user_elements()
            .find(|&e| r.element_type(e) == "InvocationExpression")
            .unwrap();
        assert!(r.b.elem_scope.get(&call.0).is_none());
        let callee_scope = *r.b.elem_scope.get(&callee.0).unwrap();
        let before = r.b.base_scopes_split(callee_scope);
        let scopes = r.b.scopes.len();
        r.implied_relationships(call);
        assert_eq!(
            r.b.dynamic_graph.as_ref().unwrap().outcome,
            Outcome::Accepted
        );
        assert_eq!(r.b.scopes.len(), scopes);
        assert!(r.b.elem_scope.get(&call.0).is_none());
        assert!(
            r.b.value_context_bases(call.0, &mut 0)
                .unwrap()
                .contains(&callee.0)
        );
        assert_eq!(
            TypeRelations::default().specializes(&mut r.b, call.0, callee.0, &mut 0),
            RelationFact::Yes
        );
        assert_eq!(r.b.base_scopes_split(callee_scope), before);
        r.b.static_planning = true;
        assert_eq!(r.b.base_scopes_split(callee_scope), before);
        r.b.static_planning = false;
        assert!(r.resolve_qualified("callee::nested").is_some());
    }
}

#[cfg(test)]
mod refusal_tests {
    use super::*;
    use crate::{json::ResolvedModel, model::Model};
    fn fixture() -> ResolvedModel {
        let mut m = Model::new();
        m.add_source("refusal.kerml","function F {return result;} feature spare; feature n; feature read=n; feature call=F();");
        assert!(!m.has_errors());
        ResolvedModel::build(&m)
    }
    #[test]
    fn dynamic_row_collision_preserves_admitted_result_family() {
        let mut r = fixture();
        let f = r.resolve_qualified("F").unwrap();
        let spare = r.resolve_qualified("spare").unwrap();
        let call = r
            .user_elements()
            .find(|&e| r.element_type(e) == "InvocationExpression")
            .unwrap();
        let reference = r
            .user_elements()
            .find(|&e| r.element_type(e) == "FeatureReferenceExpression")
            .unwrap();
        let collision = Uuid::new_v5(
            &Uuid::NAMESPACE_OID,
            format!(
                "{}/implied/FeatureTyping/{}",
                r.element_id(call),
                r.element_id(f)
            )
            .as_bytes(),
        );
        r.override_ids(&HashMap::from([(r.element_id(spare), collision)]));
        r.implied_relationships(call);
        assert!(matches!(
            r.b.dynamic_graph.as_ref().unwrap().outcome,
            Outcome::Declined(Refusal::Collision)
        ));
        assert!(
            r.b.semantic_ownership
                .as_ref()
                .unwrap()
                .result(reference.0)
                .is_some()
        );
        assert_eq!(
            r.b.elements
                .iter()
                .filter(|e| e.ty == "BindingConnector")
                .count(),
            1
        );
        assert_eq!(
            r.b.elements.len() - r.b.implied.as_ref().unwrap().owned_results_from,
            14
        );
    }
    #[test]
    fn exhausted_dynamic_preparation_preserves_admitted_result_family_and_is_cached() {
        let mut r = fixture();
        let call = r
            .user_elements()
            .find(|&e| r.element_type(e) == "InvocationExpression")
            .unwrap();
        let reference = r
            .user_elements()
            .find(|&e| r.element_type(e) == "FeatureReferenceExpression")
            .unwrap();
        // Charge concrete input-string work before cloning the name table. This
        // reaches the real transaction's dynamic refusal independently of the
        // result family's untouched full admission allowance.
        r.b.external_implied_names
            .insert("X".repeat(crate::eval::MAX_STEPS), Uuid::nil());
        r.implied_relationships(call);
        let snapshot = r.b.dynamic_graph.clone().unwrap();
        assert!(matches!(
            snapshot.outcome,
            Outcome::Declined(Refusal::WorkLimit)
        ));
        assert!(
            r.b.semantic_ownership
                .as_ref()
                .unwrap()
                .result(reference.0)
                .is_some()
        );
        assert_eq!(
            r.b.elements.len() - r.b.implied.as_ref().unwrap().owned_results_from,
            14
        );
        let count = r.b.elements.len();
        r.implied_relationships(call);
        assert!(Arc::ptr_eq(&snapshot, r.b.dynamic_graph.as_ref().unwrap()));
        assert_eq!(r.b.elements.len(), count);
    }
}

#[cfg(test)]
mod mutation_replay_tests {
    use super::*;
    use crate::{json::ResolvedModel, model::Model};
    #[test]
    fn completed_identity_binding_no_work_path_preserves_admitted_snapshot() {
        let target = Uuid::new_v5(&Uuid::NAMESPACE_OID, b"bound callee lifecycle");
        let mut m = Model::new();
        m.add_source("lifecycle.kerml",&format!("function F {{in p;return result;}} feature n; feature read=n; feature call='{target}'(1);"));
        assert!(!m.has_errors());
        let mut r = ResolvedModel::build(&m);
        let f = r.resolve_qualified("F").unwrap();
        let call = r
            .user_elements()
            .find(|&e| r.element_type(e) == "InvocationExpression")
            .unwrap();
        r.override_ids(&HashMap::from([(r.element_id(f), target)]));
        r.bind_id_spelled_references();
        r.implied_relationships(call);
        assert!(r.b.id_binding_pending.is_empty());
        assert!(!r.b.id_spelled_targets.is_empty());
        let before = r.b.dynamic_graph.clone().unwrap();
        let count = r.b.elements.len();
        assert!(r.bind_id_spelled_references().is_empty());
        assert!(Arc::ptr_eq(&before, r.b.dynamic_graph.as_ref().unwrap()));
        assert!(before.epoch.same_as(&r.b.publication.revision()));
        assert_eq!(count, r.b.elements.len());
    }
    #[test]
    fn no_op_identity_calls_keep_accepted_epoch_and_snapshot() {
        let mut m = Model::new();
        m.add_source(
            "noop.kerml",
            "function F {return result;} feature call=F();",
        );
        let mut r = ResolvedModel::build(&m);
        let f = r.resolve_qualified("F").unwrap();
        let call = r
            .user_elements()
            .find(|&e| r.element_type(e) == "InvocationExpression")
            .unwrap();
        r.implied_relationships(call);
        let before = r.b.dynamic_graph.clone().unwrap();
        let id = r.element_id(f);
        assert!(r.override_ids(&HashMap::new()).is_empty());
        assert!(r.override_ids(&HashMap::from([(id, id)])).is_empty());
        assert!(Arc::ptr_eq(&before, r.b.dynamic_graph.as_ref().unwrap()));
        assert!(before.epoch.same_as(&r.b.publication.revision()));
    }
}
