//! Query-local proofs for supported inheritance and import providers.
use super::Builder;
use crate::metaclass::conforms;
use std::{
    collections::{HashMap, HashSet},
    sync::Arc,
};

#[cfg(test)]
mod mixed_tests;
mod recursive;
#[cfg(test)]
mod recursive_tests;

#[derive(PartialEq, Eq, PartialOrd, Ord)]
enum Dependency {
    Scope(usize),
    Recursive(usize, bool),
    Package(usize),
}

/// An absence proof must include dependencies skipped by inherited lookup.
/// Kept local to one query: no stale positive result survives graph changes.
#[derive(Default)]
pub(crate) struct ProviderCompleteness {
    publication: Option<super::publication::Revision>,
    known: HashMap<(usize, usize), bool>,
    active: HashSet<usize>,
    // Shared immutable topology, retained once for this proof query. Incoming
    // standalone Annotation rows are not represented completely by metadata_of.
    annotations: Option<Arc<super::structural_index::StoredStructure>>,
    metadata_generation: Option<Arc<()>>,
    planner_state: Option<(bool, bool)>,
    retained_plan: Option<Arc<super::implied::SupportedImpliedSpecializations>>,
    transient_incomplete: bool,
    recursive: recursive::Proof,
    scope_revision: Option<crate::layered::Revision>,
    recursive_import_domains: Option<Arc<super::structural_index::ImportDomains>>,
}

impl ProviderCompleteness {
    pub(super) fn reset_with_budget(&mut self, steps: &mut usize) -> Option<()> {
        if !self.invalidate_known(steps) {
            return None;
        }
        self.recursive.charge_roots_drop(steps)?;
        *self = Self::default();
        Some(())
    }

    pub(crate) fn scope(&mut self, b: &mut Builder, scope: usize, steps: &mut usize) -> bool {
        // Resolver caches and element-to-scope maps have no content revision.
        // Never reuse semantic facts depending on recursive evidence across calls.
        if self.recursive.touched && !self.invalidate_known(steps) {
            return false;
        }
        let scopes = b.scopes.observe_revision();
        if self
            .scope_revision
            .as_ref()
            .is_some_and(|old| !old.same_as(&scopes))
            && !self.invalidate_known(steps)
        {
            return false;
        }
        self.scope_revision = Some(scopes);
        let epoch = b.publication.revision();
        match &self.publication {
            Some(previous) if !previous.same_as(&epoch) => return false,
            None => self.publication = Some(epoch),
            _ => {}
        }
        if b.positional_planning || !self.prepare_annotations(b, steps) {
            return false;
        }
        let state = (b.semantic_ready, b.positional_redefinitions.is_some());
        let same_plan = match (&self.retained_plan, &b.supported_implied) {
            (None, None) => true,
            (Some(old), Some(current)) => Arc::ptr_eq(old, current),
            _ => false,
        };
        if self.planner_state != Some(state) || !same_plan {
            if !self.invalidate_known(steps) {
                return false;
            }
            self.planner_state = Some(state);
            self.retained_plan = b.supported_implied.clone();
        }
        if let Some(&complete) = self.known.get(&(scope, 0)) {
            *steps = steps.saturating_add(1);
            return *steps <= crate::eval::MAX_STEPS && complete;
        }
        if !charge_provenance(b, steps) {
            return false;
        }
        self.transient_incomplete = false;
        neutral(b, |b| {
            if b.effective_positional_redefinitions().is_none()
                && !b.ensure_positional_redefinitions_with_budget(steps)
            {
                return false;
            }
            self.planner_state = Some((b.semantic_ready, b.positional_redefinitions.is_some()));
            self.retained_plan = b.supported_implied.clone();
            self.scope_inner(b, scope, 0, steps)
        })
    }

    fn invalidate_known(&mut self, steps: &mut usize) -> bool {
        *steps = steps
            .saturating_add(self.known.capacity())
            .saturating_add(self.active.capacity());
        if *steps > crate::eval::MAX_STEPS {
            return false;
        }
        if !self.recursive.clear(steps) {
            return false;
        }
        self.known.clear();
        self.active.clear();
        true
    }

    fn prepare_annotations(&mut self, b: &mut Builder, steps: &mut usize) -> bool {
        let same_metadata = match (
            &self.metadata_generation,
            &b.metadata_association_generation,
        ) {
            (None, None) => true,
            (Some(old), Some(current)) => Arc::ptr_eq(old, current),
            _ => false,
        };
        if !same_metadata {
            if !self.invalidate_known(steps) {
                return false;
            }
            self.annotations = None;
            self.metadata_generation = b.metadata_association_generation.clone();
        }
        if b.metadata_associations_incomplete {
            if !self.invalidate_known(steps) {
                return false;
            }
            return false;
        }
        if self
            .annotations
            .as_ref()
            .is_some_and(|index| index.is_current(b))
        {
            *steps = steps.saturating_add(1);
            return *steps <= crate::eval::MAX_STEPS;
        }
        // No scope result survives an identity/ownership/annotation mutation.
        // Failed publication leaves no partial absence certificate to reuse.
        if !self.invalidate_known(steps) {
            return false;
        }
        self.annotations = None;
        let Some(index) = super::structural_index::StoredStructure::for_annotations(b, steps)
        else {
            return false;
        };
        self.recursive_import_domains = if index.has_recursive_import {
            let Some(domains) = index.import_domains(b, steps) else {
                return false;
            };
            Some(domains)
        } else {
            None
        };
        self.annotations = Some(index);
        true
    }

    fn scope_inner(
        &mut self,
        b: &mut Builder,
        scope: usize,
        depth: usize,
        steps: &mut usize,
    ) -> bool {
        *steps = steps.saturating_add(1);
        if depth > super::MAX_RESOLUTION_DEPTH || *steps > crate::eval::MAX_STEPS {
            return false;
        }
        if let Some(&complete) = self.known.get(&(scope, depth)) {
            return complete;
        }
        if !self.active.insert(scope) {
            return false;
        }
        let complete = self
            .dependencies(b, scope, depth, false, steps)
            .is_some_and(|dependencies| self.complete_dependencies(b, dependencies, depth, steps));
        self.active.remove(&scope);
        // Exhaustion is query-local, not evidence that this scope is incomplete.
        // A later comparison can retry with a fresh budget on the same provider.
        if *steps <= crate::eval::MAX_STEPS && (complete || !self.transient_incomplete) {
            self.known.insert((scope, depth), complete);
        }
        complete
    }

    fn complete_dependencies(
        &mut self,
        b: &mut Builder,
        dependencies: Vec<Dependency>,
        depth: usize,
        steps: &mut usize,
    ) -> bool {
        dependencies.into_iter().all(|dependency| match dependency {
            Dependency::Scope(s) => self.scope_inner(b, s, depth + 1, steps),
            Dependency::Recursive(s, all) => self.recursive_scope(b, s, depth + 1, all, steps),
            Dependency::Package(s) => self.package_scope(b, s, depth + 1, None, steps),
        })
    }

    fn reference(b: &mut Builder, relationship: usize, key: &str) -> Option<usize> {
        let id = b.elements[relationship].props.get(key)?.as_reference()?;
        b.element_index_of_uuid(id)
    }

    fn dependencies(
        &mut self,
        b: &mut Builder,
        scope: usize,
        depth: usize,
        literal_package: bool,
        steps: &mut usize,
    ) -> Option<Vec<Dependency>> {
        if b.metadata_associations_incomplete {
            return None;
        }
        if self
            .recursive_import_domains
            .as_ref()
            .is_some_and(|domains| !domains.localized())
        {
            return None;
        }
        let context = &b.scopes[scope];
        let inverse_recursive = context.owner.is_some_and(|owner| {
            self.recursive_import_domains
                .as_ref()
                .is_some_and(|domains| domains.recursive_owner(owner))
        });
        self.recursive.touched |= inverse_recursive;
        if context.owner.is_some_and(|owner| {
            self.recursive_import_domains
                .as_ref()
                .is_some_and(|domains| !domains.owner_complete(owner))
        }) {
            return None;
        }
        let relationships = context
            .owner
            .map_or(0, |e| b.elements[e].owned_relationships.len());
        *steps = steps
            .saturating_add(relationships)
            .saturating_add(context.imports.len())
            .saturating_add(context.member_imports.len())
            .saturating_add(context.aliases.len())
            .saturating_add(context.bases.len())
            .saturating_add(context.implied_bases.len());
        if *steps > crate::eval::MAX_STEPS {
            return None;
        }
        // Chains and filters need a richer proof. No
        // inference is preferable to treating skipped results as absence.
        if !context.filters.is_empty()
            || !context.chain_bases.is_empty()
            || context.imports.iter().any(|i| !i.filters.is_empty())
            || context.member_imports.iter().any(|i| !i.filters.is_empty())
        {
            return None;
        }
        let owner = context.owner;
        if owner.is_some_and(|owner| {
            !b.dynamic_evidence_current(owner) || !b.result_redefinition_evidence_current(owner)
        }) {
            return None;
        }
        // Semantic metadata may add bases that the current resolver omits when
        // an annotation is incomplete. Their absence needs a separate proof.
        if owner.is_some_and(|e| b.metadata_of.get(&e).is_some_and(|m| !m.is_empty())) {
            return None;
        }
        let annotations = self.annotations.as_ref()?;
        if !annotations.is_current(b)
            || !annotations.ids_unique
            || annotations.annotations_incomplete
            || owner.is_some_and(|e| annotations.metadata_annotation_targets.contains(&e))
        {
            // Annotation-dependent supertype absence is not implemented. A
            // separately witnessed positive path remains usable by callers.
            return None;
        }
        let namespaces: Vec<_> = context
            .imports
            .iter()
            .enumerate()
            .map(|(i, entry)| (i, entry.relationship, entry.recursive))
            .collect();
        let members: Vec<_> = context
            .member_imports
            .iter()
            .map(|i| i.relationship)
            .collect();
        let aliases: Vec<_> = context.aliases.iter().map(|(_, _, r)| *r).collect();
        let relationships = owner
            .map(|e| b.elements[e].owned_relationships.clone())
            .unwrap_or_default();
        let mut dependencies = Vec::new();
        let mut recursive_domain = literal_package
            || inverse_recursive
            || namespaces.iter().any(|&(_, _, recursive)| recursive);
        for r in relationships {
            if conforms(b.elements[r].ty, "Import")
                && b.elements[r]
                    .props
                    .get("isRecursive")
                    .is_some_and(|v| v.as_bool() != Some(false))
            {
                recursive_domain = true;
            }
            if conforms(b.elements[r].ty, "Specialization") {
                let id = super::implied::specialization_target(&b.elements[r])?;
                let target = b.element_index_of_uuid(id)?;
                if !conforms(b.elements[target].ty, "Type") {
                    return None;
                }
                dependencies.push(Dependency::Scope(*b.elem_scope.get(&target)?));
            }
        }
        if recursive_domain {
            self.recursive.touched = true;
            self.recursive_import_domain(b, scope, depth, literal_package, steps)?;
        }
        for (index, r, recursive) in namespaces {
            if recursive_domain {
                let (target, all) = self.literal_namespace_import(b, scope, index, depth, steps)?;
                dependencies.push(if recursive {
                    Dependency::Recursive(target, all)
                } else {
                    Dependency::Package(target)
                });
                continue;
            }
            // A stale resolver entry cannot erase a raw recursive obligation.
            if b.elements[r]
                .props
                .get("isRecursive")
                .is_some_and(|v| v.as_bool() != Some(false))
            {
                return None;
            }
            let target = Self::reference(b, r, "importedNamespace")?;
            if !conforms(b.elements[target].ty, "Namespace") {
                return None;
            }
            dependencies.push(Dependency::Scope(*b.elem_scope.get(&target)?));
        }
        for r in members {
            let membership = Self::reference(b, r, "importedMembership")?;
            if !conforms(b.elements[membership].ty, "Membership") {
                return None;
            }
            b.stored_membership_member(membership)?;
            // A membership import contributes this exact member, not its
            // declaring namespace's unrelated imports or other members.
        }
        for alias in aliases {
            b.stored_membership_member(alias)?;
        }
        let bases = bounded_base_scopes(b, scope, steps);
        if bases.is_none() && b.base_cache[scope].is_none() {
            // Later resolver warming can supply the missing identity evidence.
            // Do not freeze this coverage limitation as a negative scope memo.
            self.transient_incomplete = true;
        }
        dependencies.extend(bases?.into_iter().map(Dependency::Scope));
        *steps = steps.saturating_add(
            dependencies
                .len()
                .saturating_mul(dependencies.len().max(1).ilog2() as usize + 2),
        );
        if *steps > crate::eval::MAX_STEPS {
            return None;
        }
        dependencies.sort_unstable();
        dependencies.dedup();
        Some(dependencies)
    }
}

/// Reuse completed resolver evidence without entering its unbudgeted cold
/// name walk. Cold semantic bases use the shared stored/retained identity graph.
/// A non-library implied base the resolver alone reads has no such
/// certificate; an uncached context requiring it remains unsupported.
fn bounded_base_scopes(b: &mut Builder, scope: usize, steps: &mut usize) -> Option<Vec<usize>> {
    if let Some((cached, _)) = &b.base_cache[scope] {
        *steps = steps.saturating_add(cached.len());
        if *steps > crate::eval::MAX_STEPS {
            return None;
        }
        return bounded_dynamic_base_scopes(b, scope, cached.clone(), steps);
    }
    let context = &b.scopes[scope];
    if context.bases.is_empty() && context.implied_bases.is_empty() {
        return bounded_dynamic_base_scopes(b, scope, Vec::new(), steps);
    }
    if context
        .implied_bases
        .iter()
        .any(|name| name.segments.len() < 2)
    {
        return None;
    }
    let owner = context.owner?;
    let bases = b.semantic_inheritance_bases(owner, b.semantic_ready, steps)?;
    *steps = steps.saturating_add(bases.len());
    if *steps > crate::eval::MAX_STEPS {
        return None;
    }
    let scopes = bases
        .into_iter()
        .filter_map(|base| b.elem_scope.get(&base).copied())
        .filter(|&base| base != scope)
        .collect();
    bounded_dynamic_base_scopes(b, scope, scopes, steps)
}

/// Overlay only admitted dynamic dependencies. Cached resolver inputs stay
/// static; missing target scopes cannot certify an empty provider dependency.
fn bounded_dynamic_base_scopes(
    b: &Builder,
    scope: usize,
    mut bases: Vec<usize>,
    steps: &mut usize,
) -> Option<Vec<usize>> {
    let Some(owner) = b.scopes.get(scope)?.owner else {
        return Some(bases);
    };
    if !b.dynamic_evidence_current(owner) {
        return None;
    }
    let Some(plan) = b.effective_dynamic_plan() else {
        return Some(bases);
    };
    let added = plan
        .added_bases
        .get(&owner)
        .map(Vec::as_slice)
        .unwrap_or(&[]);
    *steps = steps.saturating_add(added.len());
    if *steps > crate::eval::MAX_STEPS {
        return None;
    }
    for &target in added {
        *steps = steps.saturating_add(2).saturating_add(bases.len());
        if *steps > crate::eval::MAX_STEPS {
            return None;
        }
        if !crate::metaclass::conforms(b.elements.get(target)?.ty, "Type") {
            return None;
        }
        let target_scope = *b.elem_scope.get(&target)?;
        if b.scopes.get(target_scope)?.owner != Some(target) {
            return None;
        }
        if target_scope != scope && !bases.contains(&target_scope) {
            bases.push(target_scope);
        }
    }
    Some(bases)
}

/// Account for every saved provenance allocation before changing lookup state.
fn charge_provenance(b: &Builder, steps: &mut usize) -> bool {
    *steps = steps
        .saturating_add(b.used_imports.capacity())
        .saturating_add(b.current_misses.len())
        .saturating_add(b.root_misses.capacity());
    if *steps > crate::eval::MAX_STEPS {
        return false;
    }
    for text in b.current_misses.iter().chain(b.root_misses.iter()) {
        *steps = steps.saturating_add(text.len());
        if *steps > crate::eval::MAX_STEPS {
            return false;
        }
    }
    true
}

/// Proofs may warm resolver caches, but must not change the caller's lookup
/// context or import-use/miss provenance. Stabilize implied planning first.
fn neutral<T>(b: &mut Builder, f: impl FnOnce(&mut Builder) -> T) -> T {
    let saved = (
        b.exclude.take(),
        std::mem::replace(&mut b.declared_only, false),
        b.redefinition_lookup_owner.take(),
        b.redefinition_lookup_base.take(),
        std::mem::replace(&mut b.recorded_lookup_suppressed, false),
        b.identity_origin_unit,
        std::mem::replace(&mut b.probing, false),
        b.widen.take(),
    );
    let used = b.used_imports.clone();
    let imports = std::mem::take(&mut b.query_imports);
    let misses = b.current_misses.clone();
    let roots = b.root_misses.clone();
    let result = f(b);
    (
        b.exclude,
        b.declared_only,
        b.redefinition_lookup_owner,
        b.redefinition_lookup_base,
        b.recorded_lookup_suppressed,
        b.identity_origin_unit,
        b.probing,
        b.widen,
    ) = saved;
    b.used_imports = used;
    b.query_imports = imports;
    b.current_misses = misses;
    b.root_misses = roots;
    result
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::json::{LookupAccess, ResolvedModel};
    use crate::model::Model;

    #[test]
    fn accepted_scope_dependencies_overlay_cold_and_cached_static_inputs_with_budget() {
        for unsupported in [false, true] {
            for warm in [false, true] {
                let mut model = Model::new();
                let body = if unsupported { "filter true;" } else { "" };
                model.add_source("accepted-scope.kerml", &format!(
                    "classifier Caller; classifier Callee {{{body}}} function F {{return result;}} feature call=F();"
                ));
                assert!(!model.has_errors());
                let mut r = ResolvedModel::build(&model);
                let caller = r.resolve_qualified("Caller").unwrap().0;
                let callee = r.resolve_qualified("Callee").unwrap().0;
                let scope = *r.b.elem_scope.get(&caller).unwrap();
                let callee_scope = *r.b.elem_scope.get(&callee).unwrap();
                let invocation = r
                    .user_elements()
                    .find(|&e| r.element_type(e) == "InvocationExpression")
                    .unwrap();
                r.implied_relationships(invocation);
                assert!(r.b.effective_dynamic_plan().is_some());
                // The parser currently gives Invocation no textual body scope.
                // Exercise the accepted overlay seam with real existing scopes;
                // no scope is fabricated or added to production admission.
                let snapshot = Arc::make_mut(r.b.dynamic_graph.as_mut().unwrap());
                let plan = Arc::make_mut(snapshot.plan.as_mut().unwrap());
                plan.added_bases.insert(caller, vec![callee]);
                plan.affected_owners.insert(caller);
                assert!(r.b.scopes[scope].bases.is_empty());
                // Isolate the otherwise-empty static-provider case after the
                // accepted identity slice has been supplied by the test seam.
                r.b.scopes[scope].implied_bases.clear();
                r.b.base_cache[scope] = warm.then(|| (Vec::new(), 0));
                let before = r.b.base_cache[scope].clone();
                let mut near_limit = crate::eval::MAX_STEPS;
                assert!(bounded_base_scopes(&mut r.b, scope, &mut near_limit).is_none());
                assert!(near_limit > crate::eval::MAX_STEPS);
                assert_eq!(r.b.base_cache[scope], before);
                assert_eq!(
                    bounded_base_scopes(&mut r.b, scope, &mut 0),
                    Some(vec![callee_scope])
                );
                assert_eq!(r.b.base_cache[scope], before);
                let mut proof = ProviderCompleteness::default();
                let mut exhausted = crate::eval::MAX_STEPS;
                assert!(!proof.scope(&mut r.b, scope, &mut exhausted));
                assert_eq!(proof.scope(&mut r.b, scope, &mut 0), !unsupported);
                assert_eq!(proof.scope(&mut r.b, scope, &mut 0), !unsupported);
                assert_eq!(r.b.base_cache[scope], before);
                let mut scopes = crate::layered::LayeredMap::default();
                for (&element, &scope) in r.b.elem_scope.iter() {
                    if element != callee {
                        scopes.insert(element, scope);
                    }
                }
                r.b.elem_scope = scopes;
                assert!(bounded_base_scopes(&mut r.b, scope, &mut 0).is_none());
            }
        }
    }

    #[test]
    fn held_provider_observes_retained_replacement_even_after_table_rebuild() {
        let mut model = Model::new();
        model.add_source("retained-provider.kerml", "classifier A;");
        let mut r = ResolvedModel::build(&model);
        let a = r.resolve_qualified("A").unwrap().0;
        let scope = *r.b.elem_scope.get(&a).unwrap();
        let mut proof = ProviderCompleteness::default();
        assert!(proof.scope(&mut r.b, scope, &mut 0));
        let old = proof.retained_plan.clone().unwrap();
        let state = proof.planner_state;
        // Exercise retained-authority replacement independently of the public
        // name setter's stronger central publication epoch invalidation.
        r.b.supported_implied = None;
        r.b.positional_redefinitions = None;
        assert!(r.b.ensure_positional_redefinitions_with_budget(&mut 0));
        assert_eq!(
            state,
            Some((r.b.semantic_ready, r.b.positional_redefinitions.is_some()))
        );
        assert!(!Arc::ptr_eq(&old, r.b.supported_implied.as_ref().unwrap()));
        let mut steps = crate::eval::MAX_STEPS - 1;
        assert!(!proof.scope(&mut r.b, scope, &mut steps));
        assert!(steps > crate::eval::MAX_STEPS);
        assert!(Arc::ptr_eq(&old, proof.retained_plan.as_ref().unwrap()));
        assert_eq!(proof.planner_state, state);
        assert!(proof.scope(&mut r.b, scope, &mut 0));
        assert!(Arc::ptr_eq(
            proof.retained_plan.as_ref().unwrap(),
            r.b.supported_implied.as_ref().unwrap()
        ));
    }

    #[test]
    fn held_provider_refuses_a_new_publication_epoch_without_refreshing_old_facts() {
        let mut model = Model::new();
        model.add_source("provider-epoch.kerml", "classifier A;");
        let mut r = ResolvedModel::build(&model);
        let a = r.resolve_qualified("A").unwrap().0;
        let scope = *r.b.elem_scope.get(&a).unwrap();
        let mut proof = ProviderCompleteness::default();
        assert!(proof.scope(&mut r.b, scope, &mut 0));
        let old = proof.retained_plan.clone().unwrap();
        let epoch = proof.publication.clone().unwrap();
        r.set_library_names(&HashMap::new());
        assert!(r.b.ensure_positional_redefinitions_with_budget(&mut 0));
        let mut steps = crate::eval::MAX_STEPS - 1;
        assert!(!proof.scope(&mut r.b, scope, &mut steps));
        assert_eq!(steps, crate::eval::MAX_STEPS - 1);
        assert!(!proof.scope(&mut r.b, scope, &mut 0));
        assert!(Arc::ptr_eq(&old, proof.retained_plan.as_ref().unwrap()));
        assert!(epoch.same_as(proof.publication.as_ref().unwrap()));
        assert!(ProviderCompleteness::default().scope(&mut r.b, scope, &mut 0));
    }

    #[test]
    fn positive_provider_does_not_accept_a_legacy_in_progress_sentinel() {
        let mut model = Model::new();
        model.add_source("sentinel.kerml", "classifier A;");
        let mut r = ResolvedModel::build(&model);
        let a = r.resolve_qualified("A").unwrap().0;
        let scope = *r.b.elem_scope.get(&a).unwrap();
        let mut proof = ProviderCompleteness::default();
        assert!(proof.scope(&mut r.b, scope, &mut 0));
        let plan = r.b.positional_redefinitions.replace(Default::default());
        r.b.positional_planning = true;
        assert!(!r.b.ensure_positional_redefinitions_with_budget(&mut 0));
        assert!(!proof.scope(&mut r.b, scope, &mut 0));
        assert_eq!(proof.known.get(&(scope, 0)), Some(&true));
        r.b.positional_planning = false;
        r.b.positional_redefinitions = plan;
        assert!(proof.scope(&mut r.b, scope, &mut 0));
    }

    #[test]
    fn held_provider_charges_invalidation_before_discarding_cached_scopes() {
        let mut model = Model::new();
        let mut source = "classifier Root;".to_string();
        for n in 0..40 {
            source.push_str(&format!(" classifier C{n} specializes Root;"));
        }
        model.add_source("invalidation.kerml", &source);
        let mut r = ResolvedModel::build(&model);
        let mut proof = ProviderCompleteness::default();
        let mut last = 0;
        for n in 0..40 {
            let owner = r.resolve_qualified(&format!("C{n}")).unwrap().0;
            last = *r.b.elem_scope.get(&owner).unwrap();
            assert!(proof.scope(&mut r.b, last, &mut 0));
        }
        let entries = proof.known.len();
        assert!(entries >= 40);
        let planner_state = proof.planner_state;
        r.b.positional_redefinitions = None;
        let mut steps = crate::eval::MAX_STEPS - 3;
        assert!(!proof.scope(&mut r.b, last, &mut steps));
        assert!(steps > crate::eval::MAX_STEPS);
        assert_eq!(proof.planner_state, planner_state);
        assert_eq!(
            proof.known.len(),
            entries,
            "refused clear leaves old facts inaccessible for retry"
        );
        assert!(proof.scope(&mut r.b, last, &mut 0));
        let metadata = proof.metadata_generation.clone();
        r.b.metadata_association_generation = Some(Arc::new(()));
        let entries = proof.known.len();
        let mut steps = crate::eval::MAX_STEPS;
        assert!(!proof.scope(&mut r.b, last, &mut steps));
        assert_eq!(proof.known.len(), entries);
        assert!(match (&metadata, &proof.metadata_generation) {
            (None, None) => true,
            (Some(a), Some(b)) => Arc::ptr_eq(a, b),
            _ => false,
        });
        assert!(steps > crate::eval::MAX_STEPS);
        assert!(proof.scope(&mut r.b, last, &mut 0));
    }

    #[test]
    fn cold_identity_bases_match_warm_explicit_redefinition_and_library_providers() {
        for (source, name) in [
            ("classifier A; classifier B specializes A;", "B"),
            ("feature A; feature B redefines A;", "B"),
            ("class C;", "C"),
        ] {
            let mut model = Model::new();
            model.add_library_source(
                "provider-library.kerml",
                "standard library package Occurrences {class Occurrence;}",
            );
            assert!(
                model
                    .add_source("provider-bases.kerml", source)
                    .diagnostics
                    .is_empty()
            );
            let mut r = ResolvedModel::build(&model);
            let owner = r.resolve_qualified(name).unwrap().0;
            let scope = *r.b.elem_scope.get(&owner).unwrap();
            r.b.base_cache.fill(None);
            let cold = ProviderCompleteness::default().scope(&mut r.b, scope, &mut 0);
            assert!(cold, "{source}");
            assert!(r.b.base_cache[scope].is_none());
            r.b.base_scopes_split(scope);
            let warm = ProviderCompleteness::default().scope(&mut r.b, scope, &mut 0);
            assert_eq!(cold, warm, "{source}");
        }
    }

    #[test]
    fn cold_resolver_only_base_is_not_a_semantic_certificate() {
        let mut model = Model::new();
        model.add_source(
            "parameter-context.kerml",
            "function A {in p;} function B specializes A {in p;}",
        );
        let mut r = ResolvedModel::build(&model);
        let p = r.resolve_qualified("B::p").unwrap().0;
        let scope = *r.b.elem_scope.get(&p).unwrap();
        // Lowering records no non-library implied base of its own any more;
        // install precisely the resolver-only input whose cold proof is
        // unsupported.
        r.b.scopes[scope].implied_bases = vec![super::super::lib_qn("p")];
        r.b.base_cache[scope] = None;
        let mut proof = ProviderCompleteness::default();
        assert!(!proof.scope(&mut r.b, scope, &mut 0));
        assert!(!proof.known.contains_key(&(scope, 0)));
        assert!(r.b.base_cache[scope].is_none());
        // A completed lookup supplies concrete scopes whose raw dependencies
        // still receive the ordinary provider checks; no empty sentinel is used.
        r.b.base_scopes_split(scope);
        let cached = r.b.base_cache[scope].as_ref().unwrap().0.clone();
        let mut steps = 0;
        assert_eq!(
            bounded_base_scopes(&mut r.b, scope, &mut steps),
            Some(cached)
        );
    }

    #[test]
    fn cold_preparation_refuses_without_a_partial_table_and_retries() {
        let mut model = Model::new();
        model.add_source(
            "cold.kerml",
            "function A {in x; return y;} function B specializes A {in x; return y;}",
        );
        let mut r = ResolvedModel::build(&model);
        let owner = r.resolve_qualified("B").unwrap().0;
        let scope = *r.b.elem_scope.get(&owner).unwrap();
        r.b.positional_redefinitions = None;
        r.b.base_cache[scope] = None;
        let mut proof = ProviderCompleteness::default();
        assert!(proof.prepare_annotations(&mut r.b, &mut 0));
        r.b.used_imports.insert(owner);
        r.b.current_misses.push("caller".into());
        let mut steps = crate::eval::MAX_STEPS - 12;
        assert!(!proof.scope(&mut r.b, scope, &mut steps));
        assert!(steps > crate::eval::MAX_STEPS);
        assert!(r.b.positional_redefinitions.is_none());
        assert!(!r.b.positional_planning);
        assert!(proof.known.is_empty());
        assert_eq!(r.b.current_misses, ["caller"]);
        assert!(r.b.used_imports.contains(&owner));
        assert!(proof.scope(&mut r.b, scope, &mut 0));
        let plan = r.b.positional_redefinitions.as_ref().unwrap();
        assert!(!plan.targets.is_empty());
        assert_eq!(proof.known.get(&(scope, 0)), Some(&true));
        assert!(
            r.b.base_cache[scope].is_none(),
            "bounded proof does not run the cold resolver"
        );
        assert!(proof.scope(&mut r.b, scope, &mut 0));
    }

    #[test]
    fn private_planner_guard_prevents_legacy_reentry_and_preserves_readiness() {
        let mut model = Model::new();
        model.add_source("guard.kerml", "function A {in x; return y;}");
        let mut r = ResolvedModel::build(&model);
        r.b.positional_redefinitions = None;
        r.b.positional_planning = true;
        r.b.ensure_positional_redefinitions();
        assert!(!r.b.ensure_positional_redefinitions_with_budget(&mut 0));
        assert!(r.b.positional_redefinitions.is_none());
        r.b.positional_planning = false;
        r.b.semantic_ready = false;
        assert!(r.b.ensure_positional_redefinitions_with_budget(&mut 0));
        assert!(r.b.positional_redefinitions.is_none());
        r.b.semantic_ready = true;
        assert!(r.b.ensure_positional_redefinitions_with_budget(&mut 0));
        assert!(r.b.positional_redefinitions.is_some());
    }

    #[test]
    fn exhausted_dependency_proof_can_retry_with_a_fresh_budget() {
        let mut model = Model::new();
        model.add_source("retry.kerml", "classifier A; classifier B specializes A;");
        let mut r = ResolvedModel::build(&model);
        let b = r.resolve_qualified("B").unwrap().0;
        let scope = *r.b.elem_scope.get(&b).unwrap();
        let mut proof = ProviderCompleteness::default();
        let mut steps = crate::eval::MAX_STEPS - 1;
        assert!(!proof.scope(&mut r.b, scope, &mut steps));
        assert!(steps > crate::eval::MAX_STEPS);
        assert!(!proof.known.contains_key(&(scope, 0)));
        steps = 0;
        assert!(proof.scope(&mut r.b, scope, &mut steps));
        assert_eq!(proof.known.get(&(scope, 0)), Some(&true));
    }

    #[test]
    fn cold_and_memoized_proofs_preserve_context_and_obey_budget() {
        let mut model = Model::new();
        let unit = model.add_source(
            "providers.kerml",
            "package Good { feature n = 4; }
             type Complete { public import Good::*; }
             type Missing { public import Absent::*; }",
        );
        assert!(unit.diagnostics.is_empty());
        let mut r = ResolvedModel::build(&model);
        let complete = r.resolve_qualified("Complete").unwrap().0;
        let missing = r.resolve_qualified("Missing").unwrap().0;
        let b = &mut r.b;
        let complete_scope = *b.elem_scope.get(&complete).unwrap();
        let missing_scope = *b.elem_scope.get(&missing).unwrap();
        b.exclude = Some(complete);
        b.declared_only = true;
        b.redefinition_lookup_owner = Some(complete);
        b.redefinition_lookup_base = Some(missing);
        b.recorded_lookup_suppressed = true;
        b.identity_origin_unit = Some(0);
        b.probing = true;
        b.widen = Some((complete_scope, LookupAccess::All));
        b.used_imports.insert(complete);
        b.query_imports.push((missing, LookupAccess::All));
        b.current_misses.push("caller miss".into());
        b.root_misses.insert("caller root".into());
        let context = |b: &Builder| {
            (
                b.exclude,
                b.declared_only,
                b.redefinition_lookup_owner,
                b.redefinition_lookup_base,
                b.recorded_lookup_suppressed,
                b.identity_origin_unit,
                b.probing,
                b.widen,
                b.used_imports.clone(),
                b.query_imports.clone(),
                b.current_misses.clone(),
                b.root_misses.clone(),
            )
        };
        let before = context(b);
        let mut proof = ProviderCompleteness::default();
        let mut steps = 0;
        for (scope, expected) in [
            (complete_scope, true),
            (missing_scope, false),
            (complete_scope, true),
            (missing_scope, false),
        ] {
            assert_eq!(proof.scope(b, scope, &mut steps), expected);
            assert_eq!(context(b), before);
            assert!(proof.active.is_empty());
        }
        steps = crate::eval::MAX_STEPS;
        assert!(!proof.scope(b, complete_scope, &mut steps));
        assert_eq!(context(b), before);
        assert_eq!(steps, crate::eval::MAX_STEPS + 1);
    }
}

#[cfg(test)]
mod annotation_completeness_tests {
    use super::*;
    use crate::{json::ResolvedModel, model::Model};

    #[test]
    fn duplicate_loaded_identities_refuse_absence_until_repaired() {
        let mut model = Model::new();
        assert!(
            model
                .add_source("identities.kerml", "class A; class B; class C;")
                .diagnostics
                .is_empty()
        );
        let mut r = ResolvedModel::build(&model);
        let a = r.resolve_qualified("A").unwrap().0;
        let b = r.resolve_qualified("B").unwrap().0;
        let c = r.resolve_qualified("C").unwrap().0;
        let scope = *r.b.elem_scope.get(&a).unwrap();
        let mut proof = ProviderCompleteness::default();
        assert!(proof.scope(&mut r.b, scope, &mut 0));
        let original = r.b.elements[c].id;
        r.b.elements[c].id = r.b.elements[b].id;
        assert!(!proof.scope(&mut r.b, scope, &mut 0));
        r.b.elements[c].id = original;
        assert!(proof.scope(&mut r.b, scope, &mut 0));
    }

    #[test]
    fn warm_scope_proof_observes_annotation_retarget_and_repair() {
        let mut model = Model::new();
        let p = model.add_source(
            "annotation-lifecycle.kerml",
            "metaclass M; classifier A; classifier B; @M about B;",
        );
        assert!(p.diagnostics.is_empty(), "{:?}", p.diagnostics);
        let mut r = ResolvedModel::build(&model);
        let a = r.resolve_qualified("A").unwrap().0;
        let scope = *r.b.elem_scope.get(&a).unwrap();
        let rel =
            r.b.elements
                .iter()
                .position(|e| e.ty == "Annotation")
                .unwrap();
        let mut proof = ProviderCompleteness::default();
        assert!(proof.scope(&mut r.b, scope, &mut 0));
        assert_eq!(proof.known.get(&(scope, 0)), Some(&true));
        let before = Arc::clone(proof.annotations.as_ref().unwrap());
        let owner = before.carrier(&r.b, rel).unwrap().unwrap();
        let source_id = r.b.elements[owner].id;
        let target_id = r.b.elements[a].id;
        let original = r.b.elements[rel].props.clone();
        r.b.elements[rel].props.insert(
            "annotatedElement",
            serde_json::json!({"@id":target_id.to_string()}),
        );
        r.b.elements[rel]
            .props
            .insert("target", serde_json::json!([{"@id":target_id.to_string()}]));
        r.b.elements[rel].props.insert(
            "relatedElement",
            serde_json::json!([{"@id":source_id.to_string()}, {"@id":target_id.to_string()}]),
        );
        // A warm positive memo may not survive a same-length annotation mutation.
        assert!(!proof.scope(&mut r.b, scope, &mut 0));
        let after = proof.annotations.as_ref().unwrap();
        assert!(!Arc::ptr_eq(&before, after));
        assert!(!after.annotations_incomplete);
        assert!(after.metadata_annotation_targets.contains(&a));
        assert_eq!(proof.known.get(&(scope, 0)), Some(&false));
        r.b.elements[rel].props = original;
        let mut exhausted = crate::eval::MAX_STEPS;
        assert!(!proof.scope(&mut r.b, scope, &mut exhausted));
        assert!(
            !proof
                .annotations
                .as_ref()
                .is_some_and(|index| index.is_current(&r.b))
        );
        assert!(proof.scope(&mut r.b, scope, &mut 0));
        assert_eq!(proof.known.get(&(scope, 0)), Some(&true));
        assert!(
            !proof
                .annotations
                .as_ref()
                .unwrap()
                .metadata_annotation_targets
                .contains(&a)
        );
    }
}

#[cfg(test)]
mod annotation_budget_tests {
    use super::*;
    use crate::{json::ResolvedModel, model::Model};
    #[test]
    fn repeated_fresh_providers_share_annotation_topology_under_one_near_limit_budget() {
        let mut model = Model::new();
        let mut source = String::from("class Target;");
        for i in 0..5000 {
            source.push_str(&format!("class Padding{i};"));
        }
        let parsed = model.add_source("provider-cost.kerml", &source);
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let mut r = ResolvedModel::build(&model);
        let target = r.resolve_qualified("Target").unwrap().0;
        let scope = *r.b.elem_scope.get(&target).unwrap();
        assert!(r.b.elements.len() > 10_000);
        let mut cold = 0;
        assert!(ProviderCompleteness::default().scope(&mut r.b, scope, &mut cold));
        assert!(
            cold >= r.b.elements.len(),
            "cold construction remains charged"
        );
        let shared = r.b.stored_structure.as_ref().unwrap().clone();
        let reads = 500;
        let start = crate::eval::MAX_STEPS - reads * 8;
        let mut steps = start;
        for _ in 0..reads {
            // Mirrors parameter_context's new provider per argument-target query.
            assert!(ProviderCompleteness::default().scope(&mut r.b, scope, &mut steps));
            assert!(Arc::ptr_eq(&shared, r.b.stored_structure.as_ref().unwrap()));
        }
        assert!(
            steps - start <= reads * 8,
            "cached raw topology must not spend model size per call"
        );
        let mut exhausted = crate::eval::MAX_STEPS;
        assert!(!ProviderCompleteness::default().scope(&mut r.b, scope, &mut exhausted));
        assert!(ProviderCompleteness::default().scope(&mut r.b, scope, &mut 0));
    }
}
