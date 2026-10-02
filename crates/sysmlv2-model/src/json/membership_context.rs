//! Contextual inheritance for import-operation Membership projections.
use super::{Builder, InheritedBindings, LookupAccess};
use std::collections::{HashMap, HashSet};
use std::sync::Arc;

/// Ordered semantic identities; no textual scope is fabricated for leaf Types.
#[derive(Default)]
pub(super) struct MembershipProjection {
    pub(super) membership_order: Vec<usize>,
    pub(super) truncated: bool,
    pub(super) incomplete: bool,
    pub(super) implicit_redefinitions: Vec<(usize, usize)>,
}

const MAX_CONTEXT_DEPTH: usize = 128;

#[derive(Clone, Default)]
struct Guards {
    namespaces: HashMap<usize, bool>,
    types: HashMap<usize, bool>,
}
impl Guards {
    fn matches(&self, namespaces: &[usize], types: &[usize]) -> bool {
        self.namespaces
            .iter()
            .all(|(e, excluded)| namespaces.contains(e) == *excluded)
            && self
                .types
                .iter()
                .all(|(e, excluded)| types.contains(e) == *excluded)
    }
}
struct Tracking {
    namespaces: HashSet<usize>,
    types: HashSet<usize>,
    family: usize,
    guards: Guards,
}
#[derive(Clone)]
struct Complete {
    guards: Arc<Guards>,
    value: Arc<MembershipProjection>,
}
pub(super) struct ImportProjection {
    pub(super) blocked: Vec<usize>,
    guards: Arc<Guards>,
}
/// Query-local: graph mutation cannot invalidate a proof between public calls.
#[derive(Default)]
pub(super) struct MembershipContext {
    known: HashMap<(usize, bool), Vec<Complete>>,
    tracking: Vec<Tracking>,
    family: usize,
    pub(super) steps: usize,
}
impl MembershipContext {
    pub(super) fn begin_namespace(&mut self, excluded: &[usize]) {
        self.tracking.push(Tracking {
            namespaces: excluded.iter().copied().collect(),
            types: HashSet::new(),
            family: 0,
            guards: Guards::default(),
        });
    }
    pub(super) fn finish_namespace(&mut self, blocked: Vec<usize>) -> ImportProjection {
        let tracking = self.tracking.pop().expect("balanced namespace projection");
        debug_assert_eq!(tracking.family, 0);
        ImportProjection {
            blocked,
            guards: Arc::new(tracking.guards),
        }
    }
    pub(super) fn reuse_namespace(&mut self, value: &ImportProjection, excluded: &[usize]) -> bool {
        self.charge(
            value
                .guards
                .namespaces
                .len()
                .saturating_mul(excluded.len().saturating_add(1)),
        ) && value.guards.matches(excluded, &[])
            && self.replay(0, &value.guards)
    }
    pub(super) fn charge(&mut self, count: usize) -> bool {
        self.steps = self.steps.saturating_add(count);
        self.steps <= crate::eval::MAX_STEPS
    }
    pub(super) fn new_type_family(&mut self) -> usize {
        self.family += 1;
        self.family
    }
    /// Namespace exclusions continue through imports and inheritance. An
    /// exclusion introduced inside a tracked operation is constant for that
    /// operation, not a dependency on its caller's original exclusion set.
    pub(super) fn namespace_test(&mut self, namespace: usize, excluded: bool) -> bool {
        if !self.charge(self.tracking.len()) {
            return false;
        }
        for tracking in &mut self.tracking {
            if !excluded || tracking.namespaces.contains(&namespace) {
                tracking.guards.namespaces.insert(namespace, excluded);
            }
        }
        true
    }
    fn type_test(&mut self, family: usize, ty: usize, excluded: bool) -> bool {
        if !self.charge(self.tracking.len()) {
            return false;
        }
        for tracking in &mut self.tracking {
            // visibleMemberships starts inheritedMemberships with fresh Type
            // exclusions. Its proof must not constrain an outer heritage walk.
            if tracking.family == family && (!excluded || tracking.types.contains(&ty)) {
                tracking.guards.types.insert(ty, excluded);
            }
        }
        true
    }
    fn replay(&mut self, family: usize, guards: &Guards) -> bool {
        if !self.charge(guards.namespaces.len() + guards.types.len()) {
            return false;
        }
        for (&e, &excluded) in &guards.namespaces {
            if !self.namespace_test(e, excluded) {
                return false;
            }
        }
        for (&e, &excluded) in &guards.types {
            if !self.type_test(family, e, excluded) {
                return false;
            }
        }
        true
    }
}

fn incomplete() -> Arc<MembershipProjection> {
    Arc::new(MembershipProjection {
        truncated: true,
        incomplete: true,
        ..Default::default()
    })
}

impl Builder {
    /// Actual candidate gathering precedes redefinition removal. Reusing an
    /// already reduced global list cannot recover a candidate whose blocker is
    /// excluded in this import operation's namespace context.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn contextual_inherited_bindings(
        &mut self,
        element: usize,
        include_implied: bool,
        excluded_namespaces: &[usize],
        excluded_types: &[usize],
        family: usize,
        context: &mut MembershipContext,
        depth: usize,
    ) -> Arc<MembershipProjection> {
        if depth > MAX_CONTEXT_DEPTH
            || context.tracking.len() >= MAX_CONTEXT_DEPTH
            || !context.charge(1)
        {
            return incomplete();
        }
        let variants = context
            .known
            .get(&(element, include_implied))
            .cloned()
            .unwrap_or_default();
        let mut hit = None;
        for candidate in variants {
            if !context.charge(
                candidate
                    .guards
                    .namespaces
                    .len()
                    .saturating_mul(excluded_namespaces.len().saturating_add(1))
                    + candidate
                        .guards
                        .types
                        .len()
                        .saturating_mul(excluded_types.len().saturating_add(1)),
            ) {
                return incomplete();
            }
            if candidate
                .guards
                .matches(excluded_namespaces, excluded_types)
            {
                hit = Some(candidate);
                break;
            }
        }
        if let Some(hit) = hit {
            if !context.replay(family, &hit.guards)
                || !context.charge(hit.value.membership_order.len())
            {
                return incomplete();
            }
            return hit.value;
        }
        context.tracking.push(Tracking {
            namespaces: excluded_namespaces.iter().copied().collect(),
            types: excluded_types.iter().copied().collect(),
            family,
            guards: Guards::default(),
        });
        let value = self.contextual_inherited_uncached(
            element,
            include_implied,
            excluded_namespaces,
            excluded_types,
            family,
            context,
            depth,
        );
        let tracking = context
            .tracking
            .pop()
            .expect("balanced contextual inheritance");
        let value = Arc::new(value);
        if !value.incomplete && !value.truncated && context.steps <= crate::eval::MAX_STEPS {
            // A bounded variant count limits retained memory in highly cyclic
            // models. Uncached variants still compute with the shared budget.
            let variants = context.known.entry((element, include_implied)).or_default();
            if variants.len() < 8 {
                variants.push(Complete {
                    guards: Arc::new(tracking.guards),
                    value: Arc::clone(&value),
                });
            }
        }
        value
    }

    #[allow(clippy::too_many_arguments)]
    fn contextual_inherited_uncached(
        &mut self,
        element: usize,
        include_implied: bool,
        excluded_namespaces: &[usize],
        excluded_types: &[usize],
        family: usize,
        context: &mut MembershipContext,
        depth: usize,
    ) -> MembershipProjection {
        let mut types = excluded_types.to_vec();
        if !types.contains(&element) {
            types.push(element);
        }
        let mut result = MembershipProjection::default();
        let scope = self.elem_scope.get(&element).copied();
        // Preserve known positive bases but distinguish an unresolved authored
        // endpoint from a proven complete absence of other supertypes.
        let relationships = self.elements[element].owned_relationships.clone();
        if !context.charge(relationships.len()) {
            result.truncated = true;
            result.incomplete = true;
            return result;
        }
        for relationship in relationships {
            let relation = &self.elements[relationship];
            if crate::metaclass::conforms(relation.ty, "Specialization")
                && (include_implied
                    || relation
                        .props
                        .get("isImplied")
                        .and_then(|value| value.as_bool())
                        != Some(true))
            {
                let id = super::implied::specialization_target(relation);
                let target = id.and_then(|id| self.element_index_of_uuid(id));
                if target.is_none_or(|target| {
                    !crate::metaclass::conforms(self.elements[target].ty, "Type")
                }) {
                    result.incomplete = true;
                }
            }
        }
        if self.metadata_associations_incomplete
            || scope.is_some_and(|scope| !self.scopes[scope].chain_bases.is_empty())
            || self
                .metadata_of
                .get(&element)
                .is_some_and(|values| !values.is_empty())
        {
            result.incomplete = true;
        }
        let bases = if let Some(scope) = scope {
            let (mut bases, explicit) = self.base_scopes_split(scope);
            if !include_implied {
                bases.truncate(explicit);
            }
            let mut identities = Vec::new();
            for base in bases {
                if let Some(owner) = self.scopes[base].owner {
                    identities.push(owner);
                } else {
                    result.incomplete = true;
                }
            }
            identities
        } else {
            match self.semantic_inheritance_bases(element, include_implied, &mut context.steps) {
                Some(bases) => bases,
                None => {
                    result.incomplete = true;
                    result.truncated = context.steps > crate::eval::MAX_STEPS;
                    return result;
                }
            }
        };
        if !context.charge(bases.len()) {
            result.truncated = true;
            result.incomplete = true;
            return result;
        }
        for base in bases {
            let excluded = types.contains(&base);
            if !context.type_test(family, base, excluded) {
                result.incomplete = true;
                result.truncated = true;
                break;
            }
            if excluded {
                continue;
            }
            // nonPrivateMemberships: public own/imported, protected
            // own/imported, then already reduced inherited memberships.
            for access in [LookupAccess::Public, LookupAccess::Protected] {
                let own = self.contextual_own_memberships(base, access, context);
                Self::append_contextual_bindings(&mut result, &own);
                if context.steps > crate::eval::MAX_STEPS {
                    break;
                }
                let Some(base_scope) = self.elem_scope.get(&base).copied() else {
                    // Semantic Type identity exists independently of a textual
                    // declaration scope. No synthetic scopes are allocated.
                    continue;
                };
                let mut excluded = excluded_namespaces.to_vec();
                if !excluded.contains(&base_scope) {
                    excluded.push(base_scope);
                }
                let mut seen = HashMap::new();
                let mut imported = InheritedBindings::default();
                let mut order = Vec::new();
                if self
                    .collect_import_edges(
                        base_scope,
                        access,
                        include_implied,
                        &[],
                        &mut excluded,
                        &mut seen,
                        &mut imported,
                        &mut order,
                        0,
                        false,
                        context,
                    )
                    .is_none()
                {
                    imported.incomplete = true;
                }
                let imported = MembershipProjection {
                    membership_order: order,
                    truncated: imported.truncated,
                    incomplete: imported.incomplete,
                    implicit_redefinitions: Vec::new(),
                };
                Self::append_contextual_bindings(&mut result, &imported);
            }
            if context.steps > crate::eval::MAX_STEPS {
                result.truncated = true;
                result.incomplete = true;
                break;
            }
            let inherited = self.contextual_inherited_bindings(
                base,
                include_implied,
                excluded_namespaces,
                &types,
                family,
                context,
                depth + 1,
            );
            Self::append_contextual_bindings(&mut result, &inherited);
        }
        self.reduce_membership_projection(
            Some(element),
            include_implied,
            result,
            Some(&mut context.steps),
        )
    }

    fn append_contextual_bindings(out: &mut MembershipProjection, source: &MembershipProjection) {
        out.membership_order
            .extend(source.membership_order.iter().copied());
        out.truncated |= source.truncated;
        out.incomplete |= source.incomplete;
    }

    fn contextual_own_memberships(
        &mut self,
        element: usize,
        access: LookupAccess,
        context: &mut MembershipContext,
    ) -> MembershipProjection {
        let mut result = MembershipProjection::default();
        let scope = self.elem_scope.get(&element).copied();
        let mut count = self.elements[element].owned_relationships.len();
        if let Some(scope) = scope {
            count += self.scopes[scope]
                .names
                .values()
                .map(|bindings| bindings.len())
                .sum::<usize>()
                + self.scopes[scope]
                    .effective_names
                    .values()
                    .map(|bindings| bindings.len())
                    .sum::<usize>();
        }
        if !context.charge(count) {
            result.truncated = true;
            result.incomplete = true;
            return result;
        }
        let mut elements = self.owned_member_elems(element, false);
        if let Some(scope) = scope {
            for names in [
                &self.scopes[scope].names,
                &self.scopes[scope].effective_names,
            ] {
                elements.extend(
                    names
                        .values()
                        .flatten()
                        .filter(|binding| access.admits(binding.visibility))
                        .map(|binding| binding.elem),
                );
            }
        }
        elements.sort_unstable();
        elements.dedup();
        for member in elements {
            if let Some(membership) = self.elements[member].owning_relationship {
                if self.import_admitted(membership, access) {
                    result.membership_order.push(membership);
                }
            }
        }
        if let Some(scope) = scope {
            self.scope_alias_rels(scope, access, &[], &mut result.membership_order);
        }
        result.membership_order.sort_unstable();
        result.membership_order.dedup();
        result
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{json::ResolvedModel, model::Model};
    #[test]
    fn excluded_blocker_is_filtered_before_redefinition_reduction() {
        let mut m = Model::new();
        let u=m.add_source("context.sysml", "part def A {part x;} part def P :> A {part y redefines A::x; public import D::*;} part def C {public import P::*;} part def D :> A,C;");
        assert!(u.diagnostics.is_empty(), "{:?}", u.diagnostics);
        let mut r = ResolvedModel::build(&m);
        let d = r.resolve_qualified("D").unwrap().0;
        let p = r.resolve_qualified("P").unwrap().0;
        let x = r.resolve_qualified("A::x").unwrap().0;
        let y = r.resolve_qualified("P::y").unwrap().0;
        let p_scope = *r.b.elem_scope.get(&p).unwrap();
        r.b.ensure_positional_redefinitions();
        let mut context = MembershipContext::default();
        for excluded in [vec![], vec![p_scope], vec![], vec![p_scope]] {
            let family = context.new_type_family();
            let result =
                r.b.contextual_inherited_bindings(d, true, &excluded, &[], family, &mut context, 0);
            let actual: Vec<_> = result
                .membership_order
                .iter()
                .filter_map(|&m| r.b.stored_membership_member(m))
                .collect();
            assert_eq!(
                actual,
                if excluded.is_empty() {
                    vec![y]
                } else {
                    vec![x]
                }
            );
            assert!(!result.truncated);
            assert!(context.tracking.is_empty());
        }
    }
    #[test]
    fn memo_guards_distinguish_external_from_internal_exclusions() {
        let mut c = MembershipContext::default();
        c.begin_namespace(&[1]);
        c.namespace_test(1, true); // caller-dependent
        c.namespace_test(2, true); // introduced by this traversal
        c.namespace_test(3, false);
        let result = c.finish_namespace(vec![1]);
        assert!(c.reuse_namespace(&result, &[1]));
        assert!(c.reuse_namespace(&result, &[1, 2, 9]));
        assert!(!c.reuse_namespace(&result, &[]));
        assert!(!c.reuse_namespace(&result, &[1, 3]));
        assert!(c.tracking.is_empty());
    }
    #[test]
    fn namespace_boundaries_reset_type_exclusion_dependencies() {
        let mut c = MembershipContext::default();
        let outer = c.new_type_family();
        let inner = c.new_type_family();
        c.tracking.push(Tracking {
            namespaces: HashSet::new(),
            types: HashSet::from([1]),
            family: outer,
            guards: Guards::default(),
        });
        c.type_test(inner, 1, false);
        assert!(c.tracking[0].guards.types.is_empty());
        c.type_test(outer, 1, true);
        assert_eq!(c.tracking[0].guards.types.get(&1), Some(&true));
    }
    #[test]
    fn exhausted_context_does_not_cache_a_false_empty_result() {
        let mut m = Model::new();
        m.add_source(
            "budget.kerml",
            "classifier A {feature x;} classifier D specializes A;",
        );
        let mut r = ResolvedModel::build(&m);
        let d = r.resolve_qualified("D").unwrap().0;
        r.b.ensure_positional_redefinitions();
        let mut c = MembershipContext {
            steps: crate::eval::MAX_STEPS - 1,
            ..Default::default()
        };
        let family = c.new_type_family();
        let result =
            r.b.contextual_inherited_bindings(d, true, &[], &[], family, &mut c, 0);
        assert!(result.truncated);
        assert!(c.tracking.is_empty());
        assert!(!c.known.contains_key(&(d, true)));
        c.steps = 0;
        let result =
            r.b.contextual_inherited_bindings(d, true, &[], &[], family, &mut c, 0);
        assert!(!result.truncated);
        assert_eq!(result.membership_order.len(), 1);
    }
}
