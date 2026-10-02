//! Compatibility exposure projection using import Membership identities.
use super::{
    Builder, ElementRef, InheritedBindings, LookupAccess, LookupResult, MembershipContext,
    ResolvedModel,
};
use std::collections::{HashMap, HashSet};

impl ResolvedModel {
    /// Elements contributed by the view's owned `expose` relationships, in
    /// relationship/import discovery order, deduplicated after Membership
    /// projection. Ordinary imports can resolve exposure names but do not
    /// themselves expose elements. Owned, imported, and inherited view conditions apply.
    ///
    /// This retains the compatibility filter policy: an unknown condition
    /// admits the element. Imported-membership completeness and normative
    /// metadata-witness evaluation remain qualified. Inherited contributions are
    /// reduced within each operation's namespace/type exclusion context. The
    /// scoped base adapter retains compatibility lookup, chain, and metadata
    /// behavior; it is not a complete identity-based supertypes proof. This is not an exact
    /// `includeAsExposed` conformance certificate.
    pub fn view_exposed_elements(&mut self, view: ElementRef) -> Vec<ElementRef> {
        let Some(&scope) = self.b.elem_scope.get(&view.0) else {
            return Vec::new();
        };
        if self.b.semantic_ready {
            self.b.ensure_positional_redefinitions();
        }
        let mut context = MembershipContext::default();
        let filters = self.b.exposure_condition_ids(scope, &mut context);
        let memberships = self.b.exposure_memberships(view.0, scope, &mut context);
        let mut emitted = HashSet::new();
        memberships
            .into_iter()
            .filter_map(|membership| {
                let element = self.b.stored_membership_member(membership)?;
                if !emitted.insert(element) {
                    return None;
                }
                self.b
                    .import_filter_set_admits(&filters, element)
                    .then_some(ElementRef(element))
            })
            .collect()
    }
}

impl Builder {
    /// The scope already indexes local filter ASTs. Imported and inherited
    /// conditions are selected through actual surviving ElementFilterMembership
    /// identities,
    /// not through an unfiltered walk of every ancestor's filter list.
    fn exposure_condition_ids(
        &mut self,
        scope: usize,
        context: &mut MembershipContext,
    ) -> Vec<usize> {
        // Every supported condition is indexed here, including imported and
        // inherited declarations. No condition projection is needed if the
        // entire model has no filter expression.
        if self.filter_exprs.is_empty() {
            return Vec::new();
        }
        let mut filters = self.scopes[scope].filters.clone();
        let inherited = self.inherited_bindings(scope, true);
        let mut imported = InheritedBindings::default();
        let imported_order = self.imported_bindings_with_context(
            scope,
            true,
            LookupAccess::All,
            &mut imported,
            context,
        );
        let mut wanted = HashSet::new();
        let mut scopes = Vec::new();
        let mut seen_scopes = HashSet::new();
        for &membership in inherited.membership_order.iter().chain(&imported_order) {
            if !crate::metaclass::conforms(self.elements[membership].ty, "ElementFilterMembership")
            {
                continue;
            }
            wanted.insert(membership);
            let owner = self.elements[membership]
                .props
                .get("owningRelatedElement")
                .and_then(|value| value.as_reference())
                .and_then(|id| self.element_index_of_uuid(id));
            if let Some(declaration_scope) =
                owner.and_then(|owner| self.elem_scope.get(&owner).copied())
            {
                if seen_scopes.insert(declaration_scope) {
                    scopes.push(declaration_scope);
                }
            }
        }
        for declaration_scope in scopes {
            filters.extend(
                self.scopes[declaration_scope]
                    .filters
                    .iter()
                    .copied()
                    .filter(|&id| wanted.contains(&self.filter_exprs[id].0)),
            );
        }
        let mut seen_filters = HashSet::new();
        filters.retain(|id| seen_filters.insert(*id));
        filters
    }

    /// Project each Expose's import operation before final element dedup.
    /// A filtered expose's anonymous FilterPackage is represented in the
    /// resolution indexes by the original target plus its recorded filters.
    fn exposure_memberships(
        &mut self,
        view: usize,
        scope: usize,
        context: &mut MembershipContext,
    ) -> Vec<usize> {
        let members = self.scopes[scope].member_imports.clone();
        let namespaces = self.import_scopes(scope);
        let member_by_rel: HashMap<_, _> = members
            .iter()
            .enumerate()
            .map(|(index, entry)| (entry.relationship, index))
            .collect();
        let namespace_by_rel: HashMap<_, _> = namespaces
            .iter()
            .enumerate()
            .map(|(index, entry)| (entry.relationship, index))
            .collect();
        let relationships = self.elements[view].owned_relationships.to_vec();
        let mut order = Vec::new();
        let mut out = InheritedBindings::default();
        // This memo's key includes access, recursion, and the filter path.
        // Sharing it avoids diamond expansion without conflating filtered paths.
        let mut seen = HashMap::new();
        // Expose.importedMemberships starts with the empty exclusion set.
        // collect_import_scope adds each visited namespace to break cycles.
        let mut excluded = Vec::new();
        for relationship in relationships {
            if !crate::metaclass::conforms(self.elements[relationship].ty, "Expose") {
                continue;
            }
            if let Some(&index) = member_by_rel.get(&relationship) {
                let entry = &members[index];
                // A plain Expose is import-all. A bracket wrapper owns an
                // ordinary, non-import-all inner import (FilterPackageImport).
                let all = entry.filters.is_empty();
                let origin = self.set_identity_origin(relationship);
                let resolved = self.resolve_result(scope, &entry.target, 0, all);
                self.identity_origin_unit = origin;
                if let LookupResult::Found(element, _, membership) = resolved {
                    if self.import_filter_set_admits(&entry.filters, element) {
                        if let Some(membership) =
                            membership.or(self.elements[element].owning_relationship)
                        {
                            order.push(membership);
                        }
                    }
                }
            }
            if let Some(&index) = namespace_by_rel.get(&relationship) {
                let entry = &namespaces[index];
                let access = if entry.filters.is_empty() {
                    LookupAccess::All
                } else {
                    LookupAccess::Public
                };
                // View conditions apply after each import operation; they must
                // not prevent descent into a container whose child qualifies.
                let chain = [(scope, entry.filters.clone())];
                self.collect_import_scope(
                    &mut excluded,
                    entry.scope,
                    access,
                    entry.recursive,
                    true,
                    &chain,
                    &mut seen,
                    &mut out,
                    &mut order,
                    0,
                    context,
                );
            }
        }
        // Do not Namespace::importedMemberships-prune this operation result:
        // Expose.importedMemberships is a different normative boundary.
        order
    }
}
