//! Recursive lookup certificates for literal named package trees.
use super::{Builder, ProviderCompleteness};
use crate::json::{Binding, LookupAccess, structural_index::StoredStructure};
use crate::metaclass::conforms;
use std::{collections::HashMap, sync::Arc};

mod qualified;

type RootNames = (Arc<StoredStructure>, HashMap<String, Vec<usize>>);

#[derive(Default)]
pub(super) struct Proof {
    pub touched: bool,
    known: HashMap<(usize, usize, Option<bool>), bool>,
    // Raw declaration names only, never lookup outcomes. Revalidated against
    // current bindings on every use, and rebuilt after any element mutation.
    roots: Option<RootNames>,
    // Per-call raw owning declaration groups. Current bindings are still
    // compared on every path; no semantic input survives a top-level call.
    qualified: HashMap<usize, HashMap<String, Vec<Binding>>>,
}
fn charge(steps: &mut usize, n: usize) -> Option<()> {
    *steps = steps.saturating_add(n);
    (*steps <= crate::eval::MAX_STEPS).then_some(())
}
impl Proof {
    pub(super) fn charge_roots_drop(&self, steps: &mut usize) -> Option<()> {
        if let Some((_, names)) = &self.roots {
            charge(steps, names.capacity())?;
            for (name, members) in names {
                charge(steps, name.len().saturating_add(members.len()))?;
            }
        }
        Some(())
    }
    fn charge_qualified_drop(&self, steps: &mut usize) -> Option<()> {
        charge(steps, self.qualified.capacity())?;
        for names in self.qualified.values() {
            charge(steps, names.capacity())?;
            for (name, bindings) in names {
                charge(steps, name.len().saturating_add(bindings.len()))?;
            }
        }
        Some(())
    }
    pub(super) fn clear(&mut self, steps: &mut usize) -> bool {
        if charge(steps, self.known.capacity()).is_none() {
            return false;
        }
        if self.charge_qualified_drop(steps).is_none() {
            return false;
        }
        self.qualified.clear();
        self.known.clear();
        // Involvement stays sticky: an early failure may still depend on a
        // recursive resolver input even before that edge is visited again.
        true
    }
}
impl ProviderCompleteness {
    pub(super) fn recursive_import_domain(
        &mut self,
        b: &Builder,
        scope: usize,
        depth: usize,
        literal_package: bool,
        steps: &mut usize,
    ) -> Option<()> {
        let context = b.scopes.get(scope)?;
        let owner = context.owner?;
        // Package aliases were already checked against complete raw Memberships.
        // Other importing owners still need their own alias-domain certificate.
        if !literal_package && !context.aliases.is_empty() {
            return None;
        }
        let raw = Arc::clone(self.annotations.as_ref()?);
        if !raw.import_domains(b, steps)?.owner_complete(owner) {
            return None;
        }
        let cached = b.import_cache.get(scope)?.as_deref().map(Vec::as_slice);
        charge(
            steps,
            cached
                .map_or(0, |entries| entries.len())
                .saturating_add(context.imports.len())
                .saturating_add(context.member_imports.len()),
        )?;
        if cached.is_some_and(|entries| entries.len() != context.imports.len()) {
            return None;
        }
        let mut namespaces = HashMap::new();
        let mut members = HashMap::new();
        let mut caches = HashMap::new();
        for entry in &context.imports {
            if namespaces.insert(entry.relationship, entry).is_some() {
                return None;
            }
        }
        for entry in &context.member_imports {
            if members.insert(entry.relationship, entry).is_some() {
                return None;
            }
        }
        for entry in cached.unwrap_or(&[]) {
            if caches.insert(entry.relationship, entry).is_some() {
                return None;
            }
        }
        charge(steps, b.elements[owner].owned_relationships.len())?;
        for &relationship in &b.elements[owner].owned_relationships {
            if !literal_package
                && conforms(b.elements[relationship].ty, "Membership")
                && !conforms(b.elements[relationship].ty, "OwningMembership")
            {
                return None;
            }
            if !conforms(b.elements[relationship].ty, "Import") {
                continue;
            }
            let target = crate::json::import_memberships::checked_import_target(
                b,
                &raw,
                owner,
                relationship,
                steps,
            )?;
            let public = b.elements[relationship]
                .props
                .get("visibility")
                .and_then(|v| v.as_str())
                == Some("public");
            let mut mirrored = None;
            if target.membership.is_some() {
                let member = members.remove(&relationship)?;
                if member.is_import_all != target.all
                    || member.is_public != public
                    || !member.filters.is_empty()
                {
                    return None;
                }
                if b.elements[target.element].owning_relationship != target.membership {
                    return None;
                }
                if !target.recursive {
                    self.direct_global_path(
                        b,
                        &raw,
                        &member.target,
                        target.element,
                        b.unit_of_elem(relationship),
                        depth + 1,
                        steps,
                    )?;
                }
                mirrored = Some(member);
            }
            if target.membership.is_none() || target.recursive {
                let entry = namespaces.remove(&relationship)?;
                if let Some(member) = mirrored {
                    for segment in member.target.segments.iter().chain(&entry.target.segments) {
                        charge(steps, segment.value.len().saturating_add(1))?;
                    }
                    if member.target != entry.target {
                        return None;
                    }
                }
                let cache = caches.remove(&relationship);
                let target_scope = *b.elem_scope.get(&target.element)?;
                if b.scopes.get(target_scope)?.owner != Some(target.element)
                    || entry.recursive != target.recursive
                    || entry.is_import_all != target.all
                    || entry.is_public != public
                    || !entry.filters.is_empty()
                    || (cached.is_some() && cache.is_none())
                    || cache.is_some_and(|cache| {
                        cache.scope != target_scope
                            || cache.recursive != target.recursive
                            || cache.is_import_all != target.all
                            || cache.is_public != public
                            || !cache.filters.is_empty()
                    })
                {
                    return None;
                }
            }
        }
        (namespaces.is_empty() && members.is_empty() && caches.is_empty()).then_some(())
    }

    pub(super) fn literal_namespace_import(
        &mut self,
        b: &Builder,
        scope: usize,
        index: usize,
        depth: usize,
        steps: &mut usize,
    ) -> Option<(usize, bool)> {
        self.recursive.touched = true;
        let context = b.scopes.get(scope)?;
        let entry = context.imports.get(index)?;
        let owner = context.owner?;
        let raw = Arc::clone(self.annotations.as_ref()?);
        let target = crate::json::import_memberships::checked_import_target(
            b,
            &raw,
            owner,
            entry.relationship,
            steps,
        )?;
        let public = b.elements[entry.relationship]
            .props
            .get("visibility")
            .and_then(|v| v.as_str())
            == Some("public");
        if target.recursive != entry.recursive
            || target.all != entry.is_import_all
            || public != entry.is_public
        {
            return None;
        }
        // Namespace cache construction starts resolution at zero. The mirrored
        // MembershipImport additionally resolves its selected member at the
        // caller's depth + 1, which is the stricter bound.
        let target_depth = if target.membership.is_some() {
            depth + 1
        } else {
            0
        };
        self.direct_global_path(
            b,
            &raw,
            &entry.target,
            target.element,
            b.unit_of_elem(entry.relationship),
            target_depth,
            steps,
        )?;
        if target
            .membership
            .is_some_and(|m| b.elements[target.element].owning_relationship != Some(m))
        {
            return None;
        }
        let target_scope = *b.elem_scope.get(&target.element)?;
        if b.scopes.get(target_scope)?.owner != Some(target.element) {
            return None;
        }
        // The whole entry/mirror/cache domain has already been checked once.
        // Cold targets need no cache: all admitted target paths terminate in
        // directly witnessed global bindings without invoking name resolution.
        Some((target_scope, target.all))
    }

    pub(super) fn recursive_scope(
        &mut self,
        b: &mut Builder,
        scope: usize,
        depth: usize,
        all: bool,
        steps: &mut usize,
    ) -> bool {
        self.package_scope(b, scope, depth, Some(all), steps)
    }

    pub(super) fn package_scope(
        &mut self,
        b: &mut Builder,
        scope: usize,
        depth: usize,
        recursive: Option<bool>,
        steps: &mut usize,
    ) -> bool {
        self.recursive.touched = true;
        if charge(steps, 1).is_none() || depth > crate::json::MAX_RESOLUTION_DEPTH {
            return false;
        }
        let key = (scope, depth, recursive);
        // A completed nonrecursive visit must not hide an active recursive
        // route to the same scope. Cyclic providers need their own proof.
        if self.active.contains(&scope) {
            return false;
        }
        if let Some(&result) = self.recursive.known.get(&key) {
            return result;
        }
        if !self.active.insert(scope) {
            return false;
        }
        let complete = self
            .recursive_children(b, scope, depth, recursive.unwrap_or(false), steps)
            .is_some_and(|children| {
                self.dependencies(b, scope, depth, true, steps)
                    .is_some_and(|dependencies| {
                        self.complete_dependencies(b, dependencies, depth, steps)
                    })
                    && recursive.is_none_or(|all| {
                        children
                            .into_iter()
                            .all(|child| self.recursive_scope(b, child, depth + 1, all, steps))
                    })
            });
        self.active.remove(&scope);
        if *steps <= crate::eval::MAX_STEPS && (complete || !self.transient_incomplete) {
            self.recursive.known.insert(key, complete);
        }
        complete
    }

    fn recursive_children(
        &mut self,
        b: &Builder,
        scope: usize,
        depth: usize,
        all: bool,
        steps: &mut usize,
    ) -> Option<Vec<usize>> {
        let context = b.scopes.get(scope)?;
        let owner = context.owner?;
        if !matches!(
            b.elements.get(owner)?.ty,
            "Namespace" | "Package" | "LibraryPackage"
        ) || b.elem_scope.get(&owner) != Some(&scope)
            || !context.filters.is_empty()
            || !context.bases.is_empty()
            || !context.implied_bases.is_empty()
            || !context.chain_bases.is_empty()
            || !context.implied_ends.is_empty()
            || context.effective_names.iter().next().is_some()
        {
            return None;
        }
        let raw = Arc::clone(self.annotations.as_ref()?);
        if !raw.import_domains(b, steps)?.owner_complete(owner) {
            return None;
        }
        let members = crate::json::operations::namespaces::memberships_builder(
            b,
            &raw,
            owner,
            steps,
            "recursive package lookup",
        )
        .ok()?;
        charge(steps, b.elements[owner].owned_relationships.len())?;
        if b.elements[owner].owned_relationships.iter().any(|&r| {
            conforms(b.elements[r].ty, "Specialization")
                || b.elements[r].ty == "ElementFilterMembership"
        }) {
            return None;
        }
        let mut expected: HashMap<String, Vec<Binding>> = HashMap::new();
        let mut aliases = HashMap::new();
        let mut children = Vec::new();
        for m in members {
            charge(steps, 1)?;
            if !conforms(b.elements[m.relationship].ty, "OwningMembership") {
                if b.elements[m.relationship].ty != "Membership" {
                    return None;
                }
                for key in ["memberName", "memberShortName"] {
                    if let Some(value) = b.elements[m.relationship]
                        .props
                        .get(key)
                        .filter(|v| !v.is_null())
                    {
                        let name = value.as_str()?;
                        charge(steps, name.len())?;
                        aliases.insert((m.relationship, name.to_owned()), m.member);
                    }
                }
                continue;
            }
            let element = &b.elements[m.member];
            let sub_scope = b.elem_scope.get(&m.member).copied();
            let namespace = conforms(element.ty, "Namespace");
            if namespace {
                if !matches!(element.ty, "Namespace" | "Package" | "LibraryPackage") {
                    return None;
                }
                let sub = sub_scope?;
                if b.scopes.get(sub)?.owner != Some(m.member) || b.scopes[sub].parent != Some(scope)
                {
                    return None;
                }
                if all || m.visibility == "public" {
                    children.push(sub);
                }
            } else if sub_scope.is_some() {
                return None;
            }
            let visibility = match m.visibility {
                "public" => LookupAccess::Public,
                "protected" => LookupAccess::Protected,
                "private" => LookupAccess::All,
                _ => return None,
            };
            let mut named = false;
            for key in ["declaredName", "declaredShortName"] {
                if let Some(value) = element.props.get(key).filter(|v| !v.is_null()) {
                    let name = value.as_str()?;
                    charge(steps, name.len())?;
                    named = true;
                    expected.entry(name.to_owned()).or_default().push(Binding {
                        elem: m.member,
                        sub_scope,
                        visibility,
                    });
                }
            }
            if namespace && !named {
                return None;
            }
        }
        // Exact bags, including duplicate names: no omitted child or extra
        // namespace-valued alias can silently change recursive traversal.
        for (name, bindings) in context.names.iter() {
            charge(steps, name.len().saturating_add(bindings.len()))?;
            let expected = expected.remove(name)?;
            if expected != bindings {
                return None;
            }
        }
        if !expected.is_empty() {
            return None;
        }
        charge(steps, context.aliases.len())?;
        for (alias_index, (name, qn, relationship)) in context.aliases.iter().enumerate() {
            charge(steps, name.len())?;
            let member = aliases.remove(&(*relationship, name.clone()))?;
            self.direct_global_path(
                b,
                &raw,
                qn,
                member,
                b.alias_origins
                    .get(&(scope, alias_index))
                    .copied()
                    .unwrap_or_else(|| b.unit_of_scope(scope)),
                depth + 1,
                steps,
            )?;
        }
        if !aliases.is_empty() {
            return None;
        }
        Some(children)
    }

    fn direct_root_alias(
        &mut self,
        b: &Builder,
        raw: &Arc<StoredStructure>,
        name: &str,
        member: usize,
        steps: &mut usize,
    ) -> Option<()> {
        if !self
            .recursive
            .roots
            .as_ref()
            .is_some_and(|(old, _)| old.is_current(b))
        {
            self.recursive.charge_roots_drop(steps)?;
            charge(steps, b.elements.len())?;
            let mut names: HashMap<String, Vec<usize>> = HashMap::new();
            for (root, element) in b.elements.iter().enumerate() {
                if element.ty != "Namespace" || element.owning_relationship.is_some() {
                    continue;
                }
                for m in crate::json::operations::namespaces::memberships_builder(
                    b,
                    raw,
                    root,
                    steps,
                    "recursive alias root names",
                )
                .ok()?
                {
                    if !conforms(b.elements[m.relationship].ty, "OwningMembership") {
                        continue;
                    }
                    for key in ["declaredName", "declaredShortName"] {
                        if let Some(value) =
                            b.elements[m.member].props.get(key).filter(|v| !v.is_null())
                        {
                            let name = value.as_str()?;
                            charge(steps, name.len())?;
                            names.entry(name.to_owned()).or_default().push(m.member);
                        }
                    }
                }
            }
            self.recursive.roots = Some((Arc::clone(raw), names));
        }
        charge(steps, name.len())?;
        if conforms(b.elements[member].ty, "Namespace") && b.elem_scope.get(&member).is_none() {
            return None;
        }
        let expected = self.recursive.roots.as_ref()?.1.get(name)?;
        let bindings = b.scopes[0].names.get(name)?;
        charge(steps, expected.len().saturating_add(bindings.len()))?;
        if expected.is_empty()
            || expected.len() != bindings.len()
            || expected.iter().any(|&e| e != member)
            || bindings.iter().any(|binding| {
                binding.elem != member
                    || binding.sub_scope != b.elem_scope.get(&member).copied()
                    || binding.sub_scope.is_some_and(|s| {
                        b.scopes
                            .get(s)
                            .is_none_or(|scope| scope.owner != Some(member))
                    })
            })
        {
            return None;
        }
        Some(())
    }
}
