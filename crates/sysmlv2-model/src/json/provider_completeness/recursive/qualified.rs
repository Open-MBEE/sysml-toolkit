//! Direct declaration paths witnessed from an already recorded endpoint.
use super::{Builder, ProviderCompleteness, StoredStructure, charge};
use crate::json::{Binding, LookupAccess, QualifiedName, semantic_ownership};
use crate::metaclass::conforms;
use std::{collections::HashMap, sync::Arc};

impl ProviderCompleteness {
    #[allow(clippy::too_many_arguments)]
    pub(super) fn direct_global_path(
        &mut self,
        b: &Builder,
        raw: &Arc<StoredStructure>,
        name: &QualifiedName,
        member: usize,
        unit: usize,
        depth: usize,
        steps: &mut usize,
    ) -> Option<()> {
        if !name.is_global
            || name.segments.is_empty()
            || depth.saturating_add(name.segments.len() - 1) > crate::json::MAX_RESOLUTION_DEPTH
        {
            return None;
        }
        // Walk recorded ownership backwards, not resolver alternatives. Each
        // qualifier must supply the exact direct binding that lookup visits
        // before aliases, imports, inheritance or effective names.
        let mut member = member;
        for (index, segment) in name.segments.iter().enumerate().rev() {
            if b.id_spelled_targets
                .contains_key(&(unit, segment.span.start, segment.span.end))
            {
                return None;
            }
            if index == 0 {
                return self.direct_root_alias(b, raw, &segment.value, member, steps);
            }
            charge(steps, segment.value.len().saturating_add(1))?;
            let relationship = b.elements.get(member)?.owning_relationship?;
            let owner =
                semantic_ownership::checked_relationship_carrier(b, raw, relationship, steps)??;
            if !matches!(
                b.elements.get(owner)?.ty,
                "Namespace" | "Package" | "LibraryPackage"
            ) {
                return None;
            }
            let scope = *b.elem_scope.get(&owner)?;
            let context = b.scopes.get(scope)?;
            if context.owner != Some(owner) {
                return None;
            }
            let sub_scope = b.elem_scope.get(&member).copied();
            if (conforms(b.elements[member].ty, "Namespace") && sub_scope.is_none())
                || sub_scope.is_some_and(|sub| {
                    b.scopes
                        .get(sub)
                        .is_none_or(|s| s.owner != Some(member) || s.parent != Some(scope))
                })
            {
                return None;
            }
            if let std::collections::hash_map::Entry::Vacant(entry) =
                self.recursive.qualified.entry(scope)
            {
                let memberships = crate::json::operations::namespaces::memberships_builder(
                    b,
                    raw,
                    owner,
                    steps,
                    "qualified recursive target",
                )
                .ok()?;
                let mut names: HashMap<String, Vec<Binding>> = HashMap::new();
                for m in memberships {
                    charge(steps, 1)?;
                    if !conforms(b.elements[m.relationship].ty, "OwningMembership") {
                        continue;
                    }
                    let visibility = match m.visibility {
                        "public" => LookupAccess::Public,
                        "protected" => LookupAccess::Protected,
                        "private" => LookupAccess::All,
                        _ => return None,
                    };
                    for key in ["declaredName", "declaredShortName"] {
                        if let Some(value) =
                            b.elements[m.member].props.get(key).filter(|v| !v.is_null())
                        {
                            let declared = value.as_str()?;
                            charge(steps, declared.len().saturating_add(1))?;
                            names.entry(declared.to_owned()).or_default().push(Binding {
                                elem: m.member,
                                sub_scope: b.elem_scope.get(&m.member).copied(),
                                visibility,
                            });
                        }
                    }
                }
                entry.insert(names);
            }
            let expected = self.recursive.qualified.get(&scope)?.get(&segment.value)?;
            let bindings = context.names.get(&segment.value)?;
            charge(steps, expected.len().saturating_add(bindings.len()))?;
            // Public-only groups have identical lookup under every caller
            // access level, including import all. Hidden collisions need a
            // separate origin/access certificate and remain qualified.
            if expected.is_empty()
                || expected != bindings
                || expected.iter().any(|binding| {
                    binding.elem != member
                        || binding.sub_scope != sub_scope
                        || binding.visibility != LookupAccess::Public
                })
            {
                return None;
            }
            member = owner;
        }
        None
    }
}
