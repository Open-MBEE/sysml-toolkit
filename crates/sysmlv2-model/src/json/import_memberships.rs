//! Membership identity and name/type distinguishability without semantic lookup.

use super::Builder;
use crate::metaclass::conforms;
use std::collections::{HashMap, HashSet};

/// Raw Import endpoint evidence shared by namespace operations and Type
/// membership providers. A MembershipImport points to two distinct identities:
/// its selected Membership and that Membership's imported member Element.
pub(super) struct ImportTarget {
    pub element: usize,
    pub membership: Option<usize>,
    pub recursive: bool,
    pub all: bool,
}
pub(super) fn checked_import_target(
    b: &Builder,
    raw: &super::structural_index::StoredStructure,
    owner: usize,
    relationship: usize,
    steps: &mut usize,
) -> Option<ImportTarget> {
    fn charge(steps: &mut usize, n: usize) -> Option<()> {
        *steps = steps.saturating_add(n);
        (*steps <= crate::eval::MAX_STEPS).then_some(())
    }
    charge(steps, 12)?;
    if !raw.import_domains(b, steps)?.owner_complete(owner)
        || super::semantic_ownership::checked_relationship_carrier(b, raw, relationship, steps)?
            != Some(owner)
    {
        return None;
    }
    let relation = b.elements.get(relationship)?;
    let (key, kind) = match relation.ty {
        "MembershipImport" => ("importedMembership", "Membership"),
        "NamespaceImport" => ("importedNamespace", "Namespace"),
        _ => return None,
    };
    if relation
        .props
        .get("visibility")
        .is_some_and(|v| !matches!(v.as_str(), Some("private" | "protected" | "public")))
    {
        return None;
    }
    let flag = |key| match relation.props.get(key) {
        None => Some(false),
        Some(v) => v.as_bool(),
    };
    let recursive = flag("isRecursive")?;
    let all = flag("isImportAll")?;
    let selected = raw.element_for_uuid(b, relation.props.get(key)?.as_reference()?)?;
    if !conforms(b.elements.get(selected)?.ty, kind) {
        return None;
    }
    let (element, membership) = if kind == "Membership" {
        let declaring =
            super::semantic_ownership::checked_relationship_carrier(b, raw, selected, steps)??;
        if !raw.membership_domains(b, steps)?.owner_complete(declaring) {
            return None;
        }
        let member = super::membership_evidence::member(b, raw, declaring, selected, steps)?;
        if b.elements[selected]
            .props
            .get("visibility")
            .is_some_and(|v| !matches!(v.as_str(), Some("private" | "protected" | "public")))
        {
            return None;
        }
        (member, Some(selected))
    } else {
        (selected, None)
    };
    let expected = b.elements[element].id;
    if relation
        .props
        .get("importedElement")
        .is_some_and(|v| v.as_reference() != Some(expected))
    {
        return None;
    }
    // Relationship.target is redefined by importedMembership or
    // importedNamespace; importedElement is the selected Membership's member.
    let relationship_target = b.elements[selected].id;
    for (key, expected) in [
        ("target", vec![relationship_target]),
        (
            "relatedElement",
            vec![b.elements[owner].id, relationship_target],
        ),
        (
            "ownedRelatedElement",
            relation
                .children
                .iter()
                .map(|&e| b.elements[e].id)
                .collect(),
        ),
    ] {
        if let Some(value) = relation.props.get(key) {
            let values = value.as_array()?;
            charge(steps, values.len())?;
            if values.len() != expected.len()
                || values
                    .iter()
                    .zip(expected)
                    .any(|(v, id)| v.as_reference() != Some(id))
            {
                return None;
            }
        }
    }
    Some(ImportTarget {
        element,
        membership,
        recursive,
        all,
    })
}

struct Signature {
    names: Vec<String>,
    member_type: &'static str,
}

impl Builder {
    /// Remove imported memberships indistinguishable from an owned membership
    /// or another imported membership (KerML Namespace::importedMemberships).
    /// The boolean qualifies signatures unavailable from the stored graph; such
    /// candidates remain, rather than guessing their effective names or type.
    /// This operation never performs name resolution or derived-property reads.
    pub(crate) fn distinguishable_import_memberships(
        &mut self,
        owner: usize,
        candidates: Vec<usize>,
    ) -> (Vec<usize>, bool) {
        let mut seen = HashSet::new();
        let candidates: Vec<_> = candidates.into_iter().filter(|r| seen.insert(*r)).collect();
        if candidates.is_empty() {
            return (candidates, false);
        }
        let owned: Vec<_> = self.elements[owner]
            .owned_relationships
            .iter()
            .copied()
            .filter(|&r| conforms(self.elements[r].ty, "Membership"))
            .collect();
        let owned: HashSet<_> = owned.into_iter().collect();
        let mut signatures = HashMap::new();
        let mut incomplete = false;
        for &rel in candidates.iter().chain(owned.iter()) {
            let signature = self.import_membership_signature(rel);
            incomplete |= signature.is_none();
            signatures.insert(rel, signature);
        }
        // Index only actual names. Unnamed memberships never collide, and most
        // namespaces require no pairwise metaclass comparisons at all.
        let mut by_name: HashMap<&str, Vec<usize>> = HashMap::new();
        for (&rel, signature) in &signatures {
            if let Some(signature) = signature {
                for name in &signature.names {
                    by_name.entry(name).or_default().push(rel);
                }
            }
        }
        let retained = candidates
            .into_iter()
            .filter(|rel| {
                let Some(Some(signature)) = signatures.get(rel) else {
                    return true;
                };
                !(owned.contains(rel) && !signature.names.is_empty())
                    && !signature.names.iter().any(|name| {
                        by_name[name.as_str()].iter().any(|other| {
                            if other == rel {
                                return false;
                            }
                            let other = signatures[other].as_ref().unwrap();
                            conforms(signature.member_type, other.member_type)
                                || conforms(other.member_type, signature.member_type)
                        })
                    })
            })
            .collect();
        (retained, incomplete)
    }

    fn import_membership_signature(&mut self, rel: usize) -> Option<Signature> {
        let member = self.stored_membership_member(rel)?;
        let member_type = self.elements[member].ty;
        let names = if conforms(self.elements[rel].ty, "OwningMembership") {
            self.stored_import_member_names(member, &mut HashSet::new())?
        } else {
            ["memberName", "memberShortName"]
                .into_iter()
                .filter_map(|key| {
                    self.elements[rel]
                        .props
                        .get(key)?
                        .as_str()
                        .map(str::to_owned)
                })
                .collect()
        };
        Some(Signature { names, member_type })
    }

    pub(super) fn stored_membership_member(&mut self, rel: usize) -> Option<usize> {
        if conforms(self.elements[rel].ty, "OwningMembership") {
            if let Some(&member) = self.elements[rel].children.first() {
                return Some(member);
            }
        }
        let id = self.elements[rel]
            .props
            .get("memberElement")?
            .as_reference()?;
        self.element_index_of_uuid(id)
    }

    fn stored_import_member_names(
        &mut self,
        mut member: usize,
        active: &mut HashSet<usize>,
    ) -> Option<Vec<String>> {
        loop {
            if !active.insert(member) {
                return None;
            }
            let names: Vec<_> = ["declaredName", "declaredShortName"]
                .into_iter()
                .filter_map(|key| {
                    self.elements[member]
                        .props
                        .get(key)?
                        .as_str()
                        .map(str::to_owned)
                })
                .collect();
            // Either declared name fixes both effective names; the absent one
            // remains null, rather than inheriting separately.
            if self.elements[member].ty == "ConjugatedPortDefinition" {
                return None;
            }
            if !names.is_empty() || !conforms(self.elements[member].ty, "Feature") {
                return Some(names);
            }
            if self.reference_locator_has_no_semantic_name(member) {
                return Some(Vec::new());
            }
            // SysML feature subclasses override namingFeature in several
            // contexts. Positional obligations can also add a naming target.
            // Those require a semantic plan, which may itself be calling us.
            if self.elements[member].ty != "Feature"
                || self.elements[member]
                    .props
                    .get("isEnd")
                    .and_then(|v| v.as_bool())
                    == Some(true)
                || self.elements[member]
                    .props
                    .get("direction")
                    .is_some_and(|v| !v.is_null())
            {
                return None;
            }
            let rel = self.elements[member]
                .owned_relationships
                .iter()
                .copied()
                .find(|&r| self.elements[r].ty == "Redefinition");
            if let Some(rel) = rel {
                let id = self.elements[rel]
                    .props
                    .get("redefinedFeature")?
                    .as_reference()?;
                member = self.element_index_of_uuid(id)?;
                continue;
            }
            if self.elements[member].owning_relationship.is_some_and(|r| {
                matches!(
                    self.elements[r].ty,
                    "ParameterMembership"
                        | "EndFeatureMembership"
                        | "ReturnParameterMembership"
                        | "SubjectMembership"
                        | "ObjectiveMembership"
                        | "ViewRenderingMembership"
                        | "TransitionFeatureMembership"
                )
            }) {
                return None;
            }
            // KerML Feature::namingFeature uses only ownedRedefinition; a
            // ReferenceSubsetting or FeatureChaining is not a naming rule.
            return Some(Vec::new());
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;

    fn membership(b: &mut Builder, owner: usize, ty: &'static str, path: &str) -> (usize, usize) {
        let rel = b.new_relationship("OwningMembership", owner, path);
        let element = b.new_element(ty, Some(rel), format!("{path}/member"));
        (rel, element)
    }

    #[test]
    fn unresolved_specialized_and_positional_names_are_qualified_without_deletion() {
        for (ty, property) in [
            ("ReferenceUsage", None),
            ("Feature", Some(("isEnd", json!(true)))),
            ("Feature", Some(("direction", json!("in")))),
            (
                "ConjugatedPortDefinition",
                Some(("declaredName", json!("X"))),
            ),
        ] {
            let mut b = Builder::default();
            let owner = b.new_element("Namespace", None, "owner".into());
            let source = b.new_element("Namespace", None, "source".into());
            let (known, e) = membership(&mut b, source, ty, "known");
            b.elements[e].props.insert("declaredName", json!("X"));
            let (unknown, e) = membership(&mut b, source, ty, "unknown");
            if let Some((key, value)) = property {
                b.elements[e].props.insert(key, value);
            }
            let (retained, incomplete) =
                b.distinguishable_import_memberships(owner, vec![known, unknown]);
            assert_eq!(retained, [known, unknown], "{ty}");
            assert!(incomplete, "{ty}");
        }
    }

    #[test]
    fn generic_feature_reference_and_chain_do_not_supply_effective_names() {
        for (ty, property) in [
            ("ReferenceSubsetting", "referencedFeature"),
            ("FeatureChaining", "chainingFeature"),
        ] {
            let mut b = Builder::default();
            let owner = b.new_element("Namespace", None, "owner".into());
            let source = b.new_element("Namespace", None, "source".into());
            let (named, target) = membership(&mut b, source, "Feature", "named");
            b.elements[target].props.insert("declaredName", json!("X"));
            let (unnamed, element) = membership(&mut b, source, "Feature", "unnamed");
            let rel = b.new_relationship(ty, element, "naming-candidate");
            let target_id = b.elements[target].id;
            b.elements[rel]
                .props
                .insert(property, super::super::id_ref(target_id));
            assert_eq!(
                b.distinguishable_import_memberships(owner, vec![named, unnamed]),
                (vec![named, unnamed], false)
            );
        }
    }
}
