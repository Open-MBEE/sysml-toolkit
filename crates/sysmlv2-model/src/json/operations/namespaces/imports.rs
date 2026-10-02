//! One checked Namespace membership composition for operation and property reads.
use super::*;
use std::collections::HashMap;

pub(super) struct Sequence {
    pub imported: Vec<Membership>,
    pub all: Vec<Membership>,
}

pub(super) fn references(members: Vec<Membership>) -> DerivedValue {
    DerivedValue::References(
        members
            .into_iter()
            .map(|m| Reference::Element(ElementRef(m.relationship)))
            .collect(),
    )
}
pub(super) fn exclusions(value: &DerivedValue) -> Vec<usize> {
    match value {
        DerivedValue::Elements(values) => values.iter().map(|e| e.0).collect(),
        DerivedValue::References(values) => values
            .iter()
            .map(|r| match r {
                Reference::Element(e) => e.0,
                _ => unreachable!("validated local Namespace"),
            })
            .collect(),
        _ => unreachable!("validated Namespace collection"),
    }
}
// Depth counts namespace import and containment edges, not helper dispatch
// within the same namespace. Every public selector starts at its owner at zero.
fn depth_limit(depth: usize, effective: &'static str) -> Result<(), OperationError> {
    if depth > crate::json::MAX_RESOLUTION_DEPTH {
        Err(OperationError::Incomplete { effective })
    } else {
        Ok(())
    }
}
#[derive(Clone, Copy)]
enum Traversal {
    CheckedTypes,
    PackagesOnly,
}

#[allow(clippy::too_many_arguments)]
pub(super) fn memberships_of_visibility(
    r: &mut ResolvedModel,
    raw: &StoredStructure,
    owner: usize,
    excluded: &[usize],
    requested: Option<&str>,
    steps: &mut usize,
    effective: &'static str,
    depth: usize,
) -> Result<Vec<Membership>, OperationError> {
    memberships_of_visibility_builder(
        &mut r.b,
        raw,
        owner,
        excluded,
        requested,
        steps,
        effective,
        depth,
        Traversal::CheckedTypes,
    )
}
#[allow(clippy::too_many_arguments)]
pub(super) fn visible(
    r: &mut ResolvedModel,
    raw: &StoredStructure,
    owner: usize,
    excluded: &[usize],
    recursive: bool,
    all: bool,
    steps: &mut usize,
    effective: &'static str,
    depth: usize,
) -> Result<Vec<Membership>, OperationError> {
    visible_builder(
        &mut r.b,
        raw,
        owner,
        excluded,
        recursive,
        all,
        steps,
        effective,
        depth,
        Traversal::CheckedTypes,
    )
}
/// Visibility-specific imports for the shared Type certificate. The restricted
/// traversal prevents recursive Type proof dependencies; non-Type namespace
/// providers still use exactly the operation engine's import/visibility algebra.
type TypeImports = (
    Vec<crate::json::membership_projection::Membership>,
    Vec<crate::json::membership_projection::Membership>,
);
pub(in crate::json) fn type_imports(
    b: &mut crate::json::Builder,
    raw: &StoredStructure,
    owner: usize,
    excluded: &[usize],
    steps: &mut usize,
) -> Result<TypeImports, OperationError> {
    const EFFECTIVE: &str = "Core-Types-Type-nonPrivateMemberships_Namespace_Type_Boolean";
    let mut result = (Vec::new(), Vec::new());
    for (access, members) in [("public", &mut result.0), ("protected", &mut result.1)] {
        let imported = imported_builder(
            b,
            raw,
            owner,
            excluded,
            Some(access),
            steps,
            EFFECTIVE,
            0,
            Traversal::PackagesOnly,
        )?;
        charge(steps, imported.len(), EFFECTIVE)?;
        members.extend(imported.into_iter().map(|m| {
            crate::json::membership_projection::Membership {
                relationship: m.relationship,
                member: m.member,
            }
        }));
    }
    Ok(result)
}
fn owned(
    b: &crate::json::Builder,
    raw: &StoredStructure,
    owner: usize,
    steps: &mut usize,
    effective: &'static str,
) -> Result<Vec<Membership>, OperationError> {
    let incomplete = || OperationError::Incomplete { effective };
    if !raw
        .import_domains(b, steps)
        .ok_or_else(incomplete)?
        .owner_complete(owner)
    {
        return Err(incomplete());
    }
    let result = memberships_builder(b, raw, owner, steps, effective)?;
    Ok(result)
}
fn unique(members: impl IntoIterator<Item = Membership>) -> Vec<Membership> {
    let mut seen = HashSet::new();
    members
        .into_iter()
        .filter(|m| seen.insert(m.relationship))
        .collect()
}
#[allow(clippy::too_many_arguments)]
fn import_builder(
    b: &mut crate::json::Builder,
    raw: &StoredStructure,
    owner: usize,
    relationship: usize,
    excluded: &[usize],
    steps: &mut usize,
    effective: &'static str,
    depth: usize,
    policy: Traversal,
) -> Result<Vec<Membership>, OperationError> {
    depth_limit(depth, effective)?;
    charge(steps, excluded.len().saturating_add(12), effective)?;
    let incomplete = || OperationError::Incomplete { effective };
    let target =
        crate::json::import_memberships::checked_import_target(b, raw, owner, relationship, steps)
            .ok_or_else(incomplete)?;
    let recursive = target.recursive;
    let all = target.all;
    let imported_element = target.element;
    let mut result = target.membership.map_or_else(Vec::new, |membership| {
        vec![Membership {
            relationship: membership,
            member: imported_element,
            visibility: visibility_builder(b, membership)
                .expect("checked imported Membership visibility"),
        }]
    });
    if (target.membership.is_none() || recursive)
        && conforms(b.elements[imported_element].ty, "Namespace")
        && !excluded.contains(&imported_element)
    {
        result.extend(visible_builder(
            b,
            raw,
            imported_element,
            excluded,
            recursive,
            all,
            steps,
            effective,
            depth + 1,
            policy,
        )?);
    }
    Ok(unique(result))
}
#[allow(clippy::too_many_arguments)]
fn imported_builder(
    b: &mut crate::json::Builder,
    raw: &StoredStructure,
    owner: usize,
    excluded: &[usize],
    requested: Option<&str>,
    steps: &mut usize,
    effective: &'static str,
    depth: usize,
    policy: Traversal,
) -> Result<Vec<Membership>, OperationError> {
    depth_limit(depth, effective)?;
    let incomplete = || OperationError::Incomplete { effective };
    let relationships = semantic_ownership::owned_relationships(b, owner).ok_or_else(incomplete)?;
    charge(
        steps,
        relationships.len().saturating_add(excluded.len()),
        effective,
    )?;
    let relationships: Vec<_> = relationships
        .iter()
        .filter(|&rel| conforms(b.elements[rel].ty, "Import"))
        .collect();
    let mut excluded = excluded.to_vec();
    excluded.push(owner);
    let mut result = Vec::new();
    for rel in relationships {
        let access = visibility_builder(b, rel).ok_or_else(incomplete)?;
        if requested.is_some_and(|v| v != access) {
            continue;
        }
        let imported = import_builder(
            b, raw, owner, rel, &excluded, steps, effective, depth, policy,
        )?;
        charge(steps, imported.len(), effective)?;
        result.extend(imported.into_iter().map(|mut m| {
            m.visibility = access;
            m
        }));
    }
    Ok(unique(result))
}
#[allow(clippy::too_many_arguments)]
fn memberships_of_visibility_builder(
    b: &mut crate::json::Builder,
    raw: &StoredStructure,
    owner: usize,
    excluded: &[usize],
    requested: Option<&str>,
    steps: &mut usize,
    effective: &'static str,
    depth: usize,
    policy: Traversal,
) -> Result<Vec<Membership>, OperationError> {
    depth_limit(depth, effective)?;
    let mut result = owned(b, raw, owner, steps, effective)?;
    if result
        .iter()
        .any(|m| conforms(b.elements[m.relationship].ty, "ElementFilterMembership"))
    {
        // Visibility-specific unions and Package's filtered imported collection
        // have distinct normative bodies. Do not silently choose a filter
        // evaluation policy for this contextual visible-import path.
        return Err(OperationError::Incomplete { effective });
    }
    result.retain(|m| requested.is_none_or(|v| v == m.visibility));
    result.extend(imported_builder(
        b, raw, owner, excluded, requested, steps, effective, depth, policy,
    )?);
    charge(steps, result.len(), effective)?;
    Ok(unique(result))
}
#[allow(clippy::too_many_arguments)]
fn visible_builder(
    b: &mut crate::json::Builder,
    raw: &StoredStructure,
    owner: usize,
    excluded: &[usize],
    recursive: bool,
    all: bool,
    steps: &mut usize,
    effective: &'static str,
    depth: usize,
    policy: Traversal,
) -> Result<Vec<Membership>, OperationError> {
    depth_limit(depth, effective)?;
    if matches!(policy, Traversal::PackagesOnly)
        && !matches!(
            b.elements[owner].ty,
            "Namespace" | "Package" | "LibraryPackage"
        )
    {
        return Err(OperationError::Incomplete { effective });
    }
    let mut result = memberships_of_visibility_builder(
        b,
        raw,
        owner,
        excluded,
        if all { None } else { Some("public") },
        steps,
        effective,
        depth,
        policy,
    )?;
    if recursive {
        let children = owned(b, raw, owner, steps, effective)?;
        charge(
            steps,
            excluded.len().saturating_add(children.len()),
            effective,
        )?;
        let mut excluded = excluded.to_vec();
        excluded.push(owner);
        for m in children {
            if conforms(b.elements[m.relationship].ty, "OwningMembership")
                && conforms(b.elements[m.member].ty, "Namespace")
                && (all || m.visibility == "public")
            {
                result.extend(visible_builder(
                    b,
                    raw,
                    m.member,
                    &excluded,
                    true,
                    all,
                    steps,
                    effective,
                    depth + 1,
                    policy,
                )?);
            }
        }
    }
    // Type visibility uses the same complete Membership reduction. Namespace
    // exclusions affect import contributions, never the inheritance graph.
    if conforms(b.elements[owner].ty, "Type") {
        charge(steps, excluded.len().saturating_add(1), effective)?;
        let mut inherited_excluded = excluded.to_vec();
        inherited_excluded.push(owner);
        let inherited = b
            .checked_type_memberships_for_visibility(owner, &inherited_excluded, recursive, steps)
            .map_err(|_| OperationError::Incomplete { effective })?
            .inherited;
        charge(steps, inherited.len(), effective)?;
        for m in inherited {
            let visibility = visibility_builder(b, m.relationship)
                .ok_or(OperationError::Incomplete { effective })?;
            if all || visibility == "public" {
                result.push(Membership {
                    relationship: m.relationship,
                    member: m.member,
                    visibility,
                });
            }
        }
    }
    charge(steps, result.len(), effective)?;
    Ok(unique(result))
}
pub(super) fn sequence(
    r: &mut ResolvedModel,
    raw: &StoredStructure,
    owner: usize,
    excluded: &[usize],
    steps: &mut usize,
    effective: &'static str,
) -> Result<Sequence, OperationError> {
    let owned = owned(&r.b, raw, owner, steps, effective)?;
    let mut imported = imported_builder(
        &mut r.b,
        raw,
        owner,
        excluded,
        None,
        steps,
        effective,
        0,
        Traversal::CheckedTypes,
    )?;
    // The admitted filter proof either leaves an unfiltered collection intact
    // or proves every candidate excluded. Universal exclusion commutes with
    // collision pruning and needs no irrelevant effective-name certificate.
    filter_memberships(r, raw, owner, &owned, &mut imported, steps, effective)?;
    // Namespace's documented distinguishability exclusion applies to its
    // importedMembership collection, not visibility-specific import unions.
    if !imported.is_empty() {
        let mut by_name: HashMap<String, Vec<(usize, &'static str)>> = HashMap::new();
        let mut seen = HashSet::new();
        let mut named = HashSet::new();
        for m in owned.iter().chain(&imported) {
            charge(steps, 1, effective)?;
            if !seen.insert(m.relationship) {
                continue;
            }
            for name in member_names(r, m, steps, effective)? {
                named.insert(m.relationship);
                by_name
                    .entry(name)
                    .or_default()
                    .push((m.relationship, r.b.elements[m.member].ty));
            }
        }
        let mut colliding = HashSet::new();
        for group in by_name.values() {
            charge(steps, group.len().saturating_mul(group.len()), effective)?;
            for &(a, ta) in group {
                if group
                    .iter()
                    .any(|&(b, tb)| a != b && (conforms(ta, tb) || conforms(tb, ta)))
                {
                    colliding.insert(a);
                }
            }
        }
        charge(steps, imported.len().saturating_add(owned.len()), effective)?;
        let own: HashSet<_> = owned
            .iter()
            .map(|m| m.relationship)
            .filter(|m| named.contains(m))
            .collect();
        imported.retain(|m| !colliding.contains(&m.relationship) && !own.contains(&m.relationship));
    }
    let mut all = unique(owned.into_iter().chain(imported.iter().cloned()));
    if conforms(r.b.elements[owner].ty, "Type") {
        let inherited =
            r.b.checked_type_memberships_for_visibility(owner, excluded, false, steps)
                .map_err(|_| OperationError::Incomplete { effective })?
                .inherited;
        charge(steps, inherited.len(), effective)?;
        for m in inherited {
            all.push(Membership {
                relationship: m.relationship,
                member: m.member,
                visibility: visibility(r, m.relationship)
                    .ok_or(OperationError::Incomplete { effective })?,
            });
        }
        all = unique(all);
    }
    Ok(Sequence { imported, all })
}

fn filter_memberships(
    r: &mut ResolvedModel,
    raw: &StoredStructure,
    owner: usize,
    owned: &[Membership],
    imported: &mut Vec<Membership>,
    steps: &mut usize,
    effective: &'static str,
) -> Result<(), OperationError> {
    let incomplete = || OperationError::Incomplete { effective };
    // ElementFilterMembership defines no filtering for a general Namespace;
    // this composition is specifically Package::importedMemberships.
    if !conforms(r.b.elements[owner].ty, "Package") {
        return Ok(());
    }
    charge(steps, owned.len().saturating_mul(5), effective)?;
    for m in owned
        .iter()
        .filter(|m| conforms(r.b.elements[m.relationship].ty, "ElementFilterMembership"))
    {
        let relation = &r.b.elements[m.relationship];
        let condition = &r.b.elements[m.member];
        if relation
            .props
            .get("condition")
            .is_some_and(|v| v.as_reference() != Some(condition.id))
            || condition
                .props
                .get("owningFilter")
                .is_some_and(|v| v.as_reference() != Some(relation.id))
            || condition
                .props
                .get("conditionedPackage")
                .is_some_and(|v| v.as_reference() != Some(r.b.elements[owner].id))
        {
            return Err(incomplete());
        }
    }
    charge(steps, owned.len(), effective)?;
    let conditions: Vec<_> = owned
        .iter()
        .filter(|m| conforms(r.b.elements[m.relationship].ty, "ElementFilterMembership"))
        .map(|m| m.member)
        .collect();
    charge(steps, conditions.len(), effective)?;
    if conditions.is_empty() || imported.is_empty() {
        return Ok(());
    }
    for &condition in &conditions {
        // ElementFilterMembership.condition is typed Expression; a Boolean
        // literal is Boolean-valued without being a BooleanExpression metaclass.
        if !conforms(r.b.elements[condition].ty, "Expression") {
            return Err(incomplete());
        }
        if r.b.elements[condition].ty == "LiteralBoolean"
            && r.b.elements[condition]
                .props
                .get("value")
                .and_then(|v| v.as_bool())
                == Some(false)
        {
            let report = r.model_level_evaluability_with_budget(ElementRef(condition), *steps);
            *steps = report.steps;
            if report.classification != crate::json::ModelLevelEvaluability::Evaluable {
                return Err(incomplete());
            }
            imported.clear();
            return Ok(());
        }
    }
    // includeAsMember requires at least one owned metadata occurrence for each
    // condition. Complete absence proves exclusion without evaluating a
    // condition in a fabricated metadata context.
    for m in imported.iter() {
        charge(steps, 1, effective)?;
        if raw.metadata_annotation_targets.contains(&m.member)
            || r.b
                .metadata_of
                .get(&m.member)
                .is_some_and(|v| !v.is_empty())
        {
            return Err(incomplete());
        }
    }
    imported.clear();
    Ok(())
}

pub(super) fn invoke_import(
    r: &mut ResolvedModel,
    receiver: ElementRef,
    excluded: &[usize],
    steps: &mut usize,
    effective: &'static str,
) -> Result<DerivedValue, OperationError> {
    let (_, _, result) =
        super::with_stable_evidence(r, receiver, steps, effective, |r, raw, steps| {
            let incomplete = || OperationError::Incomplete { effective };
            let owner =
                semantic_ownership::checked_relationship_carrier(&r.b, raw, receiver.0, steps)
                    .flatten()
                    .ok_or_else(incomplete)?;
            if !raw
                .import_domains(&r.b, steps)
                .ok_or_else(incomplete)?
                .owner_complete(owner)
            {
                return Err(incomplete());
            }
            import_builder(
                &mut r.b,
                raw,
                owner,
                receiver.0,
                excluded,
                steps,
                effective,
                0,
                Traversal::CheckedTypes,
            )
        })?;
    Ok(references(result))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::model::Model;
    use serde_json::json;
    fn fixture(source: &str) -> ResolvedModel {
        let mut m = Model::new();
        let unit = m.add_source("checked-imports.kerml", source);
        assert!(unit.diagnostics.is_empty(), "{:?}", unit.diagnostics);
        ResolvedModel::build(&m)
    }
    fn call(
        r: &mut ResolvedModel,
        name: &str,
        operation: &str,
        arguments: &[DerivedValue],
    ) -> Result<DerivedValue, OperationError> {
        let e = r.resolve_qualified(name).unwrap();
        r.invoke_operation(
            e,
            &format!("Root-Namespaces-Namespace-{operation}"),
            arguments,
        )
        .map(|v| v.value)
    }
    fn empty() -> DerivedValue {
        DerivedValue::Elements(vec![])
    }
    fn imported(r: &mut ResolvedModel, name: &str) -> DerivedValue {
        call(r, name, "importedMemberships_Namespace", &[empty()]).unwrap()
    }
    fn refs(value: DerivedValue) -> Vec<ElementRef> {
        let DerivedValue::References(v) = value else {
            panic!("expected references")
        };
        v.into_iter()
            .map(|v| match v {
                Reference::Element(e) => e,
                _ => panic!("external"),
            })
            .collect()
    }
    #[test]
    fn namespace_imports_preserve_alias_identity_and_contextual_visibility() {
        let mut r = fixture(
            "package P { class A; alias Alias for A; private class Hidden; } package Q { protected import P::Alias; private import P::*; }",
        );
        let p = r.resolve_qualified("P").unwrap();
        let a = r.resolve_qualified("P::A").unwrap();
        let alias = r.b.elements[p.0]
            .owned_relationships
            .iter()
            .copied()
            .find(|&x| r.b.elements[x].ty == "Membership")
            .unwrap();
        let a_mem = r.b.elements[a.0].owning_relationship.unwrap();
        assert_eq!(
            refs(imported(&mut r, "Q")),
            [ElementRef(alias), ElementRef(a_mem)]
        );
        assert_eq!(
            call(
                &mut r,
                "Q",
                "visibilityOf_Membership",
                &[DerivedValue::Element(ElementRef(alias))]
            )
            .unwrap(),
            DerivedValue::Str("protected".into())
        );
        assert_eq!(
            call(&mut r, "Q", "namesOf_Element", &[DerivedValue::Element(a)]).unwrap(),
            DerivedValue::Strings(vec!["Alias".into(), "A".into()])
        );
        assert_eq!(
            refs(
                call(
                    &mut r,
                    "Q",
                    "membershipsOfVisibility_VisibilityKind_Namespace",
                    &[DerivedValue::Str("private".into()), empty()]
                )
                .unwrap()
            ),
            [ElementRef(a_mem), ElementRef(alias)]
        );
        assert!(
            refs(
                call(
                    &mut r,
                    "Q",
                    "visibleMemberships_Namespace_Boolean_Boolean",
                    &[
                        empty(),
                        DerivedValue::Bool(false),
                        DerivedValue::Bool(false)
                    ]
                )
                .unwrap()
            )
            .is_empty()
        );
        let q = r.resolve_qualified("Q").unwrap();
        assert_eq!(
            r.property(q, "importedMembership").unwrap(),
            json!([{"@id": r.b.elements[alias].id.to_string()}, {"@id": r.b.elements[a_mem].id.to_string()}])
        );
    }
    #[test]
    fn recursive_imports_and_exclusion_cycles_are_bounded_and_ordered() {
        let mut r = fixture(
            "package P { package A { package B; } private package Secret; public import Q::*; } package Q { public import P::*::**; }",
        );
        let a = r.resolve_qualified("P::A").unwrap();
        let b = r.resolve_qualified("P::A::B").unwrap();
        assert_eq!(
            refs(imported(&mut r, "Q")),
            [a, b].map(|e| ElementRef(r.b.elements[e.0].owning_relationship.unwrap()))
        );
        let p = r.resolve_qualified("P").unwrap();
        assert!(
            refs(
                call(
                    &mut r,
                    "Q",
                    "importedMemberships_Namespace",
                    &[DerivedValue::Elements(vec![p])]
                )
                .unwrap()
            )
            .is_empty()
        );
        let q = r.resolve_qualified("Q").unwrap();
        let rel = r.b.elements[q.0].owned_relationships[0];
        let operation = "Root-Namespaces-NamespaceImport-importedMemberships_Namespace";
        let direct = r
            .invoke_operation(
                ElementRef(rel),
                operation,
                &[DerivedValue::Elements(vec![p])],
            )
            .unwrap()
            .value;
        assert!(refs(direct).is_empty());
    }
    #[test]
    fn collisions_are_pruned_only_from_the_namespace_imported_collection() {
        let mut r = fixture(
            "package A { class X; } package B { class X; } package Q { private import A::*; private import B::*; }",
        );
        assert!(refs(imported(&mut r, "Q")).is_empty());
        let raw = call(
            &mut r,
            "Q",
            "membershipsOfVisibility_VisibilityKind_Namespace",
            &[DerivedValue::Null, empty()],
        )
        .unwrap();
        assert_eq!(refs(raw).len(), 2);
    }
    #[test]
    fn malformed_import_aliases_flags_and_inverse_owners_refuse_current_reads() {
        for (key, value) in [
            ("isRecursive", json!(null)),
            ("isImportAll", json!("true")),
            ("importedElement", json!({"@id":"missing"})),
            ("target", json!([])),
            ("source", json!([])),
            ("relatedElement", json!([])),
        ] {
            let mut r = fixture("package P { class A; } package Q { private import P::*; }");
            assert_eq!(refs(imported(&mut r, "Q")).len(), 1);
            let q = r.resolve_qualified("Q").unwrap();
            let rel = r.b.elements[q.0].owned_relationships[0];
            r.b.set(rel, key, value);
            assert!(
                call(&mut r, "Q", "importedMemberships_Namespace", &[empty()]).is_err(),
                "{key}"
            );
        }
    }
    #[test]
    fn namespace_import_budget_and_revision_reuse_do_not_certify_partial_results() {
        let mut r = fixture("package P { class A; } package Q { private import P::*; }");
        let q = r.resolve_qualified("Q").unwrap();
        let mut row = NamespaceRow::default();
        let declaration = "Root-Namespaces-Namespace-importedMembership";
        let mut steps = crate::eval::MAX_STEPS - 1;
        assert!(row.property(&mut r, q, declaration, &mut steps).is_err());
        assert_eq!(
            refs(row.property(&mut r, q, declaration, &mut 0).unwrap()).len(),
            1
        );
        let rel = r.b.elements[q.0].owned_relationships[0];
        r.b.set(rel, "isRecursive", json!("invalid"));
        assert!(row.property(&mut r, q, declaration, &mut 0).is_err());
        assert!(r.b.implied.is_none());
    }
    #[test]
    fn import_proofs_reconstruct_from_compact_and_full_in_both_formats() {
        for format in [
            crate::model::GraphFormat::LegacyV2,
            crate::model::GraphFormat::CanonicalV3,
        ] {
            let mut m = Model::with_graph_format(format);
            let u = m.add_source(
                "import-replay.kerml",
                "package P { class A; alias Alias for A; } package Q { public import P::Alias; }",
            );
            assert!(u.diagnostics.is_empty());
            let mut original = ResolvedModel::build(&m);
            let original_ids: Vec<_> = refs(imported(&mut original, "Q"))
                .iter()
                .map(|e| original.element_id(*e))
                .collect();
            for document in [
                crate::json::model_to_compact_json(&m),
                crate::full::model_to_full_json(&m),
            ] {
                let (_, mut loaded, _, _) =
                    crate::loader::load_document_with_format(&document, &HashMap::new(), format)
                        .unwrap();
                let ids: Vec<_> = refs(imported(&mut loaded, "Q"))
                    .iter()
                    .map(|e| loaded.element_id(*e))
                    .collect();
                assert_eq!(ids, original_ids);
                let alias = refs(imported(&mut loaded, "Q"))[0];
                assert_eq!(
                    call(
                        &mut loaded,
                        "Q",
                        "resolveVisible_String",
                        &[DerivedValue::Str("Alias".into())]
                    )
                    .unwrap(),
                    DerivedValue::Reference(Reference::Element(alias))
                );
                assert_eq!(
                    call(
                        &mut loaded,
                        "Q",
                        "resolveVisible_String",
                        &[DerivedValue::Str("A".into())]
                    )
                    .unwrap(),
                    DerivedValue::Null
                );
            }
        }
    }
    #[test]
    fn recursive_member_import_keeps_its_membership_when_namespace_is_excluded() {
        let mut r = fixture("package P { package A; } package Q { public import P::**; }");
        let p = r.resolve_qualified("P").unwrap();
        let q = r.resolve_qualified("Q").unwrap();
        let membership = ElementRef(r.b.elements[p.0].owning_relationship.unwrap());
        let relationship = ElementRef(r.b.elements[q.0].owned_relationships[0]);
        let result = r
            .invoke_operation(
                relationship,
                "Root-Namespaces-MembershipImport-importedMemberships_Namespace",
                &[DerivedValue::Elements(vec![p])],
            )
            .unwrap();
        assert_eq!(refs(result.value), [membership]);
        assert_eq!(refs(imported(&mut r, "Q")).len(), 2);
    }
    #[test]
    fn omitted_import_visibility_is_private_and_literal_false_filters_are_proven() {
        let mut r = fixture("package P { class A; } package Q { public import P::*; }");
        let q = r.resolve_qualified("Q").unwrap();
        let rel = r.b.elements[q.0].owned_relationships[0];
        let mut props = crate::properties::Properties::new();
        for (key, value) in r.b.elements[rel].props.to_json() {
            if key != "visibility" {
                props.insert(&key, value);
            }
        }
        r.b.elements[rel].props = props;
        assert_eq!(refs(imported(&mut r, "Q")).len(), 1);
        assert!(
            refs(
                call(
                    &mut r,
                    "Q",
                    "visibleMemberships_Namespace_Boolean_Boolean",
                    &[
                        empty(),
                        DerivedValue::Bool(false),
                        DerivedValue::Bool(false)
                    ]
                )
                .unwrap()
            )
            .is_empty()
        );
        let mut r =
            fixture("package P { class A; } package Q { private import P::*; filter false; }");
        assert!(refs(imported(&mut r, "Q")).is_empty());
        let mut r = fixture("package P { class A; } package Q { private import P::*[false]; }");
        let q = r.resolve_qualified("Q").unwrap();
        let mut steps = 0;
        let raw = StoredStructure::for_query(&mut r.b, &mut steps).unwrap();
        assert!(
            raw.import_domains(&r.b, &mut steps)
                .unwrap()
                .owner_complete(q.0)
        );
        assert!(call(&mut r, "Q", "importedMemberships_Namespace", &[empty()]).is_err());
        let import = r.b.elements[q.0].owned_relationships[0];
        let child = r.b.elements[import].children[0];
        r.b.elements[child].owning_relationship = None;
        let raw = StoredStructure::for_query(&mut r.b, &mut 0).unwrap();
        assert!(
            !raw.import_domains(&r.b, &mut 0)
                .unwrap()
                .owner_complete(q.0)
        );
    }
    #[test]
    fn private_membership_import_type_features_survive_full_and_compact_replay() {
        const LIB: &str = "standard library package Base { classifier Anything; datatype DataValue specializes Anything; feature things:Anything; } standard library package Occurrences { class Occurrence specializes Base::Anything; feature occurrences:Occurrence subsets Base::things; }";
        for format in [
            crate::model::GraphFormat::LegacyV2,
            crate::model::GraphFormat::CanonicalV3,
        ] {
            let mut model = Model::with_graph_format(format);
            model.add_library_source("private-import-library.kerml", LIB);
            let u = model.add_source("private-import-types.kerml", "package P { class C; alias Alias for C; } class A { private import P::Alias; in feature x; }");
            assert!(u.diagnostics.is_empty(), "{:?}", u.diagnostics);
            let names = crate::json::library_name_map(&model);
            let mut original = ResolvedModel::build(&model);
            let a = original.resolve_qualified("A").unwrap();
            assert!(original.type_feature_report(a).projections.is_ok());
            for document in [
                crate::json::model_to_compact_json(&model),
                crate::full::model_to_full_json(&model),
            ] {
                let (mut replay, _, _, _) =
                    crate::loader::load_document_with_format(&document, &names, format).unwrap();
                replay.add_library_source("private-import-library.kerml", LIB);
                let mut loaded = ResolvedModel::build(&replay);
                let a = loaded.resolve_qualified("A").unwrap();
                let x = loaded.resolve_qualified("A::x").unwrap();
                let report = loaded.type_feature_report(a);
                assert_eq!(report.projections.unwrap().inputs, [x], "{format:?}");
                let import = loaded.b.elements[a.0]
                    .owned_relationships
                    .iter()
                    .copied()
                    .find(|&rel| loaded.b.elements[rel].ty == "MembershipImport")
                    .unwrap();
                let selected = loaded.b.elements[import]
                    .props
                    .get("importedMembership")
                    .unwrap()
                    .as_reference()
                    .unwrap();
                loaded
                    .b
                    .set(import, "target", json!([{"@id":selected.to_string()}]));
                // MembershipImport redefines Relationship.target with the
                // Membership, not its effectively imported member Element.
                assert_eq!(
                    loaded.type_feature_report(a).projections.unwrap().inputs,
                    [x]
                );
                let member = loaded.resolve_qualified("P::C").unwrap();
                let member_id = loaded.element_id(member);
                loaded
                    .b
                    .set(import, "target", json!([{"@id":member_id.to_string()}]));
                assert!(loaded.type_feature_report(a).projections.is_err());
                loaded
                    .b
                    .set(import, "target", json!([{"@id":selected.to_string()}]));
                assert_eq!(
                    loaded.type_feature_report(a).projections.unwrap().inputs,
                    [x]
                );
            }
        }
    }
    #[test]
    fn package_filter_aliases_must_agree_with_the_owned_condition() {
        for (on_condition, key) in [
            (false, "condition"),
            (true, "owningFilter"),
            (true, "conditionedPackage"),
        ] {
            for malformed in [json!(null), json!({"@id":"not-an-element"})] {
                let mut r = fixture(
                    "package P { class A; } package Q { private import P::*; filter false; }",
                );
                assert!(refs(imported(&mut r, "Q")).is_empty());
                let q = r.resolve_qualified("Q").unwrap();
                let membership = r.b.elements[q.0]
                    .owned_relationships
                    .iter()
                    .copied()
                    .find(|&rel| r.b.elements[rel].ty == "ElementFilterMembership")
                    .unwrap();
                let condition = r.b.elements[membership].children[0];
                r.b.set(
                    if on_condition { condition } else { membership },
                    key,
                    malformed,
                );
                assert!(
                    call(&mut r, "Q", "importedMemberships_Namespace", &[empty()]).is_err(),
                    "{key}"
                );
            }
        }
    }
}

#[cfg(test)]
mod depth_tests;
