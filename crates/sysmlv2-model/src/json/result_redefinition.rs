//! Checked canonical return witnesses for a later atomic generated-result tail.
//! Candidate discovery never by itself certifies an effective result.
use super::{
    Builder, dynamic_invocations::Refusal, semantic_ownership, structural_index::StoredStructure,
    type_relations,
};
use crate::metaclass::conforms;
use std::collections::{HashMap, HashSet};

fn charge(steps: &mut usize, n: usize) -> Result<(), Refusal> {
    *steps = steps.saturating_add(n);
    if *steps > crate::eval::MAX_STEPS {
        Err(Refusal::WorkLimit)
    } else {
        Ok(())
    }
}
fn incomplete(steps: &usize) -> Refusal {
    if *steps > crate::eval::MAX_STEPS {
        Refusal::WorkLimit
    } else {
        Refusal::Incomplete
    }
}

/// Exact loaded role identities; ambiguity is retained before inversion.
fn roles(
    b: &Builder,
    raw: &StoredStructure,
    steps: &mut usize,
) -> Result<(usize, usize, Option<usize>), Refusal> {
    let mut found = [None; 3];
    let mut ambiguous = [false; 3];
    charge(steps, b.lib_qnames.len())?;
    for (id, path) in &b.lib_qnames {
        // Charge segment traversal before computing the aggregate byte cost.
        // Empty segments still consume work; every size addition saturates.
        charge(steps, path.len())?;
        charge(
            steps,
            path.iter()
                .fold(0usize, |n, part| n.saturating_add(part.len())),
        )?;
        let slot = match path.as_slice() {
            [p, n] if p == "Performances" && n == "Evaluation" => 0,
            [p, n, r] if p == "Performances" && n == "Evaluation" && r == "result" => 1,
            [p, n] if p == "Performances" && n == "evaluations" => 2,
            _ => continue,
        };
        if found[slot].is_some_and(|previous| previous != *id) {
            ambiguous[slot] = true;
        }
        found[slot] = Some(*id);
    }
    let mut result = [None; 3];
    for i in 0..3 {
        if !ambiguous[i] {
            result[i] = found[i]
                .and_then(|id| raw.element_for_uuid(b, id))
                .filter(|&e| e < b.lib_boundary);
        }
    }
    let evaluation = result[0]
        .filter(|&e| b.elements[e].ty == "Function")
        .ok_or(Refusal::Incomplete)?;
    let returned = result[1]
        .filter(|&e| b.elements[e].ty == "Feature")
        .ok_or(Refusal::Incomplete)?;
    let evaluations = result[2].filter(|&e| b.elements[e].ty == "Expression");
    Ok((evaluation, returned, evaluations))
}
fn relationships(b: &Builder, owner: usize, steps: &mut usize) -> Result<Vec<usize>, Refusal> {
    let rows = semantic_ownership::owned_relationships(b, owner).ok_or(Refusal::Incomplete)?;
    charge(steps, rows.len())?;
    let rows: Vec<_> = rows.iter().collect();
    let mut seen = HashSet::new();
    if rows.iter().any(|&r| !seen.insert(r)) {
        return Err(Refusal::Incomplete);
    }
    Ok(rows)
}
fn membership(
    b: &Builder,
    raw: &StoredStructure,
    owner: usize,
    rel: usize,
    steps: &mut usize,
) -> Result<usize, Refusal> {
    let row = b.elements.get(rel).ok_or(Refusal::Incomplete)?;
    if !conforms(row.ty, "OwningMembership") || row.owning_relationship.is_some() {
        return Err(Refusal::Incomplete);
    }
    let child = super::membership_evidence::member(b, raw, owner, rel, steps)
        .ok_or_else(|| incomplete(steps))?;
    if child >= b.explicit_len()
        || row
            .props
            .get("visibility")
            .is_some_and(|v| !matches!(v.as_str(), Some("public" | "protected" | "private")))
        || conforms(row.ty, "FeatureMembership") && !conforms(b.elements[child].ty, "Feature")
    {
        return Err(Refusal::Incomplete);
    }

    Ok(child)
}
fn specialization(
    b: &mut Builder,
    raw: &StoredStructure,
    owner: usize,
    rel: usize,
    steps: &mut usize,
) -> Result<usize, Refusal> {
    let kind = b.elements.get(rel).ok_or(Refusal::Incomplete)?.ty;
    let (source_kind, target_kind) = if conforms(kind, "Subsetting") {
        ("Feature", "Feature")
    } else if conforms(kind, "FeatureTyping") {
        ("Feature", "Type")
    } else if conforms(kind, "Subclassification") {
        ("Classifier", "Classifier")
    } else {
        ("Type", "Type")
    };
    if !conforms(b.elements[owner].ty, source_kind) {
        return Err(Refusal::Incomplete);
    }
    let carrier = semantic_ownership::checked_relationship_carrier(b, raw, rel, steps)
        .ok_or_else(|| incomplete(steps))?;
    if carrier != Some(owner) {
        return Err(Refusal::Incomplete);
    }
    type_relations::endpoint_with_carrier(
        b,
        owner,
        carrier,
        rel,
        &[
            "specific",
            "subclassifier",
            "typedFeature",
            "subsettingFeature",
            "redefiningFeature",
            "referencingFeature",
            "crossingFeature",
        ],
        &[
            "general",
            "superclassifier",
            "type",
            "subsettedFeature",
            "redefinedFeature",
            "referencedFeature",
            "crossedFeature",
        ],
        target_kind,
        steps,
    )
    .ok_or_else(|| incomplete(steps))
}

/// Conservative checked slice: no imported membership, conjugation, chaining or
/// semantic metadata participates in this first canonical return certificate.
fn dependency_slice(
    b: &mut Builder,
    raw: &StoredStructure,
    roots: &[usize],
    steps: &mut usize,
) -> Result<HashMap<usize, Vec<usize>>, Refusal> {
    let domains = raw
        .membership_domains(b, steps)
        .ok_or_else(|| incomplete(steps))?;
    let inverse = raw.typing(b, steps).ok_or_else(|| incomplete(steps))?;
    if inverse.sources_incomplete {
        return Err(Refusal::Incomplete);
    }
    let mut bases = HashMap::new();
    let mut todo = roots.to_vec();
    let mut features = Vec::new();
    while let Some(owner) = todo.pop() {
        charge(steps, 1)?;
        if bases.contains_key(&owner) {
            continue;
        }
        if !domains.owner_complete(owner)
            || owner >= b.explicit_len()
            || !matches!(
                b.elements[owner].ty,
                "Classifier"
                    | "Class"
                    | "Structure"
                    | "DataType"
                    | "Behavior"
                    | "Function"
                    | "Feature"
                    | "Step"
                    | "Expression"
            )
            // This bounded fragment excludes conjugation rows; a retained flag
            // must agree rather than claiming ordinary inheritance by itself.
            || b.elements[owner].props.get("isConjugated")
                .is_some_and(|v| v.as_bool() != Some(false))
            || raw.bad_bases.contains(&owner)
            || raw.bad_chains.contains(&owner)
            || raw.metadata_annotation_targets.contains(&owner)
            || b.metadata_of.get(&owner).is_some_and(|m| !m.is_empty())
        {
            return Err(Refusal::Incomplete);
        }
        if let Some(&scope) = b.elem_scope.get(&owner) {
            let scope = &b.scopes[scope];
            charge(
                steps,
                scope.imports.len()
                    + scope.member_imports.len()
                    + scope.aliases.len()
                    + scope.filters.len()
                    + scope.chain_bases.len(),
            )?;
            if scope.imports.iter().any(|i| {
                b.elements[i.relationship]
                    .props
                    .get("visibility")
                    .and_then(|v| v.as_str())
                    != Some("private")
            }) || scope.member_imports.iter().any(|i| {
                b.elements[i.relationship]
                    .props
                    .get("visibility")
                    .and_then(|v| v.as_str())
                    != Some("private")
            }) || !scope.aliases.is_empty()
                || !scope.filters.is_empty()
                || !scope.chain_bases.is_empty()
            {
                return Err(Refusal::Incomplete);
            }
        }
        let mut direct = Vec::new();
        for rel in relationships(b, owner, steps)? {
            let row = b.elements.get(rel).ok_or(Refusal::Incomplete)?;
            if conforms(row.ty, "Conjugation")
                || conforms(row.ty, "FeatureChaining")
                || (conforms(row.ty, "Import")
                    && row.props.get("visibility").and_then(|v| v.as_str()) != Some("private"))
            {
                return Err(Refusal::Incomplete);
            }
            if conforms(row.ty, "Membership") {
                let child = membership(b, raw, owner, rel, steps)?;
                if conforms(b.elements[child].ty, "Feature") {
                    features.push(child);
                }
            } else if conforms(row.ty, "Specialization") {
                let target = specialization(b, raw, owner, rel, steps)?;
                charge(steps, direct.len() + 1)?;
                if !direct.contains(&target) {
                    direct.push(target);
                    todo.push(target);
                }
            }
        }
        bases.insert(owner, direct);
    }
    // Validate every stored redefinition closure that the common positional
    // shadowing algorithm may consume, including targets outside the base slice.
    let mut seen = HashSet::new();
    let mut redefinitions = HashMap::new();
    while let Some(feature) = features.pop() {
        charge(steps, 1)?;
        if !seen.insert(feature) {
            continue;
        }
        if !conforms(
            b.elements.get(feature).ok_or(Refusal::Incomplete)?.ty,
            "Feature",
        ) || raw.bad_bases.contains(&feature)
            || raw.metadata_annotation_targets.contains(&feature)
            || b.metadata_of.get(&feature).is_some_and(|m| !m.is_empty())
        {
            return Err(Refusal::Incomplete);
        }
        let mut actual = HashSet::new();
        for rel in relationships(b, feature, steps)? {
            if conforms(b.elements[rel].ty, "Redefinition") && rel < b.explicit_len() {
                let target = specialization(b, raw, feature, rel, steps)?;
                actual.insert(target);
                features.push(target);
            }
        }
        for &rel in inverse.relationships.get(&feature).into_iter().flatten() {
            charge(steps, 1)?;
            if rel < b.explicit_len() && conforms(b.elements[rel].ty, "Redefinition") {
                let target = specialization(b, raw, feature, rel, steps)?;
                if !actual.contains(&target) {
                    return Err(Refusal::Incomplete);
                }
            }
        }
        redefinitions.insert(feature, actual.into_iter().collect::<Vec<_>>());
    }
    if b.positional_redefinition_sources_match(&redefinitions, steps) != Some(true) {
        return Err(incomplete(steps));
    }
    acyclic(&redefinitions, steps)?;
    Ok(bases)
}

fn acyclic(graph: &HashMap<usize, Vec<usize>>, steps: &mut usize) -> Result<(), Refusal> {
    let mut state = HashMap::new();
    for &root in graph.keys() {
        let mut todo = vec![(root, false)];
        while let Some((owner, exit)) = todo.pop() {
            charge(steps, 1)?;
            if exit {
                state.insert(owner, 2);
                continue;
            }
            match state.get(&owner) {
                Some(1) => return Err(Refusal::Incomplete),
                Some(2) => continue,
                _ => {}
            }
            state.insert(owner, 1);
            todo.push((owner, true));
            let next = graph.get(&owner).map(Vec::as_slice).unwrap_or(&[]);
            charge(steps, next.len())?;
            todo.extend(next.iter().rev().map(|&n| (n, false)));
        }
    }
    Ok(())
}

/// This returns positive canonical base/result identities only. It neither
/// resolves a source expression's bases nor publishes any generated edge.
pub(super) fn canonical_witness(
    b: &mut Builder,
    steps: &mut usize,
) -> Result<(Vec<usize>, usize), Refusal> {
    let raw = StoredStructure::for_query(b, steps).ok_or_else(|| incomplete(steps))?;
    if !raw.ids_unique || raw.annotations_incomplete || b.metadata_associations_incomplete {
        return Err(Refusal::Incomplete);
    }
    let (evaluation, result, evaluations) = roles(b, &raw, steps)?;
    let member = b.elements[result]
        .owning_relationship
        .ok_or(Refusal::Incomplete)?;
    if b.elements[member].ty != "ReturnParameterMembership"
        || membership(b, &raw, evaluation, member, steps)? != result
    {
        return Err(Refusal::Incomplete);
    }
    let mut admitted = Vec::new();
    for root in std::iter::once(evaluation).chain(evaluations) {
        let bases = match dependency_slice(b, &raw, &[root], steps) {
            Ok(bases) => bases,
            Err(Refusal::WorkLimit) => return Err(Refusal::WorkLimit),
            Err(_) => continue,
        };
        let candidates = b
            .plan_unique_result_candidates(&bases, &HashSet::new(), &[root], steps)
            .ok_or_else(|| incomplete(steps))?;
        if candidates.get(&root) == Some(&result) {
            admitted.push(root);
        }
    }
    Ok((admitted, result))
}

#[derive(Default)]
pub(super) struct Evidence {
    pub sources: HashSet<usize>,
    pub relationships: HashSet<usize>,
}
pub(super) struct Plan {
    from: usize,
    before: usize,
    rows: Vec<super::Elem>,
    roles: Vec<super::local_featuring::Role>,
    replacements: Vec<(usize, Vec<usize>)>,
    evidence: Evidence,
    edges: Vec<(uuid::Uuid, uuid::Uuid)>,
}
/// Stage only independently proven canonical direct-base obligations. Other
/// direct bases remain qualified and cannot erase these known obligations.
pub(super) fn prepare(
    b: &mut Builder,
    rows: &[super::Elem],
    roles: &[super::local_featuring::Role],
    steps: &mut usize,
) -> Result<Plan, Refusal> {
    charge(
        steps,
        1 + rows.len().saturating_mul(2) + roles.len().saturating_mul(16),
    )?;
    if b.implied.is_none() {
        return Err(Refusal::Incomplete);
    }
    let raw = StoredStructure::for_query(b, steps).ok_or_else(|| incomplete(steps))?;
    let metadata = b.metadata_association_generation.clone();
    let (bases, target) = canonical_witness(b, steps)?;
    let mut ids = HashSet::new();
    for row in rows {
        if raw.element_for_uuid(b, row.id).is_some() || !ids.insert(row.id) {
            return Err(Refusal::Collision);
        }
    }
    let mut plan = Plan {
        from: b.elements.len(),
        before: rows.len(),
        rows: Vec::new(),
        roles: Vec::new(),
        replacements: Vec::new(),
        evidence: Evidence::default(),
        edges: Vec::new(),
    };
    for &role in roles {
        if role.target != role.anchor || !super::local_featuring::valid(b, rows, role) {
            return Err(Refusal::Stale);
        }
        let mut proven = false;
        for relation in relationships(b, role.anchor, steps)? {
            if !conforms(b.elements[relation].ty, "Specialization") {
                continue;
            }
            match specialization(b, &raw, role.anchor, relation, steps) {
                Ok(target) if bases.contains(&target) => proven = true,
                Err(Refusal::WorkLimit) => return Err(Refusal::WorkLimit),
                _ => {}
            }
        }
        if !proven {
            continue;
        }
        if !plan.evidence.sources.insert(role.source) {
            return Err(Refusal::Stale);
        }
        let source = &rows[role.source - b.elements.len()];
        let target_id = b.elements[target].id;
        let id = uuid::Uuid::new_v5(
            &uuid::Uuid::NAMESPACE_OID,
            format!("{}/implied/Redefinition/{target_id}", source.id).as_bytes(),
        );
        if raw.element_for_uuid(b, id).is_some() || !ids.insert(id) {
            return Err(Refusal::Collision);
        }
        charge(steps, source.owned_relationships.len())?;
        let index = b.elements.len() + rows.len() + plan.rows.len();
        let mut owned = source.owned_relationships.to_vec();
        owned.push(index);
        plan.replacements
            .push((role.source - b.elements.len(), owned));
        plan.roles.push(role);
        plan.evidence.relationships.insert(index);
        plan.edges.push((source.id, target_id));
        let mut props = crate::properties::Properties::new();
        props.insert("isImplied", serde_json::json!(true));
        for (key, id) in [
            ("owningRelatedElement", source.id),
            ("redefiningFeature", source.id),
            ("redefinedFeature", target_id),
        ] {
            props.insert(key, serde_json::json!({"@id":id.to_string()}));
        }
        plan.rows.push(super::Elem {
            ty: "Redefinition",
            id,
            path: String::new(),
            path_parent: None,
            props,
            owned_relationships: Default::default(),
            children: Default::default(),
            owning_relationship: None,
        });
    }
    let metadata_current = match (&metadata, &b.metadata_association_generation) {
        (None, None) => true,
        (Some(a), Some(z)) => std::sync::Arc::ptr_eq(a, z),
        _ => false,
    };
    if !raw.is_current(b) || !metadata_current {
        return Err(Refusal::Stale);
    }
    Ok(plan)
}
impl Plan {
    pub(super) fn append(
        self,
        rows: &mut Vec<super::Elem>,
        ownership: &mut semantic_ownership::SemanticOwnership,
        graph: &mut HashMap<uuid::Uuid, Vec<uuid::Uuid>>,
    ) -> Evidence {
        assert_eq!(rows.len(), self.before);
        for (owner, relationships) in self.replacements {
            rows[owner].owned_relationships = relationships.into();
        }
        for ((row, role), (source, target)) in self.rows.into_iter().zip(self.roles).zip(self.edges)
        {
            ownership
                .register(
                    self.from + rows.len(),
                    Some(role.source),
                    role.anchor,
                    false,
                )
                .expect("prevalidated result inheritance carrier");
            rows.push(row);
            graph.entry(source).or_default().push(target);
        }
        self.evidence
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{json::ResolvedModel, model::Model};
    const LIB: &str = "standard library package Base {classifier Anything;feature things:Anything;} standard library package Occurrences {class Occurrence specializes Base::Anything;feature occurrences:Occurrence subsets Base::things;} standard library package Performances {behavior Performance specializes Occurrences::Occurrence;function Evaluation specializes Performance {return result;} step performances:Performance subsets Occurrences::occurrences;expr evaluations:Evaluation subsets performances;}";
    fn unpublished(lib: &str, user: &str) -> ResolvedModel {
        let mut m = Model::new();
        m.add_library_source("return-library.kerml", lib);
        m.add_source("return-user.kerml", user);
        assert!(!m.has_errors());
        ResolvedModel::build(&m)
    }
    fn fixture(lib: &str) -> ResolvedModel {
        let mut r = unpublished(lib, "feature n;feature x=n;");
        let e = r
            .user_elements()
            .find(|&e| r.element_type(e) == "FeatureReferenceExpression")
            .unwrap();
        r.implied_relationships(e);
        r
    }
    #[test]
    fn canonical_result_does_not_ignore_orphan_membership_claiming_same_owner() {
        let library =
            format!("{LIB} standard library package Extra {{function F {{return omitted;}}}}");
        let mut r = unpublished(&library, "feature n; feature x=n;");
        let evaluation = r.resolve_qualified("Performances::Evaluation").unwrap().0;
        let extra_owner = r.resolve_qualified("Extra::F").unwrap().0;
        let extra = r.resolve_qualified("Extra::F::omitted").unwrap().0;
        let membership = r.b.elements[extra].owning_relationship.unwrap();
        let id = r.b.elements[evaluation].id;
        r.b.elements[extra_owner]
            .owned_relationships
            .make_mut()
            .retain(|&rel| rel != membership);
        for key in [
            "owningRelatedElement",
            "membershipOwningNamespace",
            "owningType",
        ] {
            r.b.set(membership, key, serde_json::json!({"@id":id.to_string()}));
        }
        r.b.set(
            extra,
            "owningType",
            serde_json::json!({"@id":id.to_string()}),
        );
        let witness = canonical_witness(&mut r.b, &mut 0);
        assert!(
            !witness
                .as_ref()
                .is_ok_and(|(bases, _)| bases.contains(&evaluation)),
            "orphan claimed result must prevent canonical uniqueness: {witness:?}"
        );
    }
    #[test]
    fn independent_orphan_child_backlink_must_refuse_return_uniqueness() {
        let mut r = unpublished(LIB, "feature n;feature x=n;");
        let returned = r
            .resolve_qualified("Performances::Evaluation::result")
            .unwrap()
            .0;
        let member = r.b.elements[returned].owning_relationship.unwrap();
        assert!(canonical_witness(&mut r.b, &mut 0).is_ok());
        let mut extra = r.b.elements[returned].clone();
        extra.id = uuid::Uuid::new_v5(
            &uuid::Uuid::NAMESPACE_OID,
            b"independent orphan return child",
        );
        extra.path.clear();
        extra.path_parent = None;
        extra.owned_relationships = Vec::new().into();
        extra.owning_relationship = Some(member);
        r.b.elements.push(extra);
        let evaluation = r.resolve_qualified("Performances::Evaluation").unwrap().0;
        assert!(
            !canonical_witness(&mut r.b, &mut 0)
                .is_ok_and(|(bases, _)| bases.contains(&evaluation)),
            "orphan inverse child must not certify unique return"
        );
    }
    #[test]
    fn orphan_membership_and_child_refusals_replay_all_library_representations() {
        use crate::{libcache::LibraryCache, prepared::PreparedLibrary};
        use std::sync::Arc;
        let mut library = Model::new();
        library.add_library_source("return-library.kerml", LIB);
        library.record_library_cache();
        ResolvedModel::build(&library);
        let cache =
            LibraryCache::from_bytes(&library.take_recorded_library_cache().unwrap().to_bytes())
                .unwrap();
        let prepared = library.prepare_library().unwrap();
        let decoded =
            Arc::new(PreparedLibrary::from_bytes(&prepared.to_bytes(147).unwrap(), 147).unwrap());
        for mode in 0..4 {
            for orphan_child in [false, true] {
                let mut model = Model::new();
                match mode {
                    2 => Arc::clone(&prepared).install(&mut model).unwrap(),
                    3 => Arc::clone(&decoded).install(&mut model).unwrap(),
                    _ => {
                        model.add_library_source("return-library.kerml", LIB);
                        if mode == 1 {
                            model.set_library_cache(cache.clone());
                        }
                    }
                }
                model.add_source(
                    "return-user.kerml",
                    "function Other {return extra;} feature n; feature x=n;",
                );
                let mut r = ResolvedModel::build(&model);
                let evaluation = r.resolve_qualified("Performances::Evaluation").unwrap().0;
                let returned = r
                    .resolve_qualified("Performances::Evaluation::result")
                    .unwrap()
                    .0;
                let extra = r.resolve_qualified("Other::extra").unwrap().0;
                let other = r.resolve_qualified("Other").unwrap().0;
                assert!(
                    canonical_witness(&mut r.b, &mut 0)
                        .unwrap()
                        .0
                        .contains(&evaluation)
                );
                if orphan_child {
                    r.b.elements[extra].owning_relationship =
                        r.b.elements[returned].owning_relationship;
                } else {
                    let membership = r.b.elements[extra].owning_relationship.unwrap();
                    r.b.elements[other]
                        .owned_relationships
                        .make_mut()
                        .retain(|&rel| rel != membership);
                    let id = r.b.elements[evaluation].id;
                    r.b.set(
                        membership,
                        "owningRelatedElement",
                        serde_json::json!({"@id":id.to_string()}),
                    );
                }
                assert!(
                    !canonical_witness(&mut r.b, &mut 0)
                        .is_ok_and(|(bases, _)| bases.contains(&evaluation)),
                    "mode={mode}, child={orphan_child}"
                );
            }
        }
    }
    #[test]
    fn inverse_redefinition_sources_cannot_hide_a_shadowing_dependency() {
        for contradictory_alias in [false, true] {
            let mut r = unpublished(LIB, "feature other; feature alt redefines other;");
            let evaluation = r.resolve_qualified("Performances::Evaluation").unwrap().0;
            let result = r
                .resolve_qualified("Performances::Evaluation::result")
                .unwrap()
                .0;
            let alt = r.resolve_qualified("alt").unwrap().0;
            assert!(
                canonical_witness(&mut r.b, &mut 0)
                    .unwrap()
                    .0
                    .contains(&evaluation)
            );
            let relation = *r.b.elements[alt]
                .owned_relationships
                .iter()
                .find(|&&rel| r.b.elements[rel].ty == "Redefinition")
                .unwrap();
            let id = r.b.elements[result].id;
            if contradictory_alias {
                r.b.set(
                    relation,
                    "specific",
                    serde_json::json!({"@id":id.to_string()}),
                );
            } else {
                r.b.elements[alt]
                    .owned_relationships
                    .make_mut()
                    .retain(|&rel| rel != relation);
                r.b.set(
                    relation,
                    "redefiningFeature",
                    serde_json::json!({"@id":id.to_string()}),
                );
            }
            assert!(
                !canonical_witness(&mut r.b, &mut 0)
                    .is_ok_and(|(bases, _)| bases.contains(&evaluation))
            );
        }
    }
    #[test]
    fn checked_canonical_witness_matches_actual_direct_base_results() {
        let mut r = fixture(LIB);
        let expected = r
            .resolve_qualified("Performances::Evaluation::result")
            .unwrap()
            .0;
        assert_eq!(canonical_witness(&mut r.b, &mut 0).unwrap().1, expected);
    }
    #[test]
    fn canonical_role_and_membership_ambiguities_are_refused() {
        let mut r = fixture(LIB);
        let result = r
            .resolve_qualified("Performances::Evaluation::result")
            .unwrap()
            .0;
        let n = r.resolve_qualified("n").unwrap().0;
        let member = r.b.elements[result].owning_relationship.unwrap();
        let wrong = r.b.elements[n].id;
        r.b.elements[member].props.insert(
            "memberFeature",
            serde_json::json!({"@id":wrong.to_string()}),
        );
        assert!(canonical_witness(&mut r.b, &mut 0).is_err());
        let mut r = fixture(LIB);
        let n = r.resolve_qualified("n").unwrap();
        let id = r.element_id(n);
        r.b.lib_qnames.push((
            id,
            vec!["Performances".into(), "Evaluation".into(), "result".into()],
        ));
        assert!(canonical_witness(&mut r.b, &mut 0).is_err());
    }

    #[test]
    fn return_parameter_aliases_are_checked_before_positive_publication() {
        for key in [
            "ownedMemberParameter",
            "owningMembership",
            "owningFeatureMembership",
            "owningParameterMembership",
        ] {
            for bad in [false, true] {
                let mut r = unpublished(LIB, "feature n;feature x=n;");
                let result = r
                    .resolve_qualified("Performances::Evaluation::result")
                    .unwrap()
                    .0;
                let member = r.b.elements[result].owning_relationship.unwrap();
                let expected = if key == "ownedMemberParameter" {
                    result
                } else {
                    member
                };
                let target = if key == "ownedMemberParameter" {
                    member
                } else {
                    result
                };
                let id = if bad {
                    {
                        let n = r.resolve_qualified("n").unwrap();
                        r.element_id(n)
                    }
                } else {
                    r.b.elements[expected].id
                };
                r.b.elements[target]
                    .props
                    .insert(key, serde_json::json!({"@id":id.to_string()}));
                let expression = r
                    .user_elements()
                    .find(|&e| r.element_type(e) == "FeatureReferenceExpression")
                    .unwrap();
                r.implied_relationships(expression);
                let result =
                    r.b.semantic_ownership
                        .as_ref()
                        .unwrap()
                        .result(expression.0)
                        .unwrap()
                        .feature;
                assert_eq!(
                    r.b.elements[result]
                        .owned_relationships
                        .iter()
                        .any(|&rel| r.b.elements[rel].ty == "Redefinition"),
                    !bad,
                    "{key}, bad={bad}"
                );
                // Refusing this new certificate never removes the independently
                // admitted result/Binding and local TypeFeaturing families.
                assert!(
                    r.b.elements[result]
                        .owned_relationships
                        .iter()
                        .any(|&rel| r.b.elements[rel].ty == "Subsetting")
                );
                assert!(
                    r.b.elements[result]
                        .owned_relationships
                        .iter()
                        .any(|&rel| r.b.elements[rel].ty == "TypeFeaturing")
                );
            }
        }
    }

    #[test]
    fn nonconjugated_dependency_flags_require_exact_false_or_absence() {
        for value in [
            serde_json::json!(false),
            serde_json::json!(true),
            serde_json::json!(null),
            serde_json::json!("false"),
            serde_json::json!({}),
        ] {
            let mut r = fixture(LIB);
            let evaluation = r.resolve_qualified("Performances::Evaluation").unwrap().0;
            r.b.elements[evaluation]
                .props
                .insert("isConjugated", value.clone());
            let witness = canonical_witness(&mut r.b, &mut 0).unwrap();
            assert_eq!(
                !witness.0.is_empty(),
                value == serde_json::json!(false),
                "{value}"
            );
        }
    }
    #[test]
    fn role_path_segment_work_is_charged_before_traversal() {
        let mut r = fixture(LIB);
        let raw = StoredStructure::for_query(&mut r.b, &mut 0).unwrap();
        let id = r.b.elements[0].id;
        r.b.lib_qnames = vec![(id, vec![String::new(); 6])].into();
        let mut steps = crate::eval::MAX_STEPS - 5;
        assert!(matches!(
            roles(&r.b, &raw, &mut steps),
            Err(Refusal::WorkLimit)
        ));
    }
    #[test]
    fn overridden_or_cyclic_canonical_base_does_not_reuse_named_return() {
        let override_lib = LIB.replace(
            "expr evaluations:Evaluation subsets performances;",
            "expr evaluations:Evaluation subsets performances {return other;}",
        );
        let mut r = fixture(&override_lib);
        let base = r.resolve_qualified("Performances::Evaluation").unwrap().0;
        assert_eq!(canonical_witness(&mut r.b, &mut 0).unwrap().0, vec![base]);
        let cyclic = LIB.replace(
            "behavior Performance specializes Occurrences::Occurrence;",
            "behavior Performance specializes Evaluation;",
        );
        let mut r = fixture(&cyclic);
        assert!(canonical_witness(&mut r.b, &mut 0).unwrap().0.is_empty());
    }
    fn generated(r: &ResolvedModel) -> (usize, usize, usize) {
        let expression = r
            .user_elements()
            .find(|&e| r.element_type(e) == "FeatureReferenceExpression")
            .unwrap()
            .0;
        let result =
            r.b.semantic_ownership
                .as_ref()
                .unwrap()
                .result(expression)
                .unwrap()
                .feature;
        let relation = *r.b.elements[result]
            .owned_relationships
            .iter()
            .find(|&&rel| r.b.elements[rel].ty == "Redefinition")
            .unwrap();
        (expression, result, relation)
    }
    #[test]
    fn direct_result_edge_appends_after_old_fourteen_and_preserves_independent_witness() {
        use crate::json::{
            dynamic_graph::Outcome,
            type_relations::{RelationFact, TypeRelations},
        };
        let mut r = fixture(LIB);
        let (expression, result, relation) = generated(&r);
        let expected = r
            .resolve_qualified("Performances::Evaluation::result")
            .unwrap()
            .0;
        let n = r.resolve_qualified("n").unwrap().0;
        let from = r.b.implied.as_ref().unwrap().owned_results_from;
        assert_eq!(r.b.elements.len() - from, 15);
        assert_eq!(relation, from + 14);
        assert_eq!(result, from + 1);
        assert_eq!(
            r.b.elements[result].owned_relationships.to_vec(),
            vec![from + 2, from + 11, from + 14]
        );
        assert_eq!(
            r.b.dynamic_graph
                .as_ref()
                .unwrap()
                .result_redefinition_outcome,
            Outcome::Accepted
        );
        assert_eq!(
            TypeRelations::default().specializes(&mut r.b, result, expected, &mut 0),
            RelationFact::Yes
        );
        let ids: Vec<_> = r.b.elements.iter().map(|e| e.id).collect();
        r.implied_relationships(crate::json::ElementRef(expression));
        assert_eq!(ids, r.b.elements.iter().map(|e| e.id).collect::<Vec<_>>());
        r.b.metadata_association_generation = Some(std::sync::Arc::new(()));
        assert_ne!(
            TypeRelations::default().specializes(&mut r.b, result, expected, &mut 0),
            RelationFact::Yes
        );
        assert_eq!(
            TypeRelations::default().specializes(&mut r.b, result, n, &mut 0),
            RelationFact::Yes
        );
        assert_eq!(
            TypeRelations::default().featuring_types(&mut r.b, result, &mut 0),
            Some(vec![expression])
        );
    }
    #[test]
    fn explicit_supertypes_ignore_only_valid_excluded_stale_result_rows() {
        use crate::json::type_relations::{RelationFact, TypeRelations};
        let mut r = fixture(LIB);
        let (_, result, relation) = generated(&r);
        let expected = r
            .resolve_qualified("Performances::Evaluation::result")
            .unwrap()
            .0;
        let n = r.resolve_qualified("n").unwrap().0;
        let mut before = TypeRelations::default();
        assert_eq!(
            before.checked_supertypes(&mut r.b, result, true, &mut 0),
            Ok(vec![])
        );
        r.b.metadata_association_generation = Some(std::sync::Arc::new(()));
        assert!(
            before
                .checked_supertypes(&mut r.b, result, true, &mut 0)
                .is_err()
        );
        let mut fresh = TypeRelations::default();
        for _ in 0..2 {
            assert_eq!(
                fresh.checked_supertypes(&mut r.b, result, true, &mut 0),
                Ok(vec![])
            );
        }
        assert_ne!(
            TypeRelations::default().specializes(&mut r.b, result, expected, &mut 0),
            RelationFact::Yes
        );
        assert_eq!(
            TypeRelations::default().specializes(&mut r.b, result, n, &mut 0),
            RelationFact::Yes
        );
        for flag in [serde_json::json!(false), serde_json::Value::Null] {
            r.b.elements[relation].props.insert("isImplied", flag);
            assert!(
                TypeRelations::default()
                    .checked_supertypes(&mut r.b, result, true, &mut 0)
                    .is_err()
            );
        }
    }

    #[test]
    fn generated_explicit_edge_id_survives_remap_without_stale_recertification() {
        use crate::json::{
            ElementRef,
            type_relations::{RelationFact, TypeRelations},
        };
        let mut r = fixture(LIB);
        let (expression, result, relation) = generated(&r);
        let target = r
            .resolve_qualified("Performances::Evaluation::result")
            .unwrap()
            .0;
        let explicit =
            uuid::Uuid::new_v5(&uuid::Uuid::NAMESPACE_OID, b"explicit result redefinition");
        let old = r.element_id(ElementRef(relation));
        let len = r.b.elements.len();
        r.override_ids(&HashMap::from([(old, explicit)]));
        assert_eq!(r.b.elements.len(), len);
        assert_eq!(r.element_id(ElementRef(relation)), explicit);
        assert_eq!(
            TypeRelations::default().specializes(&mut r.b, result, target, &mut 0),
            RelationFact::Yes
        );
        r.b.metadata_association_generation = Some(std::sync::Arc::new(()));
        let old = r.element_id(ElementRef(expression));
        let next = uuid::Uuid::new_v5(&uuid::Uuid::NAMESPACE_OID, b"stale result expression");
        r.override_ids(&HashMap::from([(old, next)]));
        assert_eq!(r.element_id(ElementRef(relation)), explicit);
        assert_ne!(
            TypeRelations::default().specializes(&mut r.b, result, target, &mut 0),
            RelationFact::Yes
        );
    }
    #[test]
    fn a_required_direct_redefinition_is_not_removed_by_existing_subsetting_reachability() {
        let mut r = unpublished(LIB, "feature x=Performances::Evaluation::result;");
        let e = r
            .user_elements()
            .find(|&e| r.element_type(e) == "FeatureReferenceExpression")
            .unwrap();
        r.implied_relationships(e);
        let (_, result, _) = generated(&r);
        let target = r
            .resolve_qualified("Performances::Evaluation::result")
            .unwrap();
        let target_id = r.element_id(target);
        for (kind, key) in [
            ("Subsetting", "subsettedFeature"),
            ("Redefinition", "redefinedFeature"),
        ] {
            assert!(r.b.elements[result].owned_relationships.iter().any(|&rel| {
                r.b.elements[rel].ty == kind
                    && r.b.elements[rel]
                        .props
                        .get(key)
                        .and_then(|v| v.as_reference())
                        == Some(target_id)
            }));
        }
    }
    #[test]
    fn collision_preserves_dynamic_local_and_old_result_families() {
        use crate::json::dynamic_graph::Outcome;
        let mut r = unpublished(
            LIB,
            "feature spare;feature n;feature x=n;function F {return result;}feature call=F();",
        );
        let e = r
            .user_elements()
            .find(|&e| r.element_type(e) == "FeatureReferenceExpression")
            .unwrap();
        let target = r
            .resolve_qualified("Performances::Evaluation::result")
            .unwrap();
        let spare = r.resolve_qualified("spare").unwrap();
        let result_id = uuid::Uuid::new_v5(
            &uuid::Uuid::NAMESPACE_OID,
            format!("{}/implied/ownedResult", r.element_id(e)).as_bytes(),
        );
        let collision = uuid::Uuid::new_v5(
            &uuid::Uuid::NAMESPACE_OID,
            format!("{result_id}/implied/Redefinition/{}", r.element_id(target)).as_bytes(),
        );
        r.override_ids(&HashMap::from([(r.element_id(spare), collision)]));
        r.implied_relationships(e);
        let snapshot = r.b.dynamic_graph.as_ref().unwrap();
        assert_eq!(snapshot.outcome, Outcome::Accepted);
        assert_eq!(snapshot.local_featuring_outcome, Outcome::Accepted);
        assert_eq!(
            snapshot.result_redefinition_outcome,
            Outcome::Declined(Refusal::Collision)
        );
        let result =
            r.b.semantic_ownership
                .as_ref()
                .unwrap()
                .result(e.0)
                .unwrap()
                .feature;
        assert!(
            r.b.elements[result]
                .owned_relationships
                .iter()
                .all(|&rel| r.b.elements[rel].ty != "Redefinition")
        );
    }
    #[test]
    fn exhaustion_is_nonmutating_and_a_fresh_publication_can_retry() {
        let mut r = unpublished(LIB, "feature n;feature x=n;");
        let before: Vec<_> = r.b.elements.iter().map(|e| e.id).collect();
        let mut steps = crate::eval::MAX_STEPS;
        assert!(matches!(
            prepare(&mut r.b, &[], &[], &mut steps),
            Err(Refusal::WorkLimit)
        ));
        assert_eq!(
            before,
            r.b.elements.iter().map(|e| e.id).collect::<Vec<_>>()
        );
        let e = r
            .user_elements()
            .find(|&e| r.element_type(e) == "FeatureReferenceExpression")
            .unwrap();
        r.implied_relationships(e);
        generated(&r);
    }
    #[test]
    fn result_inheritance_replays_from_fresh_cached_prepared_and_decoded_libraries() {
        use crate::{libcache::LibraryCache, prepared::PreparedLibrary};
        use std::sync::Arc;
        let mut base = Model::new();
        base.add_library_source("return-library.kerml", LIB);
        base.record_library_cache();
        ResolvedModel::build(&base);
        let cache =
            LibraryCache::from_bytes(&base.take_recorded_library_cache().unwrap().to_bytes())
                .unwrap();
        let prepared = base.prepare_library().unwrap();
        let decoded =
            Arc::new(PreparedLibrary::from_bytes(&prepared.to_bytes(93).unwrap(), 93).unwrap());
        let mut expected = None;
        for mode in 0..4 {
            let mut m = Model::new();
            match mode {
                2 => Arc::clone(&prepared).install(&mut m).unwrap(),
                3 => Arc::clone(&decoded).install(&mut m).unwrap(),
                _ => {
                    m.add_library_source("return-library.kerml", LIB);
                    if mode == 1 {
                        m.set_library_cache(cache.clone());
                    }
                }
            }
            m.add_source("return-user.kerml", "feature n;feature x=n;");
            let mut r = ResolvedModel::build(&m);
            let expr = r
                .user_elements()
                .find(|&e| r.element_type(e) == "FeatureReferenceExpression")
                .unwrap();
            r.implied_relationships(expr);
            let (_, result, relation) = generated(&r);
            let ids = (r.b.elements[result].id, r.b.elements[relation].id);
            if let Some(expected) = expected {
                assert_eq!(ids, expected);
            }
            expected = Some(ids);
        }
    }
    #[test]
    fn identity_binding_discards_and_rebuilds_the_whole_common_tail() {
        let target = uuid::Uuid::new_v5(&uuid::Uuid::NAMESPACE_OID, b"bound result referent");
        let mut r = unpublished(
            LIB,
            &format!("feature n;feature ready=n;feature later='{target}';"),
        );
        let expressions: Vec<_> = r
            .user_elements()
            .filter(|&e| r.element_type(e) == "FeatureReferenceExpression")
            .collect();
        assert_eq!(expressions.len(), 2);
        r.implied_relationships(expressions[0]);
        let from = r.b.implied.as_ref().unwrap().owned_results_from;
        let ready = r.b.elements[generated(&r).2].id;
        let n = r.resolve_qualified("n").unwrap();
        r.override_ids(&HashMap::from([(r.element_id(n), target)]));
        assert!(r.bind_id_spelled_references().contains(&target));
        assert_eq!(r.b.elements.len(), from);
        assert!(r.b.dynamic_graph.is_none());
        r.implied_relationships(expressions[0]);
        let evidence =
            r.b.dynamic_graph
                .as_ref()
                .unwrap()
                .result_redefinition
                .as_ref()
                .unwrap();
        assert_eq!(evidence.sources.len(), 2);
        assert!(
            evidence
                .relationships
                .iter()
                .any(|&rel| r.b.elements[rel].id == ready)
        );
    }
    #[test]
    fn actual_library_witness() {
        let library = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../../spec-refs/SysML-v2-Release/sysml.library");
        let mut m = Model::new();
        m.load_library_dir(&library).unwrap();
        m.add_source("return-actual.kerml", "feature n;feature x=n;");
        let mut r = ResolvedModel::build(&m);
        let e = r
            .user_elements()
            .find(|&e| r.element_type(e) == "FeatureReferenceExpression")
            .unwrap();
        r.implied_relationships(e);
        let expected = r
            .resolve_qualified("Performances::Evaluation::result")
            .unwrap()
            .0;
        assert_eq!(canonical_witness(&mut r.b, &mut 0).unwrap().1, expected);
        let (_, result, relation) = generated(&r);
        assert_eq!(
            r.b.elements[relation]
                .props
                .get("redefinedFeature")
                .and_then(|v| v.as_reference()),
            Some(r.b.elements[expected].id)
        );
        assert!(r.b.elements[result].owned_relationships.contains(&relation));
    }
}
