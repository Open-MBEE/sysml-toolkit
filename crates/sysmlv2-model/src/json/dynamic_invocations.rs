//! Detached dynamic Invocation and constructor-result construction. No Builder cache, row or
//! materialized relationship is published here. The common tail transaction
//! must reserve these recipes together with result/Binding rows, validate its
//! captured semantic_batch::Snapshot, then install every view atomically.
use super::{
    Builder, membership_evidence, positional_delta,
    semantic_batch::{Edge, Plan, StaticPrefix},
    structural_index::StoredStructure,
    type_relations::{self, TypeRelations},
};
use crate::metaclass::conforms;
use std::{
    collections::{HashMap, HashSet},
    sync::Arc,
};
use uuid::Uuid;

#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) enum Refusal {
    WorkLimit,
    Incomplete,
    StaticMismatch,
    Collision,
    Stale,
}
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

fn consistent_unresolved_target(node: &super::Elem, steps: &mut usize) -> Result<bool, Refusal> {
    let mut target = None;
    for key in [
        "general",
        "superclassifier",
        "type",
        "subsettedFeature",
        "redefinedFeature",
        "referencedFeature",
        "crossedFeature",
    ] {
        charge(steps, 1)?;
        if let Some(value) = node.props.get(key) {
            let crate::properties::Atom::Object(fields) = value else {
                return Ok(false);
            };
            let Some(name) = value.get("@ref").and_then(|v| v.as_str()) else {
                return Ok(false);
            };
            charge(steps, name.len().saturating_mul(4))?;
            if fields.len() != 1
                || name.is_empty()
                || target.is_some_and(|previous| previous != value)
            {
                return Ok(false);
            }
            target = Some(value);
        }
    }
    let Some(target) = target else {
        return Ok(false);
    };
    for (key, length, index) in [("target", 1, 0), ("relatedElement", 2, 1)] {
        if let Some(value) = node.props.get(key) {
            let Some(values) = value.as_array() else {
                return Ok(false);
            };
            charge(steps, values.len())?;
            if values.len() != length || &values[index] != target {
                return Ok(false);
            }
        }
    }
    Ok(node.children.is_empty()
        && node
            .props
            .get("ownedRelatedElement")
            .is_none_or(|value| value.as_array().is_some_and(Vec::is_empty)))
}

/// Capture the immutable prefix once for this source/configuration generation.
/// Cold recipes retain the legacy emitter IDs. On a warm model, exact matching
/// graph recipes adopt the already-existing physical row IDs (including public
/// identity overrides); no rehash/replacement of a published row is permitted.
/// The caller provides a freshly produced, unshared candidate and caches only
/// the returned Arc. Existing shared prefix objects remain immutable.
pub(super) fn capture_static_prefix(
    b: &mut Builder,
    mut candidate: Arc<StaticPrefix>,
    physical_static_end: Option<usize>,
    steps: &mut usize,
) -> Result<Arc<StaticPrefix>, Refusal> {
    let raw = StoredStructure::for_query(b, steps).ok_or_else(|| incomplete(steps))?;
    if !raw.ids_unique {
        return Err(Refusal::Incomplete);
    }
    validate_fixed_prefix(b, &candidate, &raw, physical_static_end, false, steps)?;
    if physical_static_end.is_some() {
        charge(steps, candidate.rows.len())?;
        let prefix = Arc::get_mut(&mut candidate).ok_or(Refusal::Stale)?;
        for (offset, edge) in prefix.rows.iter_mut().enumerate() {
            edge.id = b.elements[prefix.authored_end + offset].id;
        }
        b.recertify_physical_static_authority(steps)
            .ok_or(Refusal::WorkLimit)?;
    }
    Ok(candidate)
}

/// Caller obtains prefix from the common static recipe source, not a historical
/// candidate list. If rows exist, their exact recipes must have been checked
/// against this prefix; a changed static prediction cannot rewrite old rows.
/// `physical_static_end` comes from ImpliedTable.owned_results_from when
/// materialized, not a length inferred from the proposed recipes.
/// `reserved` includes every other admitted semantic-tail ID. The caller must
/// reserve returned tail IDs against later result-family plans as well.
#[cfg(test)]
pub(super) fn prepare(
    b: &mut Builder,
    prefix: Arc<StaticPrefix>,
    reserved: &HashSet<Uuid>,
    physical_static_end: Option<usize>,
    steps: &mut usize,
) -> Result<Plan, Refusal> {
    prepare_with_workspace(
        b,
        prefix,
        reserved,
        physical_static_end,
        steps,
        &mut super::positional::PositionalWorkspace::default(),
    )
}

pub(super) fn prepare_with_workspace(
    b: &mut Builder,
    prefix: Arc<StaticPrefix>,
    reserved: &HashSet<Uuid>,
    physical_static_end: Option<usize>,
    steps: &mut usize,
    workspace: &mut super::positional::PositionalWorkspace,
) -> Result<Plan, Refusal> {
    charge(steps, 1)?;
    if !b.semantic_ready || prefix.authored_end != b.explicit_len() {
        return Err(Refusal::Incomplete);
    }
    let raw = StoredStructure::for_query(b, steps).ok_or_else(|| incomplete(steps))?;
    if !raw.ids_unique {
        return Err(Refusal::Incomplete);
    }
    validate_fixed_prefix(b, &prefix, &raw, physical_static_end, true, steps)?;
    let revision = b.elements.observe_revision();
    let authored = b.explicit_len();
    charge(steps, b.elements.len())?;
    let mut owners = vec![None; b.elements.len()];
    let mut conjugated = HashSet::new();
    let mut unresolved_sources = HashSet::new();
    // The legacy minimizer accepts a compatibility graph. A new positive batch
    // must not use contradictory redundant endpoints to eliminate its required
    // callee edge. Validate the authored graph through the shared typed reader.
    for (relation, owner) in owners.iter_mut().enumerate().take(authored) {
        charge(steps, 1)?;
        let node = &b.elements[relation];
        if !conforms(node.ty, "Specialization") && !conforms(node.ty, "Conjugation") {
            continue;
        }
        let carrier = if b.graph_format == crate::model::GraphFormat::CanonicalV3 {
            super::semantic_ownership::checked_relationship_carrier(b, &raw, relation, steps)
                .ok_or_else(|| incomplete(steps))?
        } else {
            Some(
                raw.carrier(b, relation)
                    .flatten()
                    .ok_or_else(|| incomplete(steps))?,
            )
        };
        *owner = carrier;
        if let Some(membership) = node.owning_relationship {
            if b.graph_format != crate::model::GraphFormat::CanonicalV3
                || !conforms(b.elements[membership].ty, "OwningMembership")
            {
                return Err(incomplete(steps));
            }
            let namespace =
                super::semantic_ownership::checked_relationship_carrier(b, &raw, membership, steps)
                    .flatten()
                    .ok_or_else(|| incomplete(steps))?;
            if !raw
                .membership_domains(b, steps)
                .is_some_and(|domains| domains.owner_complete(namespace))
                || membership_evidence::member(b, &raw, namespace, membership, steps)
                    != Some(relation)
            {
                return Err(incomplete(steps));
            }
        }
        if conforms(node.ty, "Conjugation") {
            let source_id = node
                .props
                .get("conjugatedType")
                .map(|v| v.as_reference())
                .unwrap_or_else(|| carrier.map(|owner| b.elements[owner].id))
                .ok_or_else(|| incomplete(steps))?;
            let source = raw
                .element_for_uuid(b, source_id)
                .ok_or_else(|| incomplete(steps))?;
            if !conforms(b.elements[source].ty, "Type") {
                return Err(incomplete(steps));
            }
            type_relations::endpoint_with_carrier(
                b,
                source,
                carrier,
                relation,
                &["conjugatedType"],
                &["originalType"],
                "Type",
                steps,
            )
            .ok_or_else(|| incomplete(steps))?;
            conjugated.insert(source_id);
            continue;
        }
        let source = [
            "specific",
            "subclassifier",
            "typedFeature",
            "subsettingFeature",
            "redefiningFeature",
            "referencingFeature",
            "crossingFeature",
        ]
        .iter()
        .find_map(|key| node.props.get(key))
        .map(|v| v.as_reference())
        .unwrap_or_else(|| carrier.map(|owner| b.elements[owner].id))
        .ok_or_else(|| incomplete(steps))?;
        let source = raw
            .element_for_uuid(b, source)
            .ok_or_else(|| incomplete(steps))?;
        let target_kind = if conforms(node.ty, "Subsetting") {
            "Feature"
        } else if conforms(node.ty, "Subclassification") {
            "Classifier"
        } else {
            "Type"
        };
        let source_kind = if conforms(node.ty, "Subclassification") {
            "Classifier"
        } else if conforms(node.ty, "FeatureTyping") || conforms(node.ty, "Subsetting") {
            "Feature"
        } else {
            "Type"
        };
        if !conforms(b.elements[source].ty, source_kind) {
            return Err(incomplete(steps));
        }
        // A local unresolved target cannot enter the minimizer's identity
        // graph. Canonical planning may retain an unrelated complete component,
        // but only after proving this row's source through the shared inverse
        // domain and quarantining every dependency that reaches it.
        if b.graph_format == crate::model::GraphFormat::CanonicalV3
            && (conforms(node.ty, "Subsetting") || conforms(node.ty, "FeatureTyping"))
            && super::implied::specialization_target(node).is_none()
        {
            if !consistent_unresolved_target(node, steps)? {
                return Err(incomplete(steps));
            }
            let typing = raw.typing(b, steps).ok_or_else(|| incomplete(steps))?;
            charge(steps, typing.relationships.get(&source).map_or(0, Vec::len))?;
            if typing.sources_incomplete
                || !typing
                    .relationships
                    .get(&source)
                    .is_some_and(|rows| rows.contains(&relation))
                || super::semantic_ownership::checked_relationship_carrier(b, &raw, relation, steps)
                    != Some(carrier)
            {
                return Err(incomplete(steps));
            }
            unresolved_sources.insert(source);

            continue;
        }
        type_relations::endpoint_with_carrier(
            b,
            source,
            carrier,
            relation,
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
        .ok_or_else(|| incomplete(steps))?;
    }
    let mut owning = TypeRelations::default();
    charge(steps, unresolved_sources.len())?;
    let unresolved: Vec<_> = unresolved_sources.iter().copied().collect();
    for source in unresolved {
        charge(steps, 1)?;
        // A source's immediate owning Type consumes its feature-domain
        // projection. Do not recursively lift that qualification: a nested
        // feature's signature is not the outer owner's own specialization or
        // slot direction. Actual nested consumers remain checked by the final
        // specialization/delta dependency audit.
        if !conforms(b.elements[source].ty, "Feature") {
            continue;
        }
        if let Some(owner) = owning
            .owning_type(b, source, steps)
            .ok_or_else(|| incomplete(steps))?
        {
            if unresolved_sources.insert(owner) {}
        }
    }

    charge(steps, prefix.rows.len())?;
    let mut candidates: Vec<_> = prefix
        .rows
        .iter()
        .map(|r| (r.owner, (r.kind, r.source_key, r.target_key, r.target)))
        .collect();
    let fixed = candidates.len();
    let mut required = Vec::new();
    let mut constructor_positional = HashMap::new();
    let mut unadmitted = HashSet::new();
    let mut constructor_batch = super::constructor_bindings::ConstructorBatchEvidence::default();
    for invocation in 0..authored {
        charge(steps, 1)?;
        let constructor = b.graph_format == crate::model::GraphFormat::CanonicalV3
            && b.elements[invocation].ty == "ConstructorExpression";
        let operator = b.graph_format == crate::model::GraphFormat::CanonicalV3
            && b.elements[invocation].ty == "OperatorExpression";
        if b.elements[invocation].ty != "InvocationExpression" && !constructor && !operator {
            continue;
        }
        let constructor_result = if constructor {
            Some(
                super::constructor_bindings::owned_result(b, &raw, invocation, steps)
                    .ok_or_else(|| incomplete(steps))?,
            )
        } else {
            None
        };
        let operator_target = if operator {
            let mut proposed = HashMap::new();
            match b.checked_invocation_bindings_in_batch(
                invocation,
                steps,
                Some(&mut proposed),
                &mut constructor_batch,
            ) {
                Ok(arguments) => {
                    constructor_positional.extend(proposed);
                    Some(arguments.callee.0)
                }
                Err(_) if *steps > crate::eval::MAX_STEPS => return Err(Refusal::WorkLimit),
                Err(_) => {
                    unadmitted.insert(invocation);
                    continue;
                }
            }
        } else {
            None
        };
        // Legacy publication retains whole-batch refusal. Canonical candidates
        // with a localized missing callee remain unadmitted; the final closure
        // audit prevents any accepted family from consuming their signatures.
        let target = if let Some(target) = operator_target {
            target
        } else {
            match membership_evidence::first_unowned_member(
                b,
                &raw,
                invocation,
                "FeatureMembership",
                "Type",
                None,
                steps,
            ) {
                Some(target) => target,
                None if b.graph_format == crate::model::GraphFormat::CanonicalV3
                    && *steps <= crate::eval::MAX_STEPS =>
                {
                    unadmitted.insert(invocation);
                    if let Some(result) = constructor_result {
                        unadmitted.insert(result);
                    }
                    continue;
                }
                None => {
                    return Err(incomplete(steps));
                }
            }
        };
        let id = b.elements[target].id;
        let edge = if conforms(b.elements[target].ty, "Feature") {
            ("Subsetting", "subsettingFeature", "subsettedFeature", id)
        } else {
            ("FeatureTyping", "typedFeature", "type", id)
        };
        let source = constructor_result.unwrap_or(invocation);
        if constructor {
            let mut proposed = HashMap::new();
            match b.checked_constructor_bindings_in_batch(
                invocation,
                steps,
                Some(&mut proposed),
                &mut constructor_batch,
            ) {
                Ok(_) => constructor_positional.extend(proposed),
                Err(_) => {
                    charge(steps, 0)?;
                    unadmitted.insert(invocation);
                    unadmitted.insert(source);
                    continue;
                }
            }
        }
        required.push(source);
        candidates.push((source, edge));
    }

    let (retained, mut graph) = b
        .required_specialization_edges_with_chain_bases(
            &candidates,
            fixed,
            authored,
            &owners,
            &prefix.chain_bases,
            Some(steps),
        )
        .ok_or_else(|| incomplete(steps))?;
    let mut bases = HashMap::new();
    for (&owner, targets) in &prefix.planner_bases {
        charge(steps, targets.len().saturating_add(1))?;
        bases.insert(owner, targets.clone());
    }
    charge(steps, prefix.planner_incomplete.len())?;
    let mut incomplete_bases = prefix.planner_incomplete.clone();

    let mut tail = Vec::new();
    for (index, &(source, edge)) in candidates.iter().enumerate().skip(fixed) {
        charge(steps, 1)?;
        if !retained[index] {
            continue;
        }
        let target = raw.element_for_uuid(b, edge.3).ok_or(Refusal::Incomplete)?;
        let targets = bases.entry(source).or_insert_with(Vec::new);
        charge(steps, targets.len().saturating_add(1))?;
        if !targets.contains(&target) {
            targets.push(target);
        }
        tail.push(recipe(b, source, edge));
    }
    // Every immutable positional edge visible to minimization is also visible
    // to candidate inheritance. New positional rows can in turn enable more
    // rows, so require an actual bounded fixed point, never a one-pass guess.
    let foundation = bases;
    let mut prior = Arc::clone(&prefix.positional);
    if !constructor_positional.is_empty() {
        // These pairs already have complete checked argument witnesses. Seed
        // the same fixed point with them so their consequences are considered
        // on the first pass; convergence and the immutable-prefix audit still
        // run over the full candidate graph below.
        charge(
            steps,
            prior.targets.len().saturating_add(prior.incomplete.len()),
        )?;
        for targets in prior.targets.values() {
            charge(steps, targets.len())?;
        }
        let mut seeded = (*prior).clone();
        for (&source, targets) in &constructor_positional {
            charge(steps, targets.len().saturating_add(1))?;
            if seeded
                .targets
                .get(&source)
                .is_some_and(|existing| existing != targets)
            {
                return Err(Refusal::Incomplete);
            }
            seeded.targets.insert(source, targets.clone());
        }
        prior = Arc::new(seeded);
    }
    let mut stable = None;
    for _ in 0..64 {
        let mut next_bases = HashMap::new();
        for (&owner, targets) in &foundation {
            charge(steps, targets.len().saturating_add(1))?;
            next_bases.insert(owner, targets.clone());
        }
        for (&source, targets) in &prior.targets {
            charge(steps, targets.len().saturating_add(1))?;
            let direct = next_bases.entry(source).or_insert_with(Vec::new);
            for &target in targets {
                charge(steps, direct.len().saturating_add(1))?;
                if !direct.contains(&target) {
                    direct.push(target);
                }
            }
        }
        let mut next = b
            .plan_positional_redefinitions_with_workspace(
                &next_bases,
                &incomplete_bases,
                Some(steps),
                workspace,
            )
            .ok_or_else(|| incomplete(steps))?;
        // Constructor argument ordinals use the complete public feature
        // sequence, not the generic Behavior parameter sequence. Keep these
        // checked pairs inside the same fixed point and immutable-prefix gate.
        for (&source, targets) in &constructor_positional {
            charge(steps, targets.len().saturating_add(1))?;
            if next
                .targets
                .get(&source)
                .is_some_and(|existing| existing != targets)
            {
                return Err(Refusal::Incomplete);
            }
            next.targets.insert(source, targets.clone());
        }
        let additions = positional_delta::certify(
            &prefix.positional,
            &next,
            &required,
            |source, steps| owning.owning_type(b, source, steps).flatten(),
            steps,
        )
        .map_err(|e| match e {
            positional_delta::Refusal::WorkLimit => Refusal::WorkLimit,
            _ => Refusal::Incomplete,
        })?;
        charge(
            steps,
            next.targets.len().saturating_add(next.incomplete.len()),
        )?;
        for targets in next.targets.values() {
            charge(steps, targets.len())?;
        }
        if next.targets == prior.targets && next.incomplete == prior.incomplete {
            stable = Some((next, next_bases, additions));
            break;
        }
        prior = Arc::new(next);
    }
    let (positional, mut bases, delta) = stable.ok_or(Refusal::Incomplete)?;
    // Generic positional matching includes output parameters. A newly inferred
    // Invocation input cannot be bound to an output-only parameter merely by
    // that ordinal. Full effective-input argument mapping remains separate.
    for (&source, targets) in &delta {
        charge(steps, targets.len().saturating_add(1))?;
        let owner = owning
            .owning_type(b, source, steps)
            .flatten()
            .ok_or_else(|| incomplete(steps))?;
        if !matches!(
            b.elements[owner].ty,
            "InvocationExpression" | "OperatorExpression"
        ) {
            continue;
        }
        match membership_evidence::parameter_direction(b, &raw, source, steps) {
            Some(Some("in" | "inout")) => {
                for &target in targets {
                    if !matches!(
                        membership_evidence::parameter_direction(b, &raw, target, steps),
                        Some(Some("in" | "inout"))
                    ) {
                        return Err(incomplete(steps));
                    }
                }
            }
            Some(Some("out")) => {}
            _ => return Err(incomplete(steps)),
        }
    }
    charge(
        steps,
        delta
            .len()
            .saturating_mul((usize::BITS - delta.len().max(1).leading_zeros()) as usize + 1),
    )?;
    let mut sources: Vec<_> = delta.keys().copied().collect();
    sources.sort_unstable();
    for source in sources {
        for &target in &delta[&source] {
            charge(steps, 1)?;
            tail.push(recipe(
                b,
                source,
                (
                    "Redefinition",
                    "redefiningFeature",
                    "redefinedFeature",
                    b.elements[target].id,
                ),
            ));
        }
    }
    // Publish the converged semantic direct bases and reachability graph. The
    // fixed-point planner consumed these same certified positional identities;
    // identity dedup below preserves each owner's existing semantic order.
    for (&source, targets) in &positional.targets {
        for &target in targets {
            charge(steps, 1)?;
            let direct = bases.entry(source).or_insert_with(Vec::new);
            charge(steps, direct.len().saturating_add(1))?;
            if !direct.contains(&target) {
                direct.push(target);
            }
            let direct_ids = graph.entry(b.elements[source].id).or_insert_with(Vec::new);
            charge(steps, direct_ids.len().saturating_add(1))?;
            if !direct_ids.contains(&b.elements[target].id) {
                direct_ids.push(b.elements[target].id);
            }
        }
    }
    // Audit final positional edges as well as direct callee obligations: a
    // newly mapped argument can consume a tainted owned parameter even when
    // the callee's own specialization path does not traverse that parameter.
    // Conjugation changes specialization reachability. Until the minimizer's
    // graph models that override, refuse a reachable such context rather than
    // accepting a callee obligation via the legacy raw-specialization path.
    let mut seen = HashSet::new();
    let mut todo = Vec::new();
    for &source in &required {
        charge(steps, 1)?;
        todo.push(b.elements[source].id);
    }
    for &source in delta.keys() {
        charge(steps, 1)?;
        todo.push(b.elements[source].id);
        let owner = owning
            .owning_type(b, source, steps)
            .flatten()
            .ok_or_else(|| incomplete(steps))?;
        todo.push(b.elements[owner].id);
    }
    while let Some(source) = todo.pop() {
        charge(steps, 1)?;
        if !seen.insert(source) {
            continue;
        }
        if conjugated.contains(&source) {
            return Err(Refusal::Incomplete);
        }
        // Feature::supertypes includes its final chaining Feature. The shared
        // positional base projection does not yet include that derived base;
        // accepting this context could certify an empty parameter set while
        // omitting inherited inputs. Refuse only reachable chain contexts.
        if let Some(element) = raw.element_for_uuid(b, source) {
            if unresolved_sources.contains(&element)
                || unadmitted.contains(&element)
                || raw.bad_chains.contains(&element)
            {
                return Err(Refusal::Incomplete);
            }
            let relationships = &b.elements[element].owned_relationships;
            charge(steps, relationships.len())?;
            for &relationship in relationships {
                let relation = b.elements.get(relationship).ok_or(Refusal::Incomplete)?;
                if conforms(relation.ty, "FeatureChaining") {
                    return Err(Refusal::Incomplete);
                }
            }
        }
        let next = graph.get(&source).map_or(&[][..], Vec::as_slice);
        charge(steps, next.len())?;
        todo.extend_from_slice(next);
    }
    // Missing dynamic-family coverage is not a change to the immutable static
    // positional sequence. Qualify these owners only after proving that no
    // admitted required edge or positional addition consumes their domain.
    charge(
        steps,
        unresolved_sources.len().saturating_add(unadmitted.len()),
    )?;
    incomplete_bases.extend(unresolved_sources);
    incomplete_bases.extend(unadmitted);
    let mut assigned = HashSet::new();
    for row in &prefix.rows {
        charge(steps, 1)?;
        if !assigned.insert(row.id) {
            return Err(Refusal::Collision);
        }
    }
    for row in &tail {
        charge(steps, 1)?;
        if raw.element_for_uuid(b, row.id).is_some()
            || reserved.contains(&row.id)
            || !assigned.insert(row.id)
        {
            return Err(Refusal::Collision);
        }
    }
    if !raw.is_current(b)
        || !b
            .elements
            .revision()
            .is_some_and(|now| now.same_as(&revision))
    {
        return Err(Refusal::Stale);
    }
    let mut added_bases = HashMap::<usize, Vec<usize>>::new();
    for edge in &tail {
        charge(steps, 1)?;
        let target = raw
            .element_for_uuid(b, edge.target)
            .ok_or(Refusal::Incomplete)?;
        let targets = added_bases.entry(edge.owner).or_default();
        charge(steps, targets.len().saturating_add(1))?;
        if !targets.contains(&target) {
            targets.push(target);
        }
    }
    charge(steps, required.len().saturating_add(delta.len()))?;
    let affected_owners = required.into_iter().chain(delta.keys().copied()).collect();
    Ok(Plan {
        affected_owners,
        added_bases,
        static_prefix: prefix,
        direct_bases: bases,
        incomplete_bases,
        specializations: graph,
        positional,
        tail,
    })
}
fn recipe(
    b: &Builder,
    owner: usize,
    edge: (&'static str, &'static str, &'static str, Uuid),
) -> Edge {
    let (kind, source_key, target_key, target) = edge;
    let owner_id = b.elements[owner].id;
    let id = Uuid::new_v5(
        &Uuid::NAMESPACE_OID,
        format!("{owner_id}/implied/{kind}/{target}").as_bytes(),
    );
    Edge {
        owner,
        owner_id,
        id,
        kind,
        source_key,
        target_key,
        target,
    }
}

/// Static identity gate used both before detached construction and by the final
/// transaction's snapshot check. Cold recipes cannot collide with source rows;
/// a warm prefix must be the exact already-published static relationship view.
fn validate_fixed_prefix(
    b: &mut Builder,
    prefix: &StaticPrefix,
    raw: &StoredStructure,
    physical_static_end: Option<usize>,
    require_recipe_id: bool,
    steps: &mut usize,
) -> Result<(), Refusal> {
    let authored = prefix.authored_end;
    let materialized = b.implied_from;
    if materialized.is_some() != physical_static_end.is_some()
        || physical_static_end
            .is_some_and(|end| authored.checked_add(prefix.rows.len()) != Some(end))
    {
        return Err(Refusal::StaticMismatch);
    }
    if materialized.is_some_and(|from| from != authored) {
        return Err(Refusal::StaticMismatch);
    }
    if materialized.is_none() && b.elements.len() != authored {
        return Err(Refusal::StaticMismatch);
    }
    let mut ids = HashSet::new();
    for (offset, edge) in prefix.rows.iter().enumerate() {
        charge(steps, 1)?;
        if edge.owner >= authored || b.elements[edge.owner].id != edge.owner_id {
            return Err(Refusal::StaticMismatch);
        }
        if !ids.insert(edge.id) {
            return Err(Refusal::Collision);
        }
        if materialized.is_none() {
            if raw.element_for_uuid(b, edge.id).is_some() {
                return Err(Refusal::Collision);
            }
            continue;
        }
        let index = authored
            .checked_add(offset)
            .ok_or(Refusal::StaticMismatch)?;
        let node = b.elements.get(index).ok_or(Refusal::StaticMismatch)?;
        if (require_recipe_id && node.id != edge.id)
            || node.ty != edge.kind
            || node.props.get("isImplied").and_then(|v| v.as_bool()) != Some(true)
            || !node.children.is_empty()
            || !node.owned_relationships.is_empty()
            || node.owning_relationship.is_some()
            || node
                .props
                .get(edge.source_key)
                .and_then(|v| v.as_reference())
                != Some(edge.owner_id)
            || node
                .props
                .get(edge.target_key)
                .and_then(|v| v.as_reference())
                != Some(edge.target)
        {
            return Err(Refusal::StaticMismatch);
        }
        if super::semantic_ownership::checked_relationship_carrier(b, raw, index, steps)
            != Some(Some(edge.owner))
        {
            return Err(incomplete(steps));
        }
        type_relations::endpoint_with_carrier(
            b,
            edge.owner,
            Some(edge.owner),
            index,
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
            "Type",
            steps,
        )
        .ok_or_else(|| incomplete(steps))?;
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::json::ResolvedModel;
    fn fixture(source: &str) -> ResolvedModel {
        let mut model = crate::model::Model::new();
        model.add_source("dynamic.kerml", source);
        assert!(!model.has_errors());
        ResolvedModel::build(&model)
    }
    fn static_prefix(r: &mut ResolvedModel) -> Arc<StaticPrefix> {
        r.b.static_specialization_prefix(&HashMap::new(), true, Some(&mut 0))
            .unwrap()
    }
    #[test]
    fn canonical_nested_signature_qualification_tracks_actual_consumers() {
        for (feature, succeeds) in [("feature n", true), ("in p", false)] {
            let parameter = if succeeds { "in p;" } else { "" };
            let source = format!(
                "function F {{{feature} {{feature nested redefines Missing::q;}} {parameter} return result;}} feature call=F(1);"
            );
            let mut model =
                crate::model::Model::with_graph_format(crate::model::GraphFormat::CanonicalV3);
            let parsed = model.add_source("nested-signature.kerml", &source);
            assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
            let mut r = ResolvedModel::build(&model);
            let prefix = static_prefix(&mut r);
            assert_eq!(
                prepare(&mut r.b, prefix, &HashSet::new(), None, &mut 0).is_ok(),
                succeeds,
                "{source}"
            );
        }
    }

    #[test]
    fn canonical_missing_callee_is_qualified_without_poisoning_independent_calls() {
        for format in [
            crate::model::GraphFormat::LegacyV2,
            crate::model::GraphFormat::CanonicalV3,
        ] {
            let mut model = crate::model::Model::with_graph_format(format);
            model.add_source(
                "scoped-missing-call.kerml",
                "function F {in p;} feature valid=F(1); feature missing=Missing();",
            );
            let mut r = ResolvedModel::build(&model);
            let calls: Vec<_> = r
                .elements()
                .filter(|&e| r.element_type(e) == "InvocationExpression")
                .collect();
            let prefix = static_prefix(&mut r);
            let plan = prepare(&mut r.b, prefix, &HashSet::new(), None, &mut 0);
            if format == crate::model::GraphFormat::CanonicalV3 {
                let plan = plan.unwrap();
                assert!(plan.incomplete_bases.contains(&calls[1].0));
                assert!(!plan.affected_owners.contains(&calls[1].0));
                assert!(!plan.tail.iter().any(|edge| edge.owner == calls[1].0));
                assert!(plan.affected_owners.contains(&calls[0].0));
            } else {
                assert!(plan.is_err());
            }
        }
    }
    #[test]
    fn canonical_unresolved_feature_dependencies_do_not_certify_affected_signatures() {
        for source in [
            "function F {in p redefines Missing::q;} feature call=F(1);",
            "function G {in q;} function F specializes G {in p redefines Missing::q;} feature call=F(1);",
        ] {
            let mut model =
                crate::model::Model::with_graph_format(crate::model::GraphFormat::CanonicalV3);
            let parsed = model.add_source("tainted-parameter.kerml", source);
            assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
            let mut r = ResolvedModel::build(&model);
            let prefix = static_prefix(&mut r);
            assert!(
                prepare(&mut r.b, prefix, &HashSet::new(), None, &mut 0).is_err(),
                "{source}"
            );
        }
    }
    #[test]
    fn canonical_unresolved_target_quarantine_rejects_conflicting_aliases() {
        for corruption in 0..4 {
            let mut model =
                crate::model::Model::with_graph_format(crate::model::GraphFormat::CanonicalV3);
            model.add_source("unresolved-aliases.kerml", "class Unused {feature p redefines Missing::q;} function F {return result;} feature call=F();");
            let mut r = ResolvedModel::build(&model);
            let relationship =
                r.b.elements
                    .iter()
                    .position(|e| e.ty == "Redefinition")
                    .unwrap();
            let p = r.resolve_qualified("Unused::p").unwrap();
            let f = r.resolve_qualified("F").unwrap();
            let p_id = r.element_id(p).to_string();
            let f_id = r.element_id(f).to_string();
            let (key, value) = match corruption {
                0 => ("general", serde_json::json!({"@id":f_id})),
                1 => ("target", serde_json::json!([{"@id":f_id}])),
                2 => (
                    "relatedElement",
                    serde_json::json!([{"@id":p_id},{"@ref":"Different"}]),
                ),
                _ => ("general", serde_json::json!(7)),
            };
            r.b.elements[relationship].props.insert(key, value);
            let prefix = static_prefix(&mut r);
            assert!(
                prepare(&mut r.b, prefix, &HashSet::new(), None, &mut 0).is_err(),
                "corruption {corruption}"
            );
        }
    }
    #[test]
    fn no_argument_and_argument_plans_are_detached_and_keep_static_targets() {
        for source in [
            "function F {return result;} feature call=F();",
            "function F {in p; return result;} feature call=F(1);",
        ] {
            let mut r = fixture(source);
            let f = r.resolve_qualified("F").unwrap().0;
            let inv =
                r.b.elements
                    .iter()
                    .position(|e| e.ty == "InvocationExpression")
                    .unwrap();
            let prefix = static_prefix(&mut r);
            let n = r.b.elements.len();
            let old = r.b.positional_redefinitions.clone();
            let plan =
                prepare(&mut r.b, Arc::clone(&prefix), &HashSet::new(), None, &mut 0).unwrap();
            assert_eq!(r.b.elements.len(), n);
            assert!(r.b.implied.is_none());
            assert_eq!(
                r.b.positional_redefinitions.as_ref().map(|p| &p.targets),
                old.as_ref().map(|p| &p.targets)
            );
            assert!(plan.direct_bases[&inv].contains(&f));
            assert!(
                plan.tail
                    .iter()
                    .any(|e| e.owner == inv && e.target == r.b.elements[f].id)
            );
            for (&source, old) in &prefix.positional.targets {
                assert!(plan.positional.targets[&source].starts_with(old));
            }
            if source.contains("in p") {
                let p = r.resolve_qualified("F::p").unwrap().0;
                assert!(
                    plan.tail
                        .iter()
                        .any(|e| e.kind == "Redefinition" && e.target == r.b.elements[p].id)
                );
            }
        }
    }
    #[test]
    fn failure_and_colliding_other_tail_ids_never_publish_a_prefix() {
        let mut r = fixture("function F {return result;} feature call=F();");
        let prefix = static_prefix(&mut r);
        let plan = prepare(&mut r.b, Arc::clone(&prefix), &HashSet::new(), None, &mut 0).unwrap();
        let n = r.b.elements.len();
        let collision = HashSet::from([plan.tail[0].id]);
        assert!(matches!(
            prepare(&mut r.b, Arc::clone(&prefix), &collision, None, &mut 0),
            Err(Refusal::Collision)
        ));
        let mut exhausted = crate::eval::MAX_STEPS;
        assert!(matches!(
            prepare(
                &mut r.b,
                Arc::clone(&prefix),
                &HashSet::new(),
                None,
                &mut exhausted
            ),
            Err(Refusal::WorkLimit)
        ));
        assert_eq!(r.b.elements.len(), n);
        assert!(r.b.implied.is_none());
        assert!(prepare(&mut r.b, prefix, &HashSet::new(), None, &mut 0).is_ok());
        let mut bad = fixture(
            "function F {return result;} feature firstCall=F(); feature otherCall=missing();",
        );
        let p = static_prefix(&mut bad);
        let n = bad.b.elements.len();
        assert!(matches!(
            prepare(&mut bad.b, p, &HashSet::new(), None, &mut 0),
            Err(Refusal::Incomplete)
        ));
        assert_eq!(bad.b.elements.len(), n);
    }
    #[test]
    fn warmed_static_row_mismatch_is_not_repaired_by_dynamic_admission() {
        let mut r = fixture(
            "class A; class B specializes A; function F {return result;} feature call=F();",
        );
        let p = static_prefix(&mut r);
        r.ensure_implied();
        r.discard_owned_result_tail();
        let boundary = r.b.implied.as_ref().unwrap().owned_results_from;
        assert!(
            prepare(
                &mut r.b,
                Arc::clone(&p),
                &HashSet::new(),
                Some(boundary),
                &mut 0
            )
            .is_ok()
        );
        assert!(matches!(
            prepare(&mut r.b, p, &HashSet::new(), Some(boundary + 1), &mut 0),
            Err(Refusal::StaticMismatch)
        ));
    }
    #[test]
    fn contradictory_authored_path_cannot_discharge_a_dynamic_requirement() {
        let mut r = fixture(
            "class A; class B specializes A; function F {return result;} feature call=F();",
        );
        let p = static_prefix(&mut r);
        let b = r.resolve_qualified("B").unwrap().0;
        let relation = r.b.elements[b]
            .owned_relationships
            .iter()
            .copied()
            .find(|&i| conforms(r.b.elements[i].ty, "Specialization"))
            .unwrap();
        let conflicting = r.b.elements[b].id.to_string();
        r.b.elements[relation]
            .props
            .insert("target", serde_json::json!([{"@id":conflicting}]));
        assert!(matches!(
            prepare(&mut r.b, p, &HashSet::new(), None, &mut 0),
            Err(Refusal::Incomplete)
        ));
    }
}

#[cfg(test)]
mod indirect_tests {
    use super::*;
    use crate::json::{Elem, ResolvedModel};
    #[test]
    fn eliminated_callee_edge_still_exposes_its_static_positional_path() {
        let mut model = crate::model::Model::new();
        model.add_source("indirect.kerml", "function T {in z; return result;} function Base {in p:T; return result;} function Child specializes Base {in q; return result;} feature call=Base::p(1);");
        assert!(!model.has_errors());
        let mut r = ResolvedModel::build(&model);
        let p = r.resolve_qualified("Base::p").unwrap().0;
        let q = r.resolve_qualified("Child::q").unwrap().0;
        let z = r.resolve_qualified("T::z").unwrap().0;
        let invocation =
            r.b.elements
                .iter()
                .position(|e| e.ty == "InvocationExpression")
                .unwrap();
        // Exercise the effective-end positional rule through the indirect path.
        // Ordinary parameter pairing deliberately uses a direct base's OWNED
        // parameters, so an argument→T.z expectation alone would be incorrect.
        // These two flags make this a graph-level end-pairing control.
        let argument =
            r.b.owned_member_elems(invocation, true)
                .into_iter()
                .find(|&e| r.b.is_parameter(e))
                .unwrap();
        r.b.elements[argument]
            .props
            .insert("isEnd", serde_json::json!(true));
        r.b.elements[z]
            .props
            .insert("isEnd", serde_json::json!(true));
        let source_id = r.b.elements[invocation].id;
        let q_id = r.b.elements[q].id;
        let mut props = crate::properties::Properties::new();
        props.insert(
            "subsettingFeature",
            serde_json::json!({"@id":source_id.to_string()}),
        );
        props.insert(
            "subsettedFeature",
            serde_json::json!({"@id":q_id.to_string()}),
        );
        let relation = r.b.elements.len();
        r.b.elements.push(Elem {
            ty: "Subsetting",
            id: Uuid::new_v5(&Uuid::NAMESPACE_OID, b"dynamic indirect test"),
            path: String::new(),
            path_parent: None,
            props,
            owned_relationships: Default::default(),
            children: Default::default(),
            owning_relationship: None,
        });
        r.b.elements[invocation].owned_relationships.push(relation);
        r.b.supported_implied = None;
        r.b.positional_redefinitions = None;
        r.b.reset_lookup_caches();
        let prefix =
            r.b.static_specialization_prefix(&HashMap::new(), true, Some(&mut 0))
                .unwrap();
        assert!(
            prefix
                .positional
                .targets
                .get(&q)
                .is_some_and(|targets| targets.contains(&p))
        );
        let n = r.b.elements.len();
        let plan = prepare(&mut r.b, prefix, &HashSet::new(), None, &mut 0).unwrap();
        assert!(
            !plan
                .tail
                .iter()
                .any(|edge| edge.owner == invocation && edge.target == r.b.elements[p].id),
            "actual immutable q→p path discharges the direct callee requirement"
        );
        assert!(
            plan.direct_bases
                .get(&q)
                .is_some_and(|targets| targets.contains(&p))
        );
        assert!(
            plan.tail.iter().any(|edge| edge.owner == argument
                && edge.kind == "Redefinition"
                && edge.target == r.b.elements[z].id),
            "effective-end pairing must see the actual indirect path"
        );
        assert_eq!(r.b.elements.len(), n);
    }
}

#[cfg(test)]
mod warm_prefix_tests {
    use super::*;
    use crate::json::ResolvedModel;
    fn fixture() -> ResolvedModel {
        let mut model = crate::model::Model::new();
        model.add_library_source("performances.kerml", "standard library package Performances { function Evaluation {return result;} feature evaluations : Evaluation; }");
        model.add_source(
            "user.kerml",
            "function F {return result;} feature call=F();",
        );
        assert!(!model.has_errors());
        ResolvedModel::build(&model)
    }
    fn predicted(r: &mut ResolvedModel) -> Arc<StaticPrefix> {
        let names =
            r.b.lib_qnames
                .iter()
                .map(|(id, qn)| (qn.join("::"), *id))
                .collect();
        r.b.static_specialization_prefix(&names, true, Some(&mut 0))
            .unwrap()
    }
    #[test]
    fn public_row_id_override_keeps_physical_static_identity() {
        let mut r = fixture();
        let initial = predicted(&mut r);
        assert!(!initial.rows.is_empty());
        r.ensure_implied();
        r.discard_owned_result_tail();
        let old = initial.rows[0].id;
        let new = Uuid::new_v5(&Uuid::NAMESPACE_OID, b"overridden static prefix row");
        r.override_ids(&HashMap::from([(old, new)]));
        let boundary = r.b.implied.as_ref().unwrap().owned_results_from;
        let proposed = predicted(&mut r);
        let captured = capture_static_prefix(&mut r.b, proposed, Some(boundary), &mut 0).unwrap();
        assert_eq!(captured.rows[0].id, new);
        assert_eq!(r.b.elements[captured.authored_end].id, new);
        assert!(prepare(&mut r.b, captured, &HashSet::new(), Some(boundary), &mut 0).is_ok());
    }
    #[test]
    fn warm_generic_alias_corruption_cannot_be_recaptured() {
        let mut r = fixture();
        let p = predicted(&mut r);
        r.ensure_implied();
        r.discard_owned_result_tail();
        let boundary = r.b.implied.as_ref().unwrap().owned_results_from;
        let f = r.resolve_qualified("F").unwrap();
        let wrong = r.element_id(f).to_string();
        r.b.elements[p.authored_end]
            .props
            .insert("target", serde_json::json!([{"@id":wrong}]));
        let proposed = predicted(&mut r);
        assert!(capture_static_prefix(&mut r.b, proposed, Some(boundary), &mut 0).is_err());
    }
    #[test]
    fn unrelated_unresolved_specialization_is_an_explicit_batch_limit() {
        let mut model = crate::model::Model::new();
        model.add_source(
            "user.kerml",
            "class Unused specializes Missing; function F {return result;} feature call=F();",
        );
        assert!(!model.has_errors());
        let mut r = ResolvedModel::build(&model);
        let prefix = predicted(&mut r);
        assert!(matches!(
            prepare(&mut r.b, prefix, &HashSet::new(), None, &mut 0),
            Err(Refusal::Incomplete)
        ));
        assert!(r.b.implied.is_none());
    }
}

#[cfg(test)]
mod named_callee_chain_gap_tests {
    use super::*;
    use crate::{
        json::{ResolvedModel, id_ref},
        model::Model,
    };
    fn fixture(call: &str) -> ResolvedModel {
        let mut m = Model::new();
        let source = format!(
            "function F {{in p; return r;}} class Holder {{feature fnMember : F;}} feature h : Holder; feature chain chains h.fnMember; feature indirect :> chain; feature safe=F(1); feature call = {call}(1);"
        );
        let result = m.add_source("chain.kerml", &source);
        assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);
        ResolvedModel::build(&m)
    }
    fn plan(r: &mut ResolvedModel, steps: &mut usize) -> Result<Plan, Refusal> {
        let prefix =
            r.b.static_specialization_prefix(&HashMap::new(), true, Some(&mut 0))
                .unwrap();
        prepare(&mut r.b, prefix, &HashSet::new(), None, steps)
    }
    #[test]
    fn named_chain_callee_cannot_certify_empty_inputs() {
        for call in ["chain", "indirect"] {
            let mut r = fixture(call);
            let before = r.b.elements.len();
            assert!(
                matches!(plan(&mut r, &mut 0), Err(Refusal::Incomplete)),
                "{call}"
            );
            assert_eq!(r.b.elements.len(), before);
            assert!(r.b.implied.is_none());
        }
    }
    #[test]
    fn malformed_cyclic_and_inverse_chain_evidence_cannot_hide_from_guard() {
        for mode in 0..5 {
            let mut r = fixture("chain");
            let chain = r.resolve_qualified("chain").unwrap().0;
            let indirect = r.resolve_qualified("indirect").unwrap().0;
            let first = r.b.elements[chain]
                .owned_relationships
                .iter()
                .copied()
                .find(|&e| r.b.elements[e].ty == "FeatureChaining")
                .unwrap();
            match mode {
                0 => r.b.set(first, "chainingFeature", serde_json::json!(null)),
                1 => {
                    let id = r.b.elements[chain].id;
                    r.b.set(first, "chainingFeature", id_ref(id));
                }
                2 => {
                    let id = r.b.elements[indirect].id;
                    r.b.set(first, "featureChained", id_ref(id));
                }
                3 => r.b.elements[chain].owned_relationships.push(first),
                4 => {
                    // The declared source remains chain, but only another
                    // Feature carries the row: inverse bad_chains must refuse.
                    let id = r.b.elements[chain].id;
                    r.b.set(first, "featureChained", id_ref(id));
                    r.b.elements[chain].owned_relationships = Vec::new().into();
                    r.b.elements[indirect].owned_relationships.push(first);
                    let id = r.b.elements[indirect].id;
                    r.b.set(first, "owningRelatedElement", id_ref(id));
                }
                _ => unreachable!(),
            }
            assert!(
                matches!(plan(&mut r, &mut 0), Err(Refusal::Incomplete)),
                "mode {mode}"
            );
        }
    }
    #[test]
    fn unrelated_chains_preserve_valid_inputs_and_budget_retry() {
        let mut r = fixture("F");
        let p = r.resolve_qualified("F::p").unwrap().0;
        let mut exhausted = crate::eval::MAX_STEPS;
        assert!(matches!(
            plan(&mut r, &mut exhausted),
            Err(Refusal::WorkLimit)
        ));
        let accepted = plan(&mut r, &mut 0).unwrap();
        assert_eq!(
            accepted
                .tail
                .iter()
                .filter(|e| e.kind == "Redefinition" && e.target == r.b.elements[p].id)
                .count(),
            2
        );
        let n = r.b.elements.len();
        assert!(r.b.implied.is_none());
        assert!(plan(&mut r, &mut 0).is_ok());
        assert_eq!(r.b.elements.len(), n);
    }
}

#[cfg(test)]
mod input_direction_tests {
    use super::*;
    use crate::{
        json::{ElementRef, ResolvedModel, id_ref},
        model::Model,
    };
    fn fixture(parameters: &str, arguments: &str) -> ResolvedModel {
        let mut model = Model::new();
        let parsed = model.add_source(
            "directions.kerml",
            &format!("function F {{{parameters} return r;}} feature call=F({arguments});"),
        );
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        ResolvedModel::build(&model)
    }
    fn plan(r: &mut ResolvedModel, steps: &mut usize) -> Result<Plan, Refusal> {
        let prefix =
            r.b.static_specialization_prefix(&HashMap::new(), true, Some(&mut 0))
                .unwrap();
        prepare(&mut r.b, prefix, &HashSet::new(), None, steps)
    }
    #[test]
    fn output_before_input_refuses_entire_new_batch() {
        let mut r = fixture("out ignored; in p;", "1");
        let rows = r.b.elements.len();
        assert!(matches!(plan(&mut r, &mut 0), Err(Refusal::Incomplete)));
        assert_eq!(r.b.elements.len(), rows);
        assert!(r.b.implied.is_none());
        let call =
            r.b.elements
                .iter()
                .position(|e| e.ty == "InvocationExpression")
                .unwrap();
        let emitted = r.implied_relationships(ElementRef(call));
        assert!(
            !emitted
                .iter()
                .any(|e| r.b.elements[e.0].ty == "FeatureTyping")
        );
        assert!(r.feature_type_report(ElementRef(call)).function.is_err());
    }
    #[test]
    fn input_inout_and_named_argument_controls_preserve_correct_identity() {
        for (params, args) in [
            ("in p; out ignored;", "1"),
            ("inout p; out ignored;", "1"),
            ("out ignored; in p;", "p=1"),
        ] {
            let mut r = fixture(params, args);
            let p = r.resolve_qualified("F::p").unwrap().0;
            let ignored = r.resolve_qualified("F::ignored").unwrap().0;
            let accepted = plan(&mut r, &mut 0).unwrap();
            assert!(
                !accepted
                    .tail
                    .iter()
                    .any(|e| e.kind == "Redefinition" && e.target == r.b.elements[ignored].id)
            );
            if args == "1" {
                assert!(
                    accepted
                        .tail
                        .iter()
                        .any(|e| e.kind == "Redefinition" && e.target == r.b.elements[p].id)
                );
            }
        }
    }
    #[test]
    fn default_direction_needs_exact_membership_evidence_and_malformed_values_refuse() {
        for bad in 0..5 {
            let mut r = fixture("in p;", "1");
            let p = r.resolve_qualified("F::p").unwrap().0;
            let membership = r.b.elements[p].owning_relationship.unwrap();
            r.b.elements[membership].ty = "ParameterMembership";
            match bad {
                0 => {
                    r.b.elements[p]
                        .props
                        .entries
                        .make_mut()
                        .retain(|(key, _)| key.name() != "direction");
                }
                1 => r.b.set(p, "direction", serde_json::json!(null)),
                2 => r.b.set(p, "direction", serde_json::json!("invalid")),
                3 => {
                    let id = r.b.elements[membership].id;
                    r.b.set(membership, "ownedMemberParameter", id_ref(id));
                }
                4 => {
                    r.b.elements[p]
                        .props
                        .entries
                        .make_mut()
                        .retain(|(key, _)| key.name() != "direction");
                    r.b.elements[p].owning_relationship = None;
                }
                _ => unreachable!(),
            }
            if bad == 4 {
                // The legacy positional selector omits this malformed member,
                // so no new edge reaches the direction guard. The shared
                // direction witness must still refuse its broken reciprocity;
                // full Invocation input cardinality is a separate obligation.
                let raw = StoredStructure::for_query(&mut r.b, &mut 0).unwrap();
                assert!(membership_evidence::parameter_direction(&r.b, &raw, p, &mut 0).is_none());
            } else {
                let result = plan(&mut r, &mut 0);
                assert_eq!(result.is_ok(), bad == 0, "case {bad}");
            }
        }
    }
    #[test]
    fn ordinary_null_direction_cannot_admit_an_input_redefinition() {
        let mut r = fixture("in p;", "1");
        let p = r.resolve_qualified("F::p").unwrap().0;
        let membership = r.b.elements[p].owning_relationship.unwrap();
        assert_eq!(r.b.elements[membership].ty, "FeatureMembership");
        r.b.set(p, "direction", serde_json::json!(null));
        let raw = StoredStructure::for_query(&mut r.b, &mut 0).unwrap();
        assert_eq!(
            membership_evidence::parameter_direction(&r.b, &raw, p, &mut 0),
            Some(None)
        );
        // A plan may omit the undirected target altogether. It must never
        // accept it as an input argument; arity is a separate certificate.
        if let Ok(accepted) = plan(&mut r, &mut 0) {
            assert!(
                !accepted
                    .tail
                    .iter()
                    .any(|e| e.kind == "Redefinition" && e.target == r.b.elements[p].id)
            );
        }
    }
    #[test]
    fn exhausted_direction_admission_retries_without_partial_rows() {
        let mut r = fixture("in p;", "1");
        let mut steps = crate::eval::MAX_STEPS;
        assert!(matches!(plan(&mut r, &mut steps), Err(Refusal::WorkLimit)));
        assert!(r.b.implied.is_none());
        assert!(plan(&mut r, &mut 0).is_ok());
    }
}
