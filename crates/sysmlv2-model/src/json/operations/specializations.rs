//! Checked Type and Feature bodies that read the specialization structure
//! (KerML 8.3.3.1.10, 8.3.3.3.4): `Type::specializesFromLibrary` and
//! `multiplicities`, `Feature::redefines`, `redefinesFromLibrary`,
//! `subsetsChain` and `typingFeatures`. Each answers over the shared
//! specialization, ownership, chaining and resolution evidence and
//! refuses, naming the element whose evidence was missing, where that
//! evidence is not certified.
use super::{
    OperationError, OperationExecutionSignature, argument_element,
    namespaces::{self, blocked, owned_memberships_of_namespace, resolution, with_stable_evidence},
    references,
};
use crate::{
    json::{
        DerivedValue, ElementRef, ResolvedModel, semantic_ownership,
        structural_index::StoredStructure,
        type_relations::{self, TypeRelations},
    },
    metaclass::{conforms, is_a},
};
use std::collections::HashSet;

#[derive(Clone, Copy)]
pub(super) enum Body {
    SpecializesFromLibrary,
    Multiplicities,
    Redefines,
    RedefinesFromLibrary,
    SubsetsChain,
    TypingFeatures,
}

fn charge(steps: &mut usize, n: usize, effective: &'static str) -> Result<(), OperationError> {
    *steps = steps.saturating_add(n);
    if *steps > crate::eval::MAX_STEPS {
        Err(OperationError::WorkLimit { effective })
    } else {
        Ok(())
    }
}
/// The refusal for evidence `element` lacks: the work limit once the
/// budget is spent, else an incomplete answer naming the element.
fn incomplete(steps: &usize, effective: &'static str, element: usize) -> OperationError {
    if *steps > crate::eval::MAX_STEPS {
        OperationError::WorkLimit { effective }
    } else {
        blocked(effective, element)
    }
}

/// The member a library-qualified name resolves to from the global
/// namespace (`Namespace::resolveGlobal`), or nothing.
fn library_member(
    r: &mut ResolvedModel,
    raw: &StoredStructure,
    receiver: usize,
    argument: &DerivedValue,
    signature: &OperationExecutionSignature,
    effective: &'static str,
    steps: &mut usize,
) -> Result<Option<usize>, OperationError> {
    let DerivedValue::Str(name) = argument else {
        unreachable!("validated string")
    };
    charge(steps, name.len(), effective)?;
    let (_, names) = namespaces::qualified_names(name, effective, signature, steps)?;
    Ok(
        resolution::resolve_segments(r, raw, true, receiver, &names, steps, effective)?
            .map(|membership| membership.member),
    )
}

/// `Feature::redefines(f)`: `f` is a target of the receiver's owned
/// redefinitions, the written ones and the positional ones the
/// specification implies (the closure `allRedefinedFeatures` opens with).
fn redefines(
    r: &mut ResolvedModel,
    relations: &mut TypeRelations,
    receiver: usize,
    target: usize,
    effective: &'static str,
    steps: &mut usize,
) -> Result<bool, OperationError> {
    let targets = relations.direct_redefinitions(&mut r.b, receiver, steps);
    let targets = targets.ok_or_else(|| incomplete(steps, effective, receiver))?;
    Ok(targets.contains(&target))
}

/// The chaining features of `feature`, in order; empty for a feature that
/// is not a chain.
pub(super) fn chaining_features(
    r: &mut ResolvedModel,
    raw: &StoredStructure,
    feature: usize,
    effective: &'static str,
    steps: &mut usize,
) -> Result<Vec<usize>, OperationError> {
    let rows = semantic_ownership::owned_relationships(&r.b, feature)
        .ok_or_else(|| blocked(effective, feature))?;
    charge(steps, rows.len(), effective)?;
    let rows: Vec<usize> = rows.iter().collect();
    let mut chain = Vec::new();
    for relationship in rows {
        if !conforms(r.b.elements[relationship].ty, "FeatureChaining") {
            continue;
        }
        if raw.bad_chains.contains(&feature) {
            return Err(blocked(effective, feature));
        }
        let target = type_relations::endpoint(
            &mut r.b,
            feature,
            relationship,
            &["featureChained"],
            &["chainingFeature"],
            "Feature",
            steps,
        );
        chain.push(target.ok_or_else(|| incomplete(steps, effective, feature))?);
    }
    Ok(chain)
}

/// Whether `feature` is a chain whose last two chaining features are
/// `first` and `second`.
fn ends_in(
    r: &mut ResolvedModel,
    raw: &StoredStructure,
    feature: usize,
    first: usize,
    second: usize,
    effective: &'static str,
    steps: &mut usize,
) -> Result<bool, OperationError> {
    if !is_a!(r.b.elements[feature], "Feature") {
        return Ok(false);
    }
    let chain = chaining_features(r, raw, feature, effective, steps)?;
    Ok(chain.len() >= 2 && chain[chain.len() - 2] == first && chain[chain.len() - 1] == second)
}

/// `Feature::subsetsChain(first, second)`: a supertype of the receiver
/// (itself included) is a chain whose last two chaining features are
/// `first` and `second`. A witness among the written supertypes answers
/// true without a complete closure; the absence of one needs the complete
/// closure of the bases.
fn subsets_chain(
    r: &mut ResolvedModel,
    raw: &StoredStructure,
    receiver: usize,
    first: usize,
    second: usize,
    effective: &'static str,
    steps: &mut usize,
) -> Result<bool, OperationError> {
    let mut relations = TypeRelations::default();
    let mut seen = HashSet::from([receiver]);
    let mut queue = vec![receiver];
    while let Some(current) = queue.pop() {
        charge(steps, 1, effective)?;
        if ends_in(r, raw, current, first, second, effective, steps)? {
            return Ok(true);
        }
        if let Ok(written) = relations.checked_supertypes(&mut r.b, current, true, steps) {
            for target in written {
                if seen.insert(target) {
                    queue.push(target);
                }
            }
        }
    }
    for supertype in super::supertype_closure(r, receiver, effective, steps)? {
        if ends_in(r, raw, supertype, first, second, effective, steps)? {
            return Ok(true);
        }
    }
    Ok(false)
}

fn push_once(list: &mut Vec<usize>, element: usize) {
    if !list.contains(&element) {
        list.push(element);
    }
}

/// `Feature::typingFeatures()`: the original type of a conjugated feature
/// when that is a feature; else the targets of the feature's subsettings
/// other than cross subsettings — the written ones, a reference
/// subsetting's referenced feature among them, then the implied library
/// roles and the positional redefinitions the planner certifies — and, for
/// a chain, its last chaining feature.
fn typing_features(
    r: &mut ResolvedModel,
    raw: &StoredStructure,
    receiver: usize,
    effective: &'static str,
    steps: &mut usize,
) -> Result<Vec<usize>, OperationError> {
    let mut relations = TypeRelations::default();
    match relations.owned_conjugation(&mut r.b, receiver, steps) {
        None => return Err(incomplete(steps, effective, receiver)),
        Some(Some(original)) => {
            return Ok(if is_a!(r.b.elements[original], "Feature") {
                vec![original]
            } else {
                Vec::new()
            });
        }
        Some(None) => {}
    }
    // The complete direct bases certify the implied and positional evidence
    // the list is assembled from.
    let bases = relations.complete_direct_bases(&mut r.b, receiver, steps);
    bases.ok_or_else(|| incomplete(steps, effective, receiver))?;
    let mut out = Vec::new();
    let rows = semantic_ownership::owned_relationships(&r.b, receiver)
        .ok_or_else(|| blocked(effective, receiver))?;
    charge(steps, rows.len(), effective)?;
    let rows: Vec<usize> = rows.iter().collect();
    for relationship in rows {
        let kind = r.b.elements[relationship].ty;
        if !conforms(kind, "Subsetting") || conforms(kind, "CrossSubsetting") {
            continue;
        }
        let target = type_relations::endpoint(
            &mut r.b,
            receiver,
            relationship,
            &[
                "specific",
                "subsettingFeature",
                "redefiningFeature",
                "referencingFeature",
            ],
            &[
                "general",
                "subsettedFeature",
                "redefinedFeature",
                "referencedFeature",
            ],
            "Feature",
            steps,
        );
        push_once(
            &mut out,
            target.ok_or_else(|| incomplete(steps, effective, receiver))?,
        );
    }
    let retained = r.b.retained_typing_edges(steps);
    let retained = retained.ok_or_else(|| incomplete(steps, effective, receiver))?;
    if let Some(edges) = retained.get(&receiver) {
        charge(steps, edges.len(), effective)?;
        for &(kind, id) in edges {
            if !conforms(kind, "Subsetting") || conforms(kind, "CrossSubsetting") {
                continue;
            }
            let target = raw
                .element_for_uuid(&r.b, id)
                .ok_or_else(|| blocked(effective, receiver))?;
            push_once(&mut out, target);
        }
    }
    if let Some(owner) = r.b.owner_elem(receiver) {
        let positional = r.b.positional_redefinition_targets(receiver, owner);
        charge(steps, positional.len(), effective)?;
        for target in positional {
            if target != receiver {
                push_once(&mut out, target);
            }
        }
    }
    if let Some(&last) = chaining_features(r, raw, receiver, effective, steps)?.last() {
        push_once(&mut out, last);
    }
    Ok(out)
}

/// The one Multiplicity among a type's owned members (`Type::multiplicity`),
/// if any; two refuse.
fn own_multiplicity(
    r: &ResolvedModel,
    raw: &StoredStructure,
    ty: usize,
    effective: &'static str,
    steps: &mut usize,
) -> Result<Option<usize>, OperationError> {
    let memberships = owned_memberships_of_namespace(&r.b, raw, ty, steps, effective)?;
    let mut found = None;
    for membership in memberships {
        if is_a!(r.b.elements[membership.relationship], "OwningMembership")
            && is_a!(r.b.elements[membership.member], "Multiplicity")
            && found.replace(membership.member).is_some()
        {
            return Err(blocked(effective, ty));
        }
    }
    Ok(found)
}

/// `Type::multiplicities()`: the type's own multiplicity, else those of the
/// nearest supertypes that have one, reached through the complete direct
/// bases and stopping at each type that has its own.
fn multiplicities(
    r: &mut ResolvedModel,
    raw: &StoredStructure,
    receiver: usize,
    effective: &'static str,
    steps: &mut usize,
) -> Result<Vec<usize>, OperationError> {
    if let Some(own) = own_multiplicity(r, raw, receiver, effective, steps)? {
        return Ok(vec![own]);
    }
    let mut relations = TypeRelations::default();
    let mut out = Vec::new();
    let mut seen = HashSet::from([receiver]);
    let bases = relations.complete_direct_bases(&mut r.b, receiver, steps);
    let mut stack: Vec<usize> = bases
        .ok_or_else(|| incomplete(steps, effective, receiver))?
        .into_iter()
        .rev()
        .collect();
    while let Some(ty) = stack.pop() {
        charge(steps, 1, effective)?;
        if !seen.insert(ty) {
            continue;
        }
        match own_multiplicity(r, raw, ty, effective, steps)? {
            Some(multiplicity) => push_once(&mut out, multiplicity),
            None => {
                let bases = relations.complete_direct_bases(&mut r.b, ty, steps);
                let bases = bases.ok_or_else(|| incomplete(steps, effective, ty))?;
                stack.extend(bases.into_iter().rev());
            }
        }
    }
    Ok(out)
}

pub(super) fn invoke(
    r: &mut ResolvedModel,
    receiver: ElementRef,
    effective: &'static str,
    signature: &OperationExecutionSignature,
    arguments: &[DerivedValue],
    body: Body,
    mut steps: usize,
) -> Result<DerivedValue, OperationError> {
    let steps = &mut steps;
    let (_, _, value) = with_stable_evidence(r, receiver, steps, effective, |r, raw, steps| {
        let mut relations = TypeRelations::default();
        Ok(match body {
            Body::SpecializesFromLibrary => {
                match library_member(
                    r,
                    raw,
                    receiver.0,
                    &arguments[0],
                    signature,
                    effective,
                    steps,
                )? {
                    Some(general) if is_a!(r.b.elements[general], "Type") => {
                        let fact = relations.specializes(&mut r.b, receiver.0, general, steps);
                        super::relation_fact(fact, receiver, effective, steps)?
                    }
                    _ => DerivedValue::Bool(false),
                }
            }
            Body::RedefinesFromLibrary => {
                match library_member(
                    r,
                    raw,
                    receiver.0,
                    &arguments[0],
                    signature,
                    effective,
                    steps,
                )? {
                    Some(target) if is_a!(r.b.elements[target], "Feature") => DerivedValue::Bool(
                        redefines(r, &mut relations, receiver.0, target, effective, steps)?,
                    ),
                    _ => DerivedValue::Bool(false),
                }
            }
            Body::Redefines => DerivedValue::Bool(redefines(
                r,
                &mut relations,
                receiver.0,
                argument_element(&arguments[0]),
                effective,
                steps,
            )?),
            Body::SubsetsChain => DerivedValue::Bool(subsets_chain(
                r,
                raw,
                receiver.0,
                argument_element(&arguments[0]),
                argument_element(&arguments[1]),
                effective,
                steps,
            )?),
            Body::TypingFeatures => {
                references(typing_features(r, raw, receiver.0, effective, steps)?)
            }
            Body::Multiplicities => {
                references(multiplicities(r, raw, receiver.0, effective, steps)?)
            }
        })
    })?;
    Ok(value)
}
