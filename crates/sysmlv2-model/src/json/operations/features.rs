//! Checked Feature bodies that read featuring and crossing (KerML
//! 8.3.3.3.4): `canAccess`, `isFeaturedWithin`, `isFeaturingType`,
//! `ownedCrossFeature` and `isOwnedCrossFeature`, and `isCompatibleWith`,
//! whose second way for two Features `canAccess` completes; the Cartesian
//! product reads `isCartesianProduct` and `asCartesianProduct`; and
//! `FeatureChainExpression::sourceTargetFeature` (KerML 8.3.4.8). Each
//! answers over the shared specialization, featuring and ownership
//! evidence and refuses, naming the element whose evidence was missing,
//! where that evidence is not certified.
use super::{
    OperationError, OperationExecutionSignature,
    namespaces::{self, blocked, with_stable_evidence},
    references,
};
use crate::{
    json::{
        DerivedValue, ElementRef, FeatureTypeIssue, Reference, ResolvedModel, semantic_ownership,
        structural_index::StoredStructure,
        type_relations::{RelationFact, TypeRelations},
    },
    metaclass::{conforms, is_a},
};
use std::collections::HashSet;

#[derive(Clone, Copy)]
pub(super) enum Body {
    CanAccess,
    IsFeaturedWithin,
    IsFeaturingType,
    OwnedCrossFeature,
    IsOwnedCrossFeature,
    IsCartesianProduct,
    AsCartesianProduct,
    SourceTargetFeature,
}

/// How far a compatibility question may descend through `canAccess` and
/// `isFeaturedWithin` (each of which asks compatibility of featuring types
/// in turn) before it is refused as undecided.
const MAX_DEPTH: usize = 16;

fn charge(steps: &mut usize, n: usize, effective: &'static str) -> Result<(), OperationError> {
    *steps = steps.saturating_add(n);
    if *steps > crate::eval::MAX_STEPS {
        Err(OperationError::WorkLimit { effective })
    } else {
        Ok(())
    }
}
fn argument_element(argument: &DerivedValue) -> usize {
    match argument {
        DerivedValue::Element(e) | DerivedValue::Reference(Reference::Element(e)) => e.0,
        _ => unreachable!("validated scalar element argument"),
    }
}
fn optional_element(argument: &DerivedValue) -> Option<usize> {
    match argument {
        DerivedValue::Null => None,
        other => Some(argument_element(other)),
    }
}

/// A three-valued answer. An undecided one names the element whose
/// evidence was missing, so a refusal can point at it.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Fact {
    Yes,
    No,
    Blocked(usize),
}
impl Fact {
    fn of(fact: RelationFact, blocker: usize) -> Fact {
        match fact {
            RelationFact::Yes => Fact::Yes,
            RelationFact::No => Fact::No,
            RelationFact::Unknown => Fact::Blocked(blocker),
        }
    }
    fn known(known: bool) -> Fact {
        if known { Fact::Yes } else { Fact::No }
    }
    /// `self or other()`, where a certain `Yes` on either side decides and
    /// an undecided side yields only to a `Yes` on the other.
    fn or(
        self,
        other: impl FnOnce() -> Result<Fact, OperationError>,
    ) -> Result<Fact, OperationError> {
        Ok(match self {
            Fact::Yes => Fact::Yes,
            Fact::No => other()?,
            Fact::Blocked(_) => match other()? {
                Fact::Yes => Fact::Yes,
                _ => self,
            },
        })
    }
    /// `self and other()`, where a certain `No` on either side decides and
    /// an undecided side yields only to a `No` on the other.
    fn and(
        self,
        other: impl FnOnce() -> Result<Fact, OperationError>,
    ) -> Result<Fact, OperationError> {
        Ok(match self {
            Fact::No => Fact::No,
            Fact::Yes => other()?,
            Fact::Blocked(_) => match other()? {
                Fact::No => Fact::No,
                _ => self,
            },
        })
    }
    fn value(self, effective: &'static str) -> Result<DerivedValue, OperationError> {
        match self {
            Fact::Yes => Ok(DerivedValue::Bool(true)),
            Fact::No => Ok(DerivedValue::Bool(false)),
            Fact::Blocked(element) => Err(blocked(effective, element)),
        }
    }
}

/// A declared Boolean flag; an absent flag is false, a malformed one refuses.
fn flag(
    r: &ResolvedModel,
    e: usize,
    key: &str,
    effective: &'static str,
) -> Result<bool, OperationError> {
    match r.b.elements[e].props.get(key) {
        None => Ok(false),
        Some(value) if value.is_null() => Ok(false),
        Some(value) => value.as_bool().ok_or_else(|| blocked(effective, e)),
    }
}

/// `isVariable`: declared on a Kernel Feature; on a Usage, the variability
/// verdict the checked reader certifies (`isVariable` reads the same
/// verdict as `mayTimeVary`), or undecided where it refuses.
fn is_variable(
    r: &mut ResolvedModel,
    e: usize,
    effective: &'static str,
    steps: &mut usize,
) -> Result<Option<bool>, OperationError> {
    charge(steps, 4, effective)?;
    if !is_a!(r.b.elements[e], "Usage") {
        return flag(r, e, "isVariable", effective).map(Some);
    }
    let report = r.usage_variability_report_with_budget(ElementRef(e), *steps);
    *steps = report.steps;
    charge(steps, 0, effective)?;
    Ok(report.value.ok())
}

fn featuring_types(
    r: &mut ResolvedModel,
    relations: &mut TypeRelations,
    feature: usize,
    effective: &'static str,
    steps: &mut usize,
) -> Result<Option<Vec<usize>>, OperationError> {
    let types = relations.featuring_types(&mut r.b, feature, steps);
    charge(steps, 0, effective)?;
    Ok(types)
}
fn role(
    r: &mut ResolvedModel,
    relations: &mut TypeRelations,
    name: &'static str,
    effective: &'static str,
    steps: &mut usize,
) -> Result<Option<usize>, OperationError> {
    let role = relations.library_role(&mut r.b, name, steps);
    charge(steps, 0, effective)?;
    Ok(role)
}

/// `Type::isCompatibleWith(otherType)` and the Feature override: a type is
/// compatible with another it specializes; two Features are compatible as
/// well when neither owns a feature, both redefine a common feature (the
/// other counted as its own) and this one can access the other.
fn compatible(
    r: &mut ResolvedModel,
    relations: &mut TypeRelations,
    specific: usize,
    other: usize,
    depth: usize,
    effective: &'static str,
    steps: &mut usize,
) -> Result<Fact, OperationError> {
    charge(steps, 4, effective)?;
    if depth > MAX_DEPTH {
        return Ok(Fact::Blocked(specific));
    }
    let first = Fact::of(
        relations.specializes(&mut r.b, specific, other, steps),
        specific,
    );
    charge(steps, 0, effective)?;
    if first == Fact::Yes
        || !conforms(r.b.elements[specific].ty, "Feature")
        || !conforms(r.b.elements[other].ty, "Feature")
    {
        return Ok(first);
    }
    first.or(|| second_way(r, relations, specific, other, depth, effective, steps))
}
fn second_way(
    r: &mut ResolvedModel,
    relations: &mut TypeRelations,
    specific: usize,
    other: usize,
    depth: usize,
    effective: &'static str,
    steps: &mut usize,
) -> Result<Fact, OperationError> {
    for feature in [specific, other] {
        let owns = relations.has_owned_feature(&mut r.b, feature, steps);
        charge(steps, 0, effective)?;
        match owns {
            None => return Ok(Fact::Blocked(feature)),
            Some(true) => return Ok(Fact::No),
            Some(false) => {}
        }
    }
    let mine = relations.checked_redefinition_closure(&mut r.b, specific, steps);
    charge(steps, 0, effective)?;
    let Some(mine) = mine else {
        return Ok(Fact::Blocked(specific));
    };
    let others = relations.checked_redefinition_closure(&mut r.b, other, steps);
    charge(steps, 0, effective)?;
    let Some(others) = others else {
        return Ok(Fact::Blocked(other));
    };
    charge(
        steps,
        mine.len().saturating_mul(others.len().saturating_add(1)),
        effective,
    )?;
    if !mine.iter().any(|f| *f == other || others.contains(f)) {
        return Ok(Fact::No);
    }
    can_access(r, relations, specific, other, depth + 1, effective, steps)
}

/// `Feature::canAccess(feature)`: whether `feature` is featured within one
/// of this Feature's direct or indirect featuring types. The indirect ones
/// are reached through featuring types that are Features; a Feature with
/// no featuring type stands in `Base::Anything`, at the start as in the
/// closure.
fn can_access(
    r: &mut ResolvedModel,
    relations: &mut TypeRelations,
    feature: usize,
    other: usize,
    depth: usize,
    effective: &'static str,
    steps: &mut usize,
) -> Result<Fact, OperationError> {
    charge(steps, 4, effective)?;
    if depth > MAX_DEPTH {
        return Ok(Fact::Blocked(feature));
    }
    let Some(anything) = role(r, relations, "Base::Anything", effective, steps)? else {
        return Ok(Fact::Blocked(feature));
    };
    let Some(start) = featuring_types(r, relations, feature, effective, steps)? else {
        return Ok(Fact::Blocked(feature));
    };
    let mut queue = if start.is_empty() {
        vec![anything]
    } else {
        start
    };
    let mut all = Vec::new();
    let mut seen = HashSet::new();
    let mut next = 0;
    while next < queue.len() {
        charge(steps, 2, effective)?;
        let ty = queue[next];
        next += 1;
        if !seen.insert(ty) {
            continue;
        }
        all.push(ty);
        if !conforms(r.b.elements[ty].ty, "Feature") {
            continue;
        }
        let Some(types) = featuring_types(r, relations, ty, effective, steps)? else {
            return Ok(Fact::Blocked(ty));
        };
        if types.is_empty() {
            queue.push(anything);
        } else {
            queue.extend(types);
        }
    }
    let mut result = Fact::No;
    for ty in all {
        match featured_within(r, relations, other, Some(ty), depth + 1, effective, steps)? {
            Fact::Yes => return Ok(Fact::Yes),
            Fact::No => {}
            undecided => {
                if result == Fact::No {
                    result = undecided;
                }
            }
        }
    }
    Ok(result)
}

/// `Feature::isFeaturedWithin(type)`: with no type, whether every featuring
/// type is `Base::Anything` (a Feature with none is featured in it
/// implicitly); else whether `type` is compatible with every featuring
/// type, or this Feature is variable and `type` specializes its owning
/// type, or this Feature is a chain whose first link is variable and
/// `type` specializes that link's owning type.
fn featured_within(
    r: &mut ResolvedModel,
    relations: &mut TypeRelations,
    feature: usize,
    ty: Option<usize>,
    depth: usize,
    effective: &'static str,
    steps: &mut usize,
) -> Result<Fact, OperationError> {
    charge(steps, 4, effective)?;
    if depth > MAX_DEPTH {
        return Ok(Fact::Blocked(feature));
    }
    let Some(types) = featuring_types(r, relations, feature, effective, steps)? else {
        return Ok(Fact::Blocked(feature));
    };
    let Some(ty) = ty else {
        let Some(anything) = role(r, relations, "Base::Anything", effective, steps)? else {
            return Ok(Fact::Blocked(feature));
        };
        return Ok(Fact::known(types.iter().all(|&t| t == anything)));
    };
    let mut every = Fact::Yes;
    for featuring in types {
        let fact = compatible(r, relations, ty, featuring, depth + 1, effective, steps)?;
        every = match (every, fact) {
            (_, Fact::No) | (Fact::No, _) => Fact::No,
            (Fact::Yes, fact) => fact,
            (undecided @ Fact::Blocked(_), _) => undecided,
        };
        if every == Fact::No {
            break;
        }
    }
    every
        .or(|| within_owner(r, relations, feature, ty, effective, steps))?
        .or(|| {
            let first = relations.first_chaining_feature(&mut r.b, feature, steps);
            charge(steps, 0, effective)?;
            match first {
                None => Ok(Fact::Blocked(feature)),
                Some(None) => Ok(Fact::No),
                Some(Some(first)) => within_owner(r, relations, first, ty, effective, steps),
            }
        })
}
/// `feature.isVariable and type.specializes(feature.owningType)`.
fn within_owner(
    r: &mut ResolvedModel,
    relations: &mut TypeRelations,
    feature: usize,
    ty: usize,
    effective: &'static str,
    steps: &mut usize,
) -> Result<Fact, OperationError> {
    let variable = match is_variable(r, feature, effective, steps)? {
        None => Fact::Blocked(feature),
        Some(variable) => Fact::known(variable),
    };
    variable.and(|| {
        let owning = relations.owning_type(&mut r.b, feature, steps);
        charge(steps, 0, effective)?;
        Ok(match owning {
            None => Fact::Blocked(feature),
            Some(None) => Fact::No,
            Some(Some(owner)) => Fact::of(relations.specializes(&mut r.b, ty, owner, steps), ty),
        })
    })
}

/// `Feature::isFeaturingType(type)`: an owned, nonvariable Feature's
/// featuring type is its owning type; a variable one's is the library's
/// `snapshots` feature when the owner is `Occurrences::Occurrence`, else
/// a Feature featured by the owner that redefines `snapshots`.
fn featuring_type(
    r: &mut ResolvedModel,
    relations: &mut TypeRelations,
    feature: usize,
    ty: usize,
    effective: &'static str,
    steps: &mut usize,
) -> Result<Fact, OperationError> {
    charge(steps, 4, effective)?;
    let owning = relations.owning_type(&mut r.b, feature, steps);
    charge(steps, 0, effective)?;
    let owning = match owning {
        None => return Ok(Fact::Blocked(feature)),
        Some(None) => return Ok(Fact::No),
        Some(Some(owner)) => owner,
    };
    let Some(variable) = is_variable(r, feature, effective, steps)? else {
        return Ok(Fact::Blocked(feature));
    };
    if !variable {
        return Ok(Fact::known(ty == owning));
    }
    let Some(occurrence) = role(r, relations, "Occurrences::Occurrence", effective, steps)? else {
        return Ok(Fact::Blocked(feature));
    };
    let Some(snapshots) = role(
        r,
        relations,
        "Occurrences::Occurrence::snapshots",
        effective,
        steps,
    )?
    else {
        return Ok(Fact::Blocked(feature));
    };
    if owning == occurrence {
        return Ok(Fact::known(ty == snapshots));
    }
    if !conforms(r.b.elements[ty].ty, "Feature") {
        return Ok(Fact::No);
    }
    let Some(types) = featuring_types(r, relations, ty, effective, steps)? else {
        return Ok(Fact::Blocked(ty));
    };
    if !types.contains(&owning) {
        return Ok(Fact::No);
    }
    let redefined = relations.direct_redefinitions(&mut r.b, ty, steps);
    charge(steps, 0, effective)?;
    let Some(redefined) = redefined else {
        return Ok(Fact::Blocked(ty));
    };
    Ok(Fact::known(redefined.contains(&snapshots)))
}

/// `Feature::ownedCrossFeature()`: for an end Feature of its owning type,
/// the first owned member that is a Feature other than a Multiplicity or
/// MetadataFeature and is not owned by a FeatureMembership; else null.
fn owned_cross_feature(
    r: &mut ResolvedModel,
    raw: &StoredStructure,
    relations: &mut TypeRelations,
    feature: usize,
    effective: &'static str,
    steps: &mut usize,
) -> Result<Option<usize>, OperationError> {
    charge(steps, 4, effective)?;
    if !flag(r, feature, "isEnd", effective)? {
        return Ok(None);
    }
    let owning = relations.owning_type(&mut r.b, feature, steps);
    charge(steps, 0, effective)?;
    match owning {
        None => return Err(blocked(effective, feature)),
        Some(None) => return Ok(None),
        Some(Some(_)) => {}
    }
    let memberships =
        namespaces::owned_memberships_of_namespace(&r.b, raw, feature, steps, effective)?;
    charge(steps, memberships.len(), effective)?;
    Ok(memberships
        .iter()
        .filter(|m| !is_a!(r.b.elements[m.relationship], "FeatureMembership"))
        .map(|m| m.member)
        .find(|&member| {
            let kind = r.b.elements[member].ty;
            conforms(kind, "Feature")
                && !conforms(kind, "Multiplicity")
                && !conforms(kind, "MetadataFeature")
        }))
}

/// `Feature::isOwnedCrossFeature()`: whether the owning namespace is a
/// Feature whose `ownedCrossFeature()` is this Feature.
fn is_owned_cross_feature(
    r: &mut ResolvedModel,
    raw: &StoredStructure,
    relations: &mut TypeRelations,
    feature: usize,
    effective: &'static str,
    steps: &mut usize,
) -> Result<bool, OperationError> {
    charge(steps, 4, effective)?;
    let Some(relationship) = r.b.elements[feature].owning_relationship else {
        return Ok(false);
    };
    if !is_a!(r.b.elements[relationship], "OwningMembership") {
        return Ok(false);
    }
    let owner = semantic_ownership::checked_relationship_carrier(&r.b, raw, relationship, steps)
        .ok_or_else(|| blocked(effective, feature))?;
    charge(steps, 0, effective)?;
    let Some(owner) = owner else {
        return Ok(false);
    };
    if !conforms(r.b.elements[owner].ty, "Feature") {
        return Ok(false);
    }
    Ok(owned_cross_feature(r, raw, relations, owner, effective, steps)? == Some(feature))
}

/// `Type::isCompatibleWith` (`feature` false) and the Feature override.
pub(super) fn compatible_with(
    r: &mut ResolvedModel,
    receiver: ElementRef,
    other: usize,
    feature: bool,
    effective: &'static str,
    steps: &mut usize,
) -> Result<DerivedValue, OperationError> {
    let mut relations = TypeRelations::default();
    if !feature {
        let fact = relations.specializes(&mut r.b, receiver.0, other, steps);
        charge(steps, 0, effective)?;
        return Fact::of(fact, receiver.0).value(effective);
    }
    compatible(r, &mut relations, receiver.0, other, 0, effective, steps)?.value(effective)
}

/// The checked `Feature::type` of a feature, through the shared
/// identity-based projection.
fn feature_types(
    r: &mut ResolvedModel,
    feature: usize,
    effective: &'static str,
    steps: &mut usize,
) -> Result<Vec<usize>, OperationError> {
    let report = r.feature_type_report_with_budget(ElementRef(feature), *steps);
    *steps = report.steps;
    report
        .types
        .map(|types| types.into_iter().map(|e| e.0).collect())
        .map_err(|issue| match issue {
            FeatureTypeIssue::WorkLimit => OperationError::WorkLimit { effective },
            _ => blocked(effective, feature),
        })
}

/// The checked featuring types of a feature, refusing where they are not
/// certified.
fn certified_featuring_types(
    r: &mut ResolvedModel,
    relations: &mut TypeRelations,
    feature: usize,
    effective: &'static str,
    steps: &mut usize,
) -> Result<Vec<usize>, OperationError> {
    featuring_types(r, relations, feature, effective, steps)?
        .ok_or_else(|| blocked(effective, feature))
}

/// `Feature::isCartesianProduct()`: one type and one featuring type, which,
/// when the feature itself owns it, is a Feature that is a product in turn.
fn is_cartesian_product(
    r: &mut ResolvedModel,
    relations: &mut TypeRelations,
    feature: usize,
    depth: usize,
    effective: &'static str,
    steps: &mut usize,
) -> Result<bool, OperationError> {
    if depth > MAX_DEPTH {
        return Err(blocked(effective, feature));
    }
    charge(steps, 4, effective)?;
    if feature_types(r, feature, effective, steps)?.len() != 1 {
        return Ok(false);
    }
    let featuring = certified_featuring_types(r, relations, feature, effective, steps)?;
    if featuring.len() != 1 {
        return Ok(false);
    }
    let first = featuring[0];
    if r.b.owner_elem(first) != Some(feature) {
        return Ok(true);
    }
    if !is_a!(r.b.elements[first], "Feature") {
        return Ok(false);
    }
    is_cartesian_product(r, relations, first, depth + 1, effective, steps)
}

/// `Feature::asCartesianProduct()`: the featuring types the feature does
/// not own, then the products of the Features it owns among them, then
/// its types — ordered, non-unique.
fn as_cartesian_product(
    r: &mut ResolvedModel,
    relations: &mut TypeRelations,
    feature: usize,
    depth: usize,
    effective: &'static str,
    steps: &mut usize,
    out: &mut Vec<usize>,
) -> Result<(), OperationError> {
    if depth > MAX_DEPTH {
        return Err(blocked(effective, feature));
    }
    charge(steps, 4, effective)?;
    let featuring = certified_featuring_types(r, relations, feature, effective, steps)?;
    let types = feature_types(r, feature, effective, steps)?;
    charge(
        steps,
        featuring.len().saturating_add(types.len()),
        effective,
    )?;
    let (owned, outside): (Vec<usize>, Vec<usize>) = featuring
        .into_iter()
        .partition(|&t| r.b.owner_elem(t) == Some(feature));
    out.extend(outside);
    for t in owned {
        if is_a!(r.b.elements[t], "Feature") {
            as_cartesian_product(r, relations, t, depth + 1, effective, steps, out)?;
        }
    }
    out.extend(types);
    Ok(())
}

/// `FeatureChainExpression::sourceTargetFeature()`: the first owned
/// feature of the expression's first `in` parameter, or nothing. The
/// toolkit's own lowering writes no such nested feature, so a chain
/// expression it lowered answers nothing; a lifted graph that carries one
/// answers it.
fn source_target_feature(
    r: &mut ResolvedModel,
    raw: &StoredStructure,
    expression: usize,
    effective: &'static str,
    steps: &mut usize,
) -> Result<Option<usize>, OperationError> {
    let memberships =
        namespaces::owned_memberships_of_namespace(&r.b, raw, expression, steps, effective)?;
    charge(steps, memberships.len(), effective)?;
    let input = memberships.iter().find(|membership| {
        is_a!(r.b.elements[membership.relationship], "FeatureMembership")
            && conforms(r.b.elements[membership.member].ty, "Feature")
            && r.b.elements[membership.member]
                .props
                .get("direction")
                .and_then(|value| value.as_str())
                == Some("in")
    });
    let Some(input) = input.map(|membership| membership.member) else {
        return Ok(None);
    };
    let nested = namespaces::owned_memberships_of_namespace(&r.b, raw, input, steps, effective)?;
    charge(steps, nested.len(), effective)?;
    Ok(nested
        .iter()
        .find(|membership| {
            is_a!(r.b.elements[membership.relationship], "FeatureMembership")
                && conforms(r.b.elements[membership.member].ty, "Feature")
        })
        .map(|membership| membership.member))
}

pub(super) fn invoke(
    r: &mut ResolvedModel,
    receiver: ElementRef,
    effective: &'static str,
    _signature: &OperationExecutionSignature,
    arguments: &[DerivedValue],
    body: Body,
    mut steps: usize,
) -> Result<DerivedValue, OperationError> {
    let steps = &mut steps;
    let mut relations = TypeRelations::default();
    match body {
        Body::IsCartesianProduct | Body::AsCartesianProduct | Body::SourceTargetFeature => {
            let (_, _, value) =
                with_stable_evidence(r, receiver, steps, effective, |r, raw, steps| {
                    let mut relations = TypeRelations::default();
                    Ok(match body {
                        Body::IsCartesianProduct => DerivedValue::Bool(is_cartesian_product(
                            r,
                            &mut relations,
                            receiver.0,
                            0,
                            effective,
                            steps,
                        )?),
                        Body::AsCartesianProduct => {
                            let mut out = Vec::new();
                            as_cartesian_product(
                                r,
                                &mut relations,
                                receiver.0,
                                0,
                                effective,
                                steps,
                                &mut out,
                            )?;
                            references(out)
                        }
                        _ => match source_target_feature(r, raw, receiver.0, effective, steps)? {
                            Some(nested) => {
                                DerivedValue::Reference(Reference::Element(ElementRef(nested)))
                            }
                            None => DerivedValue::Null,
                        },
                    })
                })?;
            return Ok(value);
        }
        _ => {}
    }
    match body {
        Body::IsCartesianProduct | Body::AsCartesianProduct | Body::SourceTargetFeature => {
            unreachable!("answered above")
        }
        Body::CanAccess => can_access(
            r,
            &mut relations,
            receiver.0,
            argument_element(&arguments[0]),
            0,
            effective,
            steps,
        )?
        .value(effective),
        Body::IsFeaturedWithin => featured_within(
            r,
            &mut relations,
            receiver.0,
            optional_element(&arguments[0]),
            0,
            effective,
            steps,
        )?
        .value(effective),
        Body::IsFeaturingType => featuring_type(
            r,
            &mut relations,
            receiver.0,
            argument_element(&arguments[0]),
            effective,
            steps,
        )?
        .value(effective),
        Body::OwnedCrossFeature | Body::IsOwnedCrossFeature => {
            let (_, _, value) =
                with_stable_evidence(r, receiver, steps, effective, |r, raw, steps| {
                    let mut relations = TypeRelations::default();
                    Ok(match body {
                        Body::OwnedCrossFeature => {
                            match owned_cross_feature(
                                r,
                                raw,
                                &mut relations,
                                receiver.0,
                                effective,
                                steps,
                            )? {
                                Some(cross) => {
                                    DerivedValue::Reference(Reference::Element(ElementRef(cross)))
                                }
                                None => DerivedValue::Null,
                            }
                        }
                        _ => DerivedValue::Bool(is_owned_cross_feature(
                            r,
                            raw,
                            &mut relations,
                            receiver.0,
                            effective,
                            steps,
                        )?),
                    })
                })?;
            Ok(value)
        }
    }
}
