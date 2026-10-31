//! Checked SysML usage bodies that read a usage's place in its owner
//! (SysML 8.3.9, 8.3.16, 8.3.17): `ActionUsage::isSubactionUsage`,
//! `inputParameters`, `inputParameter` and `argument`,
//! `AcceptActionUsage::isTriggerAction`, `StateUsage::isSubstateUsage`,
//! `TransitionUsage::sourceFeature` and `triggerPayloadParameter`, and
//! `Usage::referencedFeatureTarget`. Each answers over the shared
//! ownership, membership and specialization evidence and refuses, naming
//! the element whose evidence was missing, where that evidence is not
//! certified.
use super::{
    OperationError, OperationExecutionSignature,
    namespaces::{blocked, owned_memberships_of_namespace, with_stable_evidence},
    references,
    specializations::chaining_features,
};
use crate::{
    json::{
        DerivedValue, ElementRef, Reference, ResolvedModel, TypeInputIssue, semantic_ownership,
        structural_index::StoredStructure,
        type_relations::{self, TypeRelations},
    },
    metaclass::{conforms, is_a},
};

#[derive(Clone, Copy)]
pub(super) enum Body {
    IsSubactionUsage,
    InputParameters,
    InputParameter,
    Argument,
    IsTriggerAction,
    IsSubstateUsage,
    SourceFeature,
    TriggerPayloadParameter,
    ReferencedFeatureTarget,
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
fn integer_argument(argument: &DerivedValue) -> i128 {
    match argument {
        DerivedValue::Literal(text) => text.parse().expect("validated integer"),
        _ => unreachable!("validated integer argument"),
    }
}
fn truth_argument(argument: &DerivedValue) -> bool {
    match argument {
        DerivedValue::Bool(value) => *value,
        _ => unreachable!("validated boolean argument"),
    }
}
fn optional(element: Option<usize>) -> DerivedValue {
    element.map_or(DerivedValue::Null, |e| {
        DerivedValue::Reference(Reference::Element(ElementRef(e)))
    })
}

/// The checked owning type of a feature, or nothing for a feature that
/// has none.
fn owning_type(
    r: &mut ResolvedModel,
    relations: &mut TypeRelations,
    feature: usize,
    effective: &'static str,
    steps: &mut usize,
) -> Result<Option<usize>, OperationError> {
    let owning = relations.owning_type(&mut r.b, feature, steps);
    charge(steps, 0, effective)?;
    owning.ok_or_else(|| blocked(effective, feature))
}

/// The membership that owns `feature`, with its certified carrier.
fn owning_membership(
    r: &ResolvedModel,
    raw: &StoredStructure,
    feature: usize,
    effective: &'static str,
    steps: &mut usize,
) -> Result<Option<(usize, usize)>, OperationError> {
    let Some(relationship) = r.b.elements[feature].owning_relationship else {
        return Ok(None);
    };
    charge(steps, 1, effective)?;
    let carrier = semantic_ownership::checked_relationship_carrier(&r.b, raw, relationship, steps)
        .ok_or_else(|| blocked(effective, feature))?;
    Ok(carrier.map(|owner| (relationship, owner)))
}

fn membership_kind(r: &ResolvedModel, relationship: usize) -> Option<&str> {
    r.b.elements[relationship].props.get("kind")?.as_str()
}

/// `Feature::featureTarget`: a chain's last chaining feature, else the
/// feature itself.
fn feature_target(
    r: &mut ResolvedModel,
    raw: &StoredStructure,
    feature: usize,
    effective: &'static str,
    steps: &mut usize,
) -> Result<usize, OperationError> {
    Ok(chaining_features(r, raw, feature, effective, steps)?
        .last()
        .copied()
        .unwrap_or(feature))
}

/// `ActionUsage::isSubactionUsage()`: composite, owned by an action
/// definition or usage, and not a state's entry or exit action.
fn is_subaction_usage(
    r: &mut ResolvedModel,
    raw: &StoredStructure,
    relations: &mut TypeRelations,
    action: usize,
    effective: &'static str,
    steps: &mut usize,
) -> Result<bool, OperationError> {
    charge(steps, 4, effective)?;
    if !flag(r, action, "isComposite", effective)? {
        return Ok(false);
    }
    let Some(owner) = owning_type(r, relations, action, effective, steps)? else {
        return Ok(false);
    };
    let kind = r.b.elements[owner].ty;
    if !(conforms(kind, "ActionDefinition") || conforms(kind, "ActionUsage")) {
        return Ok(false);
    }
    let (membership, carrier) = owning_membership(r, raw, action, effective, steps)?
        .ok_or_else(|| blocked(effective, action))?;
    if carrier != owner {
        return Err(blocked(effective, action));
    }
    if is_a!(r.b.elements[membership], "StateSubactionMembership") {
        return Ok(membership_kind(r, membership) == Some("do"));
    }
    Ok(true)
}

/// `StateUsage::isSubstateUsage(isParallel)`: composite, owned by a state
/// definition or usage whose `isParallel` is the argument, and not an
/// entry, do or exit action.
fn is_substate_usage(
    r: &mut ResolvedModel,
    raw: &StoredStructure,
    relations: &mut TypeRelations,
    state: usize,
    parallel: bool,
    effective: &'static str,
    steps: &mut usize,
) -> Result<bool, OperationError> {
    charge(steps, 4, effective)?;
    if !flag(r, state, "isComposite", effective)? {
        return Ok(false);
    }
    let Some(owner) = owning_type(r, relations, state, effective, steps)? else {
        return Ok(false);
    };
    let kind = r.b.elements[owner].ty;
    if !(conforms(kind, "StateDefinition") || conforms(kind, "StateUsage")) {
        return Ok(false);
    }
    if flag(r, owner, "isParallel", effective)? != parallel {
        return Ok(false);
    }
    let (membership, _) = owning_membership(r, raw, state, effective, steps)?
        .ok_or_else(|| blocked(effective, state))?;
    Ok(!is_a!(r.b.elements[membership], "StateSubactionMembership"))
}

/// `AcceptActionUsage::isTriggerAction()`: owned by a transition usage as
/// one of its trigger actions (a `trigger` transition feature membership).
fn is_trigger_action(
    r: &mut ResolvedModel,
    raw: &StoredStructure,
    relations: &mut TypeRelations,
    accept: usize,
    effective: &'static str,
    steps: &mut usize,
) -> Result<bool, OperationError> {
    charge(steps, 4, effective)?;
    let Some(owner) = owning_type(r, relations, accept, effective, steps)? else {
        return Ok(false);
    };
    if !conforms(r.b.elements[owner].ty, "TransitionUsage") {
        return Ok(false);
    }
    let (membership, _) = owning_membership(r, raw, accept, effective, steps)?
        .ok_or_else(|| blocked(effective, accept))?;
    Ok(
        is_a!(r.b.elements[membership], "TransitionFeatureMembership")
            && membership_kind(r, membership) == Some("trigger"),
    )
}

/// `ActionUsage::inputParameters()`: the action's inputs (`Type::input`,
/// certified) that it owns itself.
fn input_parameters(
    r: &mut ResolvedModel,
    action: usize,
    signature: &OperationExecutionSignature,
    effective: &'static str,
    steps: &mut usize,
) -> Result<Vec<usize>, OperationError> {
    let report = r.type_input_report_with_budget(ElementRef(action), *steps);
    *steps = report.steps;
    let inputs = report.inputs.map_err(|issue| match issue {
        TypeInputIssue::WorkLimit => OperationError::WorkLimit { effective },
        TypeInputIssue::UnsupportedConfiguration => OperationError::UnsupportedConfiguration {
            effective,
            parameter: signature.result,
        },
        _ => blocked(effective, action),
    })?;
    charge(steps, inputs.len(), effective)?;
    Ok(inputs
        .into_iter()
        .map(|input| input.0)
        .filter(|&input| r.b.owner_elem(input) == Some(action))
        .collect())
}

/// `ActionUsage::inputParameter(i)`: the i-th owned input (from 1), or
/// nothing past the last.
fn input_parameter(
    r: &mut ResolvedModel,
    action: usize,
    i: i128,
    signature: &OperationExecutionSignature,
    effective: &'static str,
    steps: &mut usize,
) -> Result<Option<usize>, OperationError> {
    let parameters = input_parameters(r, action, signature, effective, steps)?;
    if i < 1 {
        return Ok(None);
    }
    Ok(usize::try_from(i - 1)
        .ok()
        .and_then(|index| parameters.get(index).copied()))
}

/// `ActionUsage::argument(i)`: the value expression bound to the i-th
/// owned input, or nothing.
fn argument(
    r: &mut ResolvedModel,
    raw: &StoredStructure,
    action: usize,
    i: i128,
    signature: &OperationExecutionSignature,
    effective: &'static str,
    steps: &mut usize,
) -> Result<Option<usize>, OperationError> {
    let Some(parameter) = input_parameter(r, action, i, signature, effective, steps)? else {
        return Ok(None);
    };
    let rows = semantic_ownership::owned_relationships(&r.b, parameter)
        .ok_or_else(|| blocked(effective, parameter))?;
    charge(steps, rows.len(), effective)?;
    let rows: Vec<usize> = rows.iter().collect();
    for relationship in rows {
        if !is_a!(r.b.elements[relationship], "FeatureValue") {
            continue;
        }
        let carrier =
            semantic_ownership::checked_relationship_carrier(&r.b, raw, relationship, steps)
                .ok_or_else(|| blocked(effective, parameter))?;
        if carrier != Some(parameter) {
            return Err(blocked(effective, parameter));
        }
        let value = r.b.elements[relationship]
            .children
            .iter()
            .copied()
            .find(|&child| conforms(r.b.elements[child].ty, "Expression"))
            .ok_or_else(|| blocked(effective, parameter))?;
        return Ok(Some(value));
    }
    Ok(None)
}

/// `TransitionUsage::sourceFeature()`: the first feature a membership of
/// the transition other than a feature membership names whose feature
/// target is an action usage; for a target transition, its implicit
/// source (the implied Membership the materializer gives it names the
/// same element, so the answer does not depend on whether the implied
/// relationships are materialized when the body runs).
fn source_feature(
    r: &mut ResolvedModel,
    raw: &StoredStructure,
    transition: usize,
    effective: &'static str,
    steps: &mut usize,
) -> Result<Option<usize>, OperationError> {
    let memberships = owned_memberships_of_namespace(&r.b, raw, transition, steps, effective)?;
    charge(steps, memberships.len(), effective)?;
    for membership in memberships {
        if is_a!(r.b.elements[membership.relationship], "FeatureMembership")
            || !conforms(r.b.elements[membership.member].ty, "Feature")
        {
            continue;
        }
        let target = feature_target(r, raw, membership.member, effective, steps)?;
        if conforms(r.b.elements[target].ty, "ActionUsage") {
            return Ok(Some(membership.member));
        }
    }
    Ok(
        r.implicit_transition_source(crate::json::ElementRef(transition))
            .map(|source| source.0),
    )
}

/// `TransitionUsage::triggerPayloadParameter()`: the first trigger
/// action's payload parameter — its first parameter — or nothing.
fn trigger_payload_parameter(
    r: &mut ResolvedModel,
    raw: &StoredStructure,
    transition: usize,
    effective: &'static str,
    steps: &mut usize,
) -> Result<Option<usize>, OperationError> {
    let memberships = owned_memberships_of_namespace(&r.b, raw, transition, steps, effective)?;
    charge(steps, memberships.len(), effective)?;
    let trigger = memberships.iter().find(|membership| {
        is_a!(
            r.b.elements[membership.relationship],
            "TransitionFeatureMembership"
        ) && membership_kind(r, membership.relationship) == Some("trigger")
            && conforms(r.b.elements[membership.member].ty, "AcceptActionUsage")
    });
    let Some(trigger) = trigger.map(|membership| membership.member) else {
        return Ok(None);
    };
    let parameters = owned_memberships_of_namespace(&r.b, raw, trigger, steps, effective)?;
    charge(steps, parameters.len(), effective)?;
    Ok(parameters
        .iter()
        .find(|membership| is_a!(r.b.elements[membership.relationship], "ParameterMembership"))
        .map(|membership| membership.member))
}

/// `Usage::referencedFeatureTarget()`: the feature target of the owned
/// reference subsetting's referenced feature, or nothing.
fn referenced_feature_target(
    r: &mut ResolvedModel,
    raw: &StoredStructure,
    usage: usize,
    effective: &'static str,
    steps: &mut usize,
) -> Result<Option<usize>, OperationError> {
    let rows = semantic_ownership::owned_relationships(&r.b, usage)
        .ok_or_else(|| blocked(effective, usage))?;
    charge(steps, rows.len(), effective)?;
    let rows: Vec<usize> = rows.iter().collect();
    for relationship in rows {
        if !conforms(r.b.elements[relationship].ty, "ReferenceSubsetting") {
            continue;
        }
        let target = type_relations::endpoint(
            &mut r.b,
            usage,
            relationship,
            &["referencingFeature", "subsettingFeature", "specific"],
            &["referencedFeature", "subsettedFeature", "general"],
            "Feature",
            steps,
        )
        .ok_or_else(|| incomplete(steps, effective, usage))?;
        return Ok(Some(feature_target(r, raw, target, effective, steps)?));
    }
    Ok(None)
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
        let e = receiver.0;
        Ok(match body {
            Body::IsSubactionUsage => DerivedValue::Bool(is_subaction_usage(
                r,
                raw,
                &mut relations,
                e,
                effective,
                steps,
            )?),
            Body::IsSubstateUsage => DerivedValue::Bool(is_substate_usage(
                r,
                raw,
                &mut relations,
                e,
                truth_argument(&arguments[0]),
                effective,
                steps,
            )?),
            Body::IsTriggerAction => DerivedValue::Bool(is_trigger_action(
                r,
                raw,
                &mut relations,
                e,
                effective,
                steps,
            )?),
            Body::InputParameters => {
                references(input_parameters(r, e, signature, effective, steps)?)
            }
            Body::InputParameter => optional(input_parameter(
                r,
                e,
                integer_argument(&arguments[0]),
                signature,
                effective,
                steps,
            )?),
            Body::Argument => optional(argument(
                r,
                raw,
                e,
                integer_argument(&arguments[0]),
                signature,
                effective,
                steps,
            )?),
            Body::SourceFeature => optional(source_feature(r, raw, e, effective, steps)?),
            Body::TriggerPayloadParameter => {
                optional(trigger_payload_parameter(r, raw, e, effective, steps)?)
            }
            Body::ReferencedFeatureTarget => {
                optional(referenced_feature_target(r, raw, e, effective, steps)?)
            }
        })
    })?;
    Ok(value)
}
