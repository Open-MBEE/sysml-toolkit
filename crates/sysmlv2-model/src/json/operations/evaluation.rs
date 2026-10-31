//! Checked Expression, MultiplicityRange, ControlNode and MetadataFeature
//! bodies that evaluate at model level (KerML 8.3.4.1.3, 8.3.4.8,
//! 8.3.4.13, 8.3.4.14; SysML 8.3.17, 8.3.21): `evaluate`,
//! `checkCondition`, `modelLevelEvaluable`, `instantiatedType`,
//! `valueOf`, `hasBounds`, `multiplicityHasBounds`, `evaluateFeature`,
//! `isSemantic` and `isSyntactic`. Model-level eligibility is the shared
//! proof; evaluation is the toolkit's evaluator over the expression as
//! written, from the scope the target opens. A result that is an element
//! is returned as a reference; one that is a literal is returned as the
//! spelling of the literal expression that would carry it
//! ([`DerivedValue::Literals`]), since the toolkit materializes no result
//! elements.
use super::{
    OperationError, OperationExecutionSignature, argument_element,
    namespaces::{self, blocked, resolution, with_stable_evidence},
    references,
};
use crate::{
    eval::{EvalError, Value},
    json::{
        DerivedValue, ElementRef, ModelLevelEvaluability, Reference, ResolvedModel, ScopeRef,
        semantic_ownership,
        structural_index::StoredStructure,
        type_relations::{RelationFact, TypeRelations},
    },
    metaclass::{conforms, is_a},
};
use std::collections::HashSet;
use sysmlv2_syntax::ast::Expr;

#[derive(Clone, Copy)]
pub(super) enum Body {
    Evaluate,
    CheckCondition,
    ModelLevelEvaluable,
    InstantiatedType,
    OperatorInstantiatedType,
    TriggerInstantiatedType,
    ValueOf,
    HasBounds,
    MultiplicityHasBounds,
    EvaluateFeature,
    IsSemantic,
    IsSyntactic,
}

const INVOCATION_EVALUATE: &str = "Kernel-Expressions-InvocationExpression-evaluate_Element";

fn charge(steps: &mut usize, n: usize, effective: &'static str) -> Result<(), OperationError> {
    *steps = steps.saturating_add(n);
    if *steps > crate::eval::MAX_STEPS {
        Err(OperationError::WorkLimit { effective })
    } else {
        Ok(())
    }
}
fn optional_element(argument: &DerivedValue) -> Option<usize> {
    match argument {
        DerivedValue::Null => None,
        other => Some(argument_element(other)),
    }
}
fn integer_argument(argument: &DerivedValue) -> i128 {
    match argument {
        DerivedValue::Literal(text) => text.parse().expect("validated integer"),
        _ => unreachable!("validated integer argument"),
    }
}
/// An unlimited natural: `None` is `*`.
fn unlimited_argument(argument: &DerivedValue) -> Option<i128> {
    match argument {
        DerivedValue::Literal(text) if text == "*" => None,
        DerivedValue::Literal(text) => Some(text.parse().expect("validated natural")),
        _ => unreachable!("validated unlimited natural argument"),
    }
}
/// The bounds a multiplicity is asked about: an unlimited upper bound is `None`.
#[derive(Clone, Copy)]
struct Bounds {
    lower: i128,
    upper: Option<i128>,
}
fn unsupported(effective: &'static str, parameter: &'static str) -> OperationError {
    OperationError::UnsupportedConfiguration {
        effective,
        parameter,
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Fact {
    Yes,
    No,
    Blocked(usize),
}
impl Fact {
    fn value(self, effective: &'static str) -> Result<DerivedValue, OperationError> {
        match self {
            Fact::Yes => Ok(DerivedValue::Bool(true)),
            Fact::No => Ok(DerivedValue::Bool(false)),
            Fact::Blocked(element) => Err(blocked(effective, element)),
        }
    }
}

/// The model-level eligibility of an expression, by the shared proof.
fn evaluable(
    r: &mut ResolvedModel,
    expression: usize,
    effective: &'static str,
    steps: &mut usize,
) -> Result<Fact, OperationError> {
    let report = r.model_level_evaluability_with_budget(ElementRef(expression), *steps);
    *steps = report.steps;
    charge(steps, 0, effective)?;
    Ok(match report.classification {
        ModelLevelEvaluability::Evaluable => Fact::Yes,
        ModelLevelEvaluability::NotEvaluable => Fact::No,
        ModelLevelEvaluability::Unknown(_) => Fact::Blocked(expression),
    })
}

/// A model-level result: nothing, literal values, or elements.
enum Rendered {
    Empty,
    Literals(Vec<String>),
    References(Vec<usize>),
}
impl Rendered {
    fn value(self) -> DerivedValue {
        match self {
            Rendered::Empty => DerivedValue::References(Vec::new()),
            Rendered::Literals(values) => DerivedValue::Literals(values),
            Rendered::References(elements) => references(elements),
        }
    }
}
fn flatten(value: Value, out: &mut Vec<Value>) {
    match value {
        Value::Sequence(values) => {
            for value in values {
                flatten(value, out);
            }
        }
        value => out.push(value),
    }
}
/// The spelling of the literal expression that would carry a value.
fn spell(value: &Value) -> Option<String> {
    Some(match value {
        Value::Boolean(b) => b.to_string(),
        Value::Integer(i) => i.to_string(),
        Value::Rational(r) => r.to_string(),
        Value::Real(f) if f.is_infinite() && *f > 0.0 => "*".to_owned(),
        Value::Real(f) => format!("{f:?}"),
        Value::String(s) => format!("{s:?}"),
        Value::Quantity(number, unit) => format!("{} [{}]", spell(number)?, unit.display()),
        _ => return None,
    })
}
fn render(
    value: Value,
    expression: usize,
    effective: &'static str,
    parameter: &'static str,
) -> Result<Rendered, OperationError> {
    let mut items = Vec::new();
    flatten(value, &mut items);
    let mut literals = Vec::new();
    let mut elements = Vec::new();
    for item in items {
        match item {
            Value::Element(e) => elements.push(e.0),
            // An unbound feature or an indeterminate operand is no
            // model-level value: the expression's evaluability proof and
            // its evaluation disagree, which names the feature.
            Value::Unbound(e, _) | Value::UnboundMember(e, _) => {
                return Err(blocked(effective, e.0));
            }
            Value::Indeterminate => return Err(blocked(effective, expression)),
            Value::Instance { .. } => return Err(unsupported(effective, parameter)),
            other => literals.push(spell(&other).ok_or_else(|| unsupported(effective, parameter))?),
        }
    }
    Ok(match (literals.is_empty(), elements.is_empty()) {
        (true, true) => Rendered::Empty,
        (false, true) => Rendered::Literals(literals),
        (true, false) => Rendered::References(elements),
        (false, false) => return Err(unsupported(effective, parameter)),
    })
}

/// The expression as written and the scope it was recorded from: the
/// value expression of a feature (the FeatureValue's child), a result
/// expression (the ResultExpressionMembership's child), or the receiver's
/// own result expression. An operand or argument expression has no source
/// of its own.
fn expression_source(
    r: &mut ResolvedModel,
    raw: &StoredStructure,
    expression: usize,
    effective: &'static str,
    steps: &mut usize,
) -> Result<Option<(usize, Expr)>, OperationError> {
    charge(steps, 4, effective)?;
    let result_of = |r: &ResolvedModel, owner: usize| {
        r.b.result_exprs
            .iter()
            .find(|(o, _, _)| *o == owner)
            .map(|(_, scope, expr)| (*scope, expr.clone()))
    };
    let Some(relationship) = r.b.elements[expression].owning_relationship else {
        return Ok(result_of(r, expression));
    };
    let kind = r.b.elements[relationship].ty;
    if kind == "FeatureValue" || kind == "ResultExpressionMembership" {
        let carrier =
            semantic_ownership::checked_relationship_carrier(&r.b, raw, relationship, steps)
                .ok_or_else(|| blocked(effective, expression))?;
        let Some(owner) = carrier else {
            return Ok(None);
        };
        return Ok(if kind == "FeatureValue" {
            r.b.values
                .get(&owner)
                .map(|(scope, expr)| (*scope, expr.clone()))
        } else {
            result_of(r, owner)
        });
    }
    Ok(result_of(r, expression))
}
/// The scope a target opens, else the one its declaration lives in.
fn target_scope(r: &ResolvedModel, target: usize) -> Option<usize> {
    r.b.elem_scope
        .get(&target)
        .copied()
        .or_else(|| r.b.owner_scope_of(target))
}

/// `Expression::evaluate(target)` and its overrides: nothing for an
/// expression that is not model-level evaluable; else the expression as
/// written, evaluated from the scope the target opens.
fn evaluate(
    r: &mut ResolvedModel,
    raw: &StoredStructure,
    expression: usize,
    target: usize,
    effective: &'static str,
    parameter: &'static str,
    steps: &mut usize,
) -> Result<Rendered, OperationError> {
    charge(steps, 16, effective)?;
    let kind = r.b.elements[expression].ty;
    if conforms(kind, "CalculationUsage") || conforms(kind, "ConstraintUsage") {
        return Ok(Rendered::Empty);
    }
    match evaluable(r, expression, effective, steps)? {
        Fact::No => return Ok(Rendered::Empty),
        Fact::Blocked(e) => return Err(blocked(effective, e)),
        Fact::Yes => {}
    }
    let Some((_, expr)) = expression_source(r, raw, expression, effective, steps)? else {
        return Err(unsupported(effective, parameter));
    };
    let scope = target_scope(r, target).ok_or_else(|| blocked(effective, target))?;
    charge(steps, 64, effective)?;
    match r.evaluate_in(ScopeRef(scope), &expr) {
        Ok(value) => render(value, expression, effective, parameter),
        // An application that is not possible: an empty sequence, as the
        // invocation body says; any other failure refuses.
        Err(EvalError::Type(_) | EvalError::DivisionByZero) if effective == INVOCATION_EVALUATE => {
            Ok(Rendered::Empty)
        }
        Err(_) => Err(blocked(effective, expression)),
    }
}

/// `Expression::modelLevelEvaluable(visited)`: the shared proof, with no
/// features visited yet.
fn model_level_evaluable(
    r: &mut ResolvedModel,
    expression: usize,
    visited: &DerivedValue,
    effective: &'static str,
    parameter: &'static str,
    steps: &mut usize,
) -> Result<DerivedValue, OperationError> {
    let visited = match visited {
        DerivedValue::Elements(v) => v.len(),
        DerivedValue::References(v) => v.len(),
        _ => 0,
    };
    if visited > 0 {
        return Err(unsupported(effective, parameter));
    }
    evaluable(r, expression, effective, steps)?.value(effective)
}

/// `InstantiationExpression::instantiatedType()`: the member of the first
/// owned membership that is not a feature membership, when a Type.
fn instantiated_type(
    r: &mut ResolvedModel,
    raw: &StoredStructure,
    receiver: usize,
    effective: &'static str,
    steps: &mut usize,
) -> Result<DerivedValue, OperationError> {
    let memberships =
        namespaces::owned_memberships_of_namespace(&r.b, raw, receiver, steps, effective)?;
    charge(steps, memberships.len(), effective)?;
    Ok(memberships
        .iter()
        .find(|m| !is_a!(r.b.elements[m.relationship], "FeatureMembership"))
        .filter(|m| is_a!(r.b.elements[m.member], "Type"))
        .map_or(DerivedValue::Null, |m| {
            DerivedValue::Reference(Reference::Element(ElementRef(m.member)))
        }))
}
/// A library type by its qualified name, through the checked global
/// resolution; absent when the name does not resolve to a Type.
fn library_type(
    r: &mut ResolvedModel,
    raw: &StoredStructure,
    receiver: usize,
    names: &[&str],
    effective: &'static str,
    steps: &mut usize,
) -> Result<Option<usize>, OperationError> {
    let names: Vec<String> = names.iter().map(|n| (*n).to_owned()).collect();
    let membership =
        resolution::resolve_segments(r, raw, true, receiver, &names, steps, effective)?;
    Ok(membership
        .map(|m| m.member)
        .filter(|&member| is_a!(r.b.elements[member], "Type")))
}
fn as_type(found: Option<usize>) -> DerivedValue {
    found.map_or(DerivedValue::Null, |t| {
        DerivedValue::Reference(Reference::Element(ElementRef(t)))
    })
}
/// `OperatorExpression::instantiatedType()`: the operator's function in
/// the base, data or control function library, in that order.
fn operator_instantiated_type(
    r: &mut ResolvedModel,
    raw: &StoredStructure,
    receiver: usize,
    effective: &'static str,
    steps: &mut usize,
) -> Result<DerivedValue, OperationError> {
    let operator = r.b.elements[receiver]
        .props
        .get("operator")
        .and_then(|v| v.as_str())
        .ok_or_else(|| blocked(effective, receiver))?
        .to_owned();
    for package in ["BaseFunctions", "DataFunctions", "ControlFunctions"] {
        if let Some(function) =
            library_type(r, raw, receiver, &[package, &operator], effective, steps)?
        {
            return Ok(as_type(Some(function)));
        }
    }
    Ok(DerivedValue::Null)
}
/// `TriggerInvocationExpression::instantiatedType()`: the trigger function
/// its kind names.
fn trigger_instantiated_type(
    r: &mut ResolvedModel,
    raw: &StoredStructure,
    receiver: usize,
    effective: &'static str,
    steps: &mut usize,
) -> Result<DerivedValue, OperationError> {
    let function = match r.b.elements[receiver]
        .props
        .get("kind")
        .and_then(|v| v.as_str())
    {
        Some("when") => "TriggerWhen",
        Some("at") => "TriggerAt",
        Some("after") => "TriggerAfter",
        _ => return Err(blocked(effective, receiver)),
    };
    Ok(as_type(library_type(
        r,
        raw,
        receiver,
        &["Triggers", function],
        effective,
        steps,
    )?))
}

/// The bound expressions of a range, lower first where there are two.
fn bounds(
    r: &mut ResolvedModel,
    raw: &StoredStructure,
    range: usize,
    effective: &'static str,
    steps: &mut usize,
) -> Result<Vec<usize>, OperationError> {
    Ok(
        namespaces::owned_memberships_of_namespace(&r.b, raw, range, steps, effective)?
            .into_iter()
            .map(|m| m.member)
            .filter(|&m| conforms(r.b.elements[m].ty, "Expression"))
            .collect(),
    )
}
/// A bound's expression as written: one of the range's own bounds comes
/// from the multiplicity declaration of the range's owner; any other
/// expression from its own source.
fn bound_source(
    r: &mut ResolvedModel,
    raw: &StoredStructure,
    range: usize,
    bound: usize,
    effective: &'static str,
    steps: &mut usize,
) -> Result<Option<(usize, Expr)>, OperationError> {
    let members = bounds(r, raw, range, effective, steps)?;
    let Some(position) = members.iter().position(|&m| m == bound) else {
        return expression_source(r, raw, bound, effective, steps);
    };
    let Some(relationship) = r.b.elements[range].owning_relationship else {
        return Ok(None);
    };
    let owner = semantic_ownership::checked_relationship_carrier(&r.b, raw, relationship, steps)
        .ok_or_else(|| blocked(effective, range))?;
    let Some(owner) = owner else {
        return Ok(None);
    };
    charge(steps, 4, effective)?;
    let Some((_, scope, multiplicity)) = r.b.multiplicities.iter().find(|(o, _, _)| *o == owner)
    else {
        return Ok(None);
    };
    let expr = match (members.len(), position) {
        (2, 0) => multiplicity.lower.clone(),
        (2, 1) | (1, 0) => Some(multiplicity.upper.clone()),
        _ => None,
    };
    Ok(expr.map(|expr| (*scope, expr)))
}
/// `MultiplicityRange::valueOf(bound)`: `Ok(None)` is null, `Some(None)`
/// is `*`, `Some(Some(n))` a natural number.
fn value_of(
    r: &mut ResolvedModel,
    raw: &StoredStructure,
    range: usize,
    bound: Option<usize>,
    effective: &'static str,
    parameter: &'static str,
    steps: &mut usize,
) -> Result<Option<Option<i128>>, OperationError> {
    charge(steps, 8, effective)?;
    let Some(bound) = bound else {
        return Ok(None);
    };
    match evaluable(r, bound, effective, steps)? {
        Fact::No => return Ok(None),
        Fact::Blocked(e) => return Err(blocked(effective, e)),
        Fact::Yes => {}
    }
    let Some((scope, expr)) = bound_source(r, raw, range, bound, effective, steps)? else {
        return Err(unsupported(effective, parameter));
    };
    charge(steps, 64, effective)?;
    let value = r
        .evaluate_in(ScopeRef(scope), &expr)
        .map_err(|_| blocked(effective, bound))?;
    let mut items = Vec::new();
    flatten(value, &mut items);
    if items.len() != 1 {
        return Ok(None);
    }
    Ok(match items.pop().expect("one item") {
        Value::Real(f) if f.is_infinite() && f > 0.0 => Some(None),
        Value::Integer(n) if n >= 0 => Some(Some(n)),
        Value::Unbound(e, _) | Value::UnboundMember(e, _) => {
            return Err(blocked(effective, e.0));
        }
        Value::Indeterminate => return Err(blocked(effective, bound)),
        _ => None,
    })
}
fn natural(value: Option<Option<i128>>) -> DerivedValue {
    match value {
        None => DerivedValue::Null,
        Some(None) => DerivedValue::Literal("*".to_owned()),
        Some(Some(n)) => DerivedValue::Literal(n.to_string()),
    }
}
/// `MultiplicityRange::hasBounds(lower, upper)`: the upper bound evaluates
/// to `upper`, and the lower bound to `lower`, or there is none and
/// `lower` is `upper` or the range is `0..*`.
fn has_bounds(
    r: &mut ResolvedModel,
    raw: &StoredStructure,
    range: usize,
    asked: Bounds,
    effective: &'static str,
    parameter: &'static str,
    steps: &mut usize,
) -> Result<bool, OperationError> {
    let Bounds { lower, upper } = asked;
    let members = bounds(r, raw, range, effective, steps)?;
    let (lower_bound, upper_bound) = match members.as_slice() {
        [upper_bound] => (None, Some(*upper_bound)),
        [lower_bound, upper_bound] => (Some(*lower_bound), Some(*upper_bound)),
        _ => (None, None),
    };
    if value_of(r, raw, range, upper_bound, effective, parameter, steps)? != Some(upper) {
        return Ok(false);
    }
    Ok(
        match value_of(r, raw, range, lower_bound, effective, parameter, steps)? {
            Some(Some(n)) => n == lower,
            Some(None) => false,
            None => upper == Some(lower) || (lower == 0 && upper.is_none()),
        },
    )
}
/// `ControlNode::multiplicityHasBounds(mult, lower, upper)`: the given
/// multiplicity, or a range among its supertypes, has the bounds.
fn multiplicity_has_bounds(
    r: &mut ResolvedModel,
    raw: &StoredStructure,
    multiplicity: usize,
    asked: Bounds,
    effective: &'static str,
    parameter: &'static str,
    steps: &mut usize,
) -> Result<bool, OperationError> {
    if r.b.elements[multiplicity].ty == "MultiplicityRange" {
        return has_bounds(r, raw, multiplicity, asked, effective, parameter, steps);
    }
    let mut relations = TypeRelations::default();
    let mut seen = HashSet::new();
    let mut queue = vec![multiplicity];
    let mut next = 0;
    while next < queue.len() {
        let ty = queue[next];
        next += 1;
        charge(steps, 2, effective)?;
        if !seen.insert(ty) {
            continue;
        }
        if ty != multiplicity
            && r.b.elements[ty].ty == "MultiplicityRange"
            && has_bounds(r, raw, ty, asked, effective, parameter, steps)?
        {
            return Ok(true);
        }
        let bases = relations.complete_direct_bases(&mut r.b, ty, steps);
        charge(steps, 0, effective)?;
        queue.extend(bases.ok_or_else(|| blocked(effective, ty))?);
    }
    Ok(false)
}

/// `MetadataFeature::isSemantic()` / `isSyntactic()`: whether the feature
/// specializes the library's semantic metadata metaclass, or the
/// reflective abstract syntax's root metaclass.
fn specializes_library(
    r: &mut ResolvedModel,
    raw: &StoredStructure,
    receiver: usize,
    names: &[&str],
    effective: &'static str,
    steps: &mut usize,
) -> Result<DerivedValue, OperationError> {
    let Some(general) = library_type(r, raw, receiver, names, effective, steps)? else {
        return Ok(DerivedValue::Bool(false));
    };
    let fact = TypeRelations::default().specializes(&mut r.b, receiver, general, steps);
    charge(steps, 0, effective)?;
    match fact {
        RelationFact::Yes => Fact::Yes,
        RelationFact::No => Fact::No,
        RelationFact::Unknown => Fact::Blocked(receiver),
    }
    .value(effective)
}
/// `MetadataFeature::evaluateFeature(baseFeature)`: the value of the first
/// feature of this metadata feature that is, or redefines, `baseFeature`,
/// read from it or from the nearest feature it redefines that has one,
/// evaluated with this metadata feature as the target. The features are
/// the owned ones; an inherited match is not certified.
fn evaluate_feature(
    r: &mut ResolvedModel,
    raw: &StoredStructure,
    receiver: usize,
    base: usize,
    effective: &'static str,
    parameter: &'static str,
    steps: &mut usize,
) -> Result<DerivedValue, OperationError> {
    let mut relations = TypeRelations::default();
    let memberships =
        namespaces::owned_memberships_of_namespace(&r.b, raw, receiver, steps, effective)?;
    let mut selected = None;
    for membership in memberships {
        charge(steps, 2, effective)?;
        let feature = membership.member;
        if !is_a!(r.b.elements[membership.relationship], "FeatureMembership")
            || !conforms(r.b.elements[feature].ty, "Feature")
        {
            continue;
        }
        if feature == base {
            selected = Some(feature);
            break;
        }
        let closure = relations.checked_redefinition_closure(&mut r.b, feature, steps);
        charge(steps, 0, effective)?;
        if closure
            .ok_or_else(|| blocked(effective, feature))?
            .contains(&base)
        {
            selected = Some(feature);
            break;
        }
    }
    let Some(selected) = selected else {
        return Err(blocked(effective, receiver));
    };
    let mut candidates = vec![selected];
    let closure = relations.checked_redefinition_closure(&mut r.b, selected, steps);
    charge(steps, 0, effective)?;
    candidates.extend(closure.ok_or_else(|| blocked(effective, selected))?);
    for candidate in candidates {
        charge(steps, 2, effective)?;
        let Some(expression) = r.b.elements[candidate]
            .owned_relationships
            .iter()
            .copied()
            .find(|&rel| r.b.elements[rel].ty == "FeatureValue")
            .and_then(|rel| r.b.elements[rel].children.first().copied())
        else {
            continue;
        };
        return evaluate(r, raw, expression, receiver, effective, parameter, steps)
            .map(Rendered::value);
    }
    Ok(DerivedValue::References(Vec::new()))
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
    let parameter = signature
        .inputs
        .first()
        .copied()
        .unwrap_or(signature.result);
    if let Body::ModelLevelEvaluable = body {
        return model_level_evaluable(r, receiver.0, &arguments[0], effective, parameter, steps);
    }
    let (_, _, value) = with_stable_evidence(r, receiver, steps, effective, |r, raw, steps| {
        Ok(match body {
            Body::Evaluate => evaluate(
                r,
                raw,
                receiver.0,
                argument_element(&arguments[0]),
                effective,
                parameter,
                steps,
            )?
            .value(),
            Body::CheckCondition => {
                let rendered = evaluate(
                    r,
                    raw,
                    receiver.0,
                    argument_element(&arguments[0]),
                    effective,
                    parameter,
                    steps,
                )?;
                DerivedValue::Bool(
                    matches!(rendered, Rendered::Literals(ref values) if values.len() == 1 && values[0] == "true"),
                )
            }
            Body::ModelLevelEvaluable => unreachable!("answered above"),
            Body::InstantiatedType => instantiated_type(r, raw, receiver.0, effective, steps)?,
            Body::OperatorInstantiatedType => {
                operator_instantiated_type(r, raw, receiver.0, effective, steps)?
            }
            Body::TriggerInstantiatedType => {
                trigger_instantiated_type(r, raw, receiver.0, effective, steps)?
            }
            Body::ValueOf => natural(value_of(
                r,
                raw,
                receiver.0,
                optional_element(&arguments[0]),
                effective,
                parameter,
                steps,
            )?),
            Body::HasBounds => DerivedValue::Bool(has_bounds(
                r,
                raw,
                receiver.0,
                Bounds {
                    lower: integer_argument(&arguments[0]),
                    upper: unlimited_argument(&arguments[1]),
                },
                effective,
                parameter,
                steps,
            )?),
            Body::MultiplicityHasBounds => DerivedValue::Bool(multiplicity_has_bounds(
                r,
                raw,
                argument_element(&arguments[0]),
                Bounds {
                    lower: integer_argument(&arguments[1]),
                    upper: unlimited_argument(&arguments[2]),
                },
                effective,
                parameter,
                steps,
            )?),
            Body::EvaluateFeature => evaluate_feature(
                r,
                raw,
                receiver.0,
                argument_element(&arguments[0]),
                effective,
                parameter,
                steps,
            )?,
            Body::IsSemantic => specializes_library(
                r,
                raw,
                receiver.0,
                &["Metaobjects", "SemanticMetadata"],
                effective,
                steps,
            )?,
            Body::IsSyntactic => {
                specializes_library(r, raw, receiver.0, &["KerML", "Element"], effective, steps)?
            }
        })
    })?;
    Ok(value)
}
