//! Checked Expression, MultiplicityRange, ControlNode and MetadataFeature
//! bodies that evaluate at model level (KerML 8.3.4.1.3, 8.3.4.8,
//! 8.3.4.13, 8.3.4.14; SysML 8.3.17, 8.3.21): `evaluate`,
//! `checkCondition`, `modelLevelEvaluable`, `instantiatedType`,
//! `valueOf`, `hasBounds`, `multiplicityHasBounds`, `evaluateFeature`,
//! `isSemantic`, `isSyntactic` and `syntaxElement`, and the metadata
//! access bodies `metaclassFeature` and the `evaluate` override (KerML
//! 8.3.4.8.8, 9.2). Model-level eligibility is the shared
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
    SyntaxElement,
    MetadataEvaluate,
    MetaclassFeature,
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

/// The element a metadata access expression refers to: the member of
/// its first owned membership that is not a feature membership (KerML
/// 8.3.4.8.8), refusing where the expression's membership domain is not
/// certified or the reference does not resolve.
fn referenced_element(
    r: &mut ResolvedModel,
    raw: &StoredStructure,
    expression: usize,
    effective: &'static str,
    steps: &mut usize,
) -> Result<usize, OperationError> {
    let memberships =
        namespaces::owned_memberships_of_namespace(&r.b, raw, expression, steps, effective)?;
    charge(steps, memberships.len(), effective)?;
    memberships
        .iter()
        .find(|m| !is_a!(r.b.elements[m.relationship], "FeatureMembership"))
        .map(|m| m.member)
        .ok_or_else(|| blocked(effective, expression))
}
/// `MetadataAccessExpression::metaclassFeature()`: the reflective
/// metaclass feature of the referenced element. The toolkit materializes
/// no result elements, so the feature is answered by the reflective
/// metaclass that types it: the metaclass of the standard reflection
/// libraries named like the element's own (`SysML::PartUsage`,
/// `KerML::Class`), the type the evaluator's metaobject instance carries.
/// Refuses at the referenced element when no reflective metaclass names
/// it: the reflection library is not loaded, or a user namespace shadows
/// it.
fn metaclass_feature(
    r: &mut ResolvedModel,
    referenced: usize,
    effective: &'static str,
    steps: &mut usize,
) -> Result<usize, OperationError> {
    charge(steps, 8, effective)?;
    let ty = r.b.elements[referenced].ty;
    r.b.reflection_metaclass(ty)
        .filter(|&metaclass| r.b.is_reflection_target(metaclass))
        .ok_or_else(|| blocked(effective, referenced))
}
/// `MetadataAccessExpression::evaluate(target)`: the metadata features
/// the referenced element owns that annotate it, in declaration order,
/// then its metaclass feature. The body does not read the target. The
/// annotation associations are complete under the stable evidence, so
/// the recorded annotations of the referenced element decide which of
/// its owned metadata features annotate it (a `@M about other;` in its
/// body does not).
fn metadata_access(
    r: &mut ResolvedModel,
    raw: &StoredStructure,
    expression: usize,
    effective: &'static str,
    steps: &mut usize,
) -> Result<Vec<usize>, OperationError> {
    let referenced = referenced_element(r, raw, expression, effective, steps)?;
    let annotating: Vec<usize> =
        r.b.metadata_of
            .get(&referenced)
            .cloned()
            .unwrap_or_default();
    let rows = semantic_ownership::owned_relationships(&r.b, referenced)
        .ok_or_else(|| blocked(effective, referenced))?;
    charge(
        steps,
        rows.len().saturating_add(annotating.len()),
        effective,
    )?;
    let rows: Vec<usize> = rows.iter().collect();
    let mut out = Vec::new();
    for relationship in rows {
        for &child in &r.b.elements[relationship].children {
            if is_a!(r.b.elements[child], "MetadataFeature") && annotating.contains(&child) {
                out.push(child);
            }
        }
    }
    out.push(metaclass_feature(r, referenced, effective, steps)?);
    Ok(out)
}
/// The elements a metadata feature annotates: the targets of its
/// Annotations (the owning one in the prefix shape, then the owned
/// ones), else its owner (KerML 8.3.2.1.2). The stable evidence has
/// already refused a model whose annotation targets do not all resolve;
/// a target this read still cannot place refuses at its Annotation.
fn annotated_elements(
    r: &mut ResolvedModel,
    receiver: usize,
    effective: &'static str,
    steps: &mut usize,
) -> Result<Vec<usize>, OperationError> {
    r.ensure_by_id();
    let is_annotation = |r: &ResolvedModel, rel: usize| r.b.elements[rel].ty == "Annotation";
    let mut annotations: Vec<usize> = r.b.elements[receiver]
        .owning_relationship
        .filter(|&rel| is_annotation(r, rel))
        .into_iter()
        .collect();
    annotations.extend(
        r.b.elements[receiver]
            .owned_relationships
            .iter()
            .copied()
            .filter(|&rel| is_annotation(r, rel)),
    );
    charge(steps, annotations.len().saturating_add(2), effective)?;
    if annotations.is_empty() {
        return Ok(r
            .owner(ElementRef(receiver))
            .map(|o| o.0)
            .into_iter()
            .collect());
    }
    let mut out = Vec::new();
    for annotation in annotations {
        let target = if r.b.elements[annotation]
            .props
            .get("annotatedElement")
            .is_some()
        {
            r.prop_target(annotation, "annotatedElement")
        } else {
            r.owner(ElementRef(annotation)).map(|o| o.0)
        };
        out.push(target.ok_or_else(|| blocked(effective, annotation))?);
    }
    Ok(out)
}
/// A type and every type its written specializations reach, each once,
/// nearest first, through the checked explicit projection. The
/// reflective abstract-syntax chain is written (`metadata def PartUsage
/// :> ItemUsage`, `metaclass Class :> Classifier`, a model's `:>
/// SysML::PartUsage`); the implied bases are library roles, none an
/// abstract-syntax metaclass, and a minimal reflection library leaves
/// them uncertified.
fn written_supertype_closure(
    r: &mut ResolvedModel,
    receiver: usize,
    effective: &'static str,
    steps: &mut usize,
) -> Result<Vec<usize>, OperationError> {
    let mut relations = TypeRelations::default();
    let mut order = vec![receiver];
    let mut seen = HashSet::from([receiver]);
    let mut next = 0;
    while let Some(&current) = order.get(next) {
        next += 1;
        charge(steps, 1, effective)?;
        let bases = relations.checked_supertypes(&mut r.b, current, true, steps);
        charge(steps, 0, effective)?;
        for base in bases.map_err(|_| blocked(effective, current))? {
            if seen.insert(base) {
                order.push(base);
            }
        }
    }
    Ok(order)
}
/// `MetadataFeature::syntaxElement()`: the element a syntactic metadata
/// feature reflectively represents. Its precondition is `isSyntactic()`;
/// a feature that is not syntactic answers null. A syntactic feature
/// represents the one element it annotates when that element's own
/// metaclass conforms to the most specific reflective abstract-syntax
/// metaclass in the written supertype closure of its one typing (the
/// metaclass itself, or the one a metadata definition of the model
/// specializes), else nothing. A feature whose typing is not one certified type refuses at
/// the feature; one whose reflective metaclasses are incomparable, or
/// that annotates several elements, refuses as an unsupported
/// configuration, since the result is at most one element.
fn syntax_element(
    r: &mut ResolvedModel,
    raw: &StoredStructure,
    receiver: usize,
    effective: &'static str,
    parameter: &'static str,
    steps: &mut usize,
) -> Result<DerivedValue, OperationError> {
    let syntactic = specializes_library(r, raw, receiver, &["KerML", "Element"], effective, steps)?;
    if syntactic == DerivedValue::Bool(false) {
        return Ok(DerivedValue::Null);
    }
    charge(steps, 8, effective)?;
    let types = r.b.direct_typing_elems(receiver);
    let &[metaclass] = types.as_slice() else {
        return Err(blocked(effective, receiver));
    };
    // The reflective abstract-syntax metaclasses the typing reaches,
    // nearest first (`Metaobjects::Metaobject` and the model's own
    // metaclasses are not among them); the most specific is the one every
    // other one generalizes.
    let mut names = Vec::new();
    for general in written_supertype_closure(r, metaclass, effective, steps)? {
        charge(steps, 1, effective)?;
        if r.b.is_reflection_target(general) {
            let name =
                r.b.effective_name(general)
                    .ok_or_else(|| blocked(effective, general))?;
            if crate::metaclass::lookup(&name).is_some() {
                names.push(name);
            }
        }
    }
    let Some(name) = names
        .iter()
        .find(|name| names.iter().all(|other| conforms(name, other)))
        .cloned()
    else {
        return Err(if names.is_empty() {
            blocked(effective, receiver)
        } else {
            unsupported(effective, parameter)
        });
    };
    let represented = match annotated_elements(r, receiver, effective, steps)?.as_slice() {
        [] => return Ok(DerivedValue::Null),
        &[one] => one,
        _ => return Err(unsupported(effective, parameter)),
    };
    Ok(if conforms(r.b.elements[represented].ty, &name) {
        DerivedValue::Reference(Reference::Element(ElementRef(represented)))
    } else {
        DerivedValue::Null
    })
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
            Body::SyntaxElement => syntax_element(r, raw, receiver.0, effective, parameter, steps)?,
            Body::MetadataEvaluate => {
                references(metadata_access(r, raw, receiver.0, effective, steps)?)
            }
            Body::MetaclassFeature => {
                let referenced = referenced_element(r, raw, receiver.0, effective, steps)?;
                DerivedValue::Reference(Reference::Element(ElementRef(metaclass_feature(
                    r, referenced, effective, steps,
                )?)))
            }
        })
    })?;
    Ok(value)
}
