//! Static action/state graph checks. No scheduling or behavioral execution.
use super::{
    expressions,
    facts::{Facts, flag, is},
};
use crate::{
    json::{ElementRef, ResolvedModel},
    model::Model,
};
use sysmlv2_syntax::diag::Diagnostic;

pub(super) fn validate(
    r: &mut ResolvedModel,
    model: &Model,
    g: &Facts,
) -> Vec<(usize, Diagnostic)> {
    let mut out = Vec::new();
    let n = r.b.explicit_len();
    let mut incoming = vec![0; n];
    let mut outgoing = vec![0; n];
    let mut edges = Vec::new();
    for e in 0..n {
        if !is(&r.b, e, "Succession") {
            continue;
        }
        let ends: Vec<_> = g.members[e]
            .iter()
            .copied()
            .filter(|&m| flag(&r.b, m, "isEnd"))
            .collect();
        let [from, to] = ends.as_slice() else {
            continue;
        };
        let a = g.feature_target(&r.b, *from);
        let z = g.feature_target(&r.b, *to);
        let a = if a == *from {
            g.owner[e]
                .filter(|&p| is(&r.b, p, "TransitionUsage"))
                .and_then(|p| {
                    g.relations(&r.b, p, "Membership", "memberElement")
                        .first()
                        .copied()
                })
        } else {
            Some(a)
        };
        if let Some(a) = a {
            if z != *to {
                incoming[z] += 1;
                outgoing[a] += 1;
                edges.push((e, a, z, *from, *to));
            }
        }
        if let Some(t) = g.owner[e].filter(|&p| is(&r.b, p, "TransitionUsage")) {
            let unit = r.b.unit_of_elem(t);
            if !model.is_library_unit(unit) && z != *to && !g.effective_kind(&r.b, z, "ActionUsage")
            {
                out.push((
                    unit,
                    super::rule_error(
                        g.span(&r.b, t),
                        "validateTransitionUsageSuccession",
                        "A transition's succession must target an action usage",
                    ),
                ));
            }
        }
    }
    for (edge, a, z, from, to) in edges {
        let unit = r.b.unit_of_elem(edge);
        if model.is_library_unit(unit) {
            continue;
        }
        for (end, required, rule) in [
            (
                to,
                (1.0, 1.0),
                is(&r.b, z, "ControlNode").then_some("validateControlNodeIncomingSuccessions"),
            ),
            (
                from,
                (1.0, 1.0),
                is(&r.b, a, "ControlNode").then_some("validateControlNodeOutgoingSuccessions"),
            ),
            (
                from,
                (0.0, 1.0),
                is(&r.b, z, "MergeNode").then_some("validateMergeNodeIncomingSuccessions"),
            ),
            (
                to,
                (0.0, 1.0),
                is(&r.b, a, "DecisionNode").then_some("validateDecisionNodeOutgoingSuccessions"),
            ),
        ] {
            if let Some(rule) = rule {
                if r.declared_multiplicity(ElementRef(end))
                    .is_some_and(|m| m != required)
                {
                    out.push((
                        unit,
                        super::rule_error(
                            g.span(&r.b, edge),
                            rule,
                            format!(
                                "Succession end must have multiplicity {}..{}",
                                required.0, required.1
                            ),
                        ),
                    ));
                }
            }
        }
    }
    for e in 0..n {
        let unit = r.b.unit_of_elem(e);
        if model.is_library_unit(unit) {
            continue;
        }
        let span = g.span(&r.b, e);
        for (bad, rule) in [
            (
                is(&r.b, e, "ForkNode") && incoming[e] > 1,
                "validateForkNodeIncomingSuccessions",
            ),
            (
                is(&r.b, e, "DecisionNode") && incoming[e] > 1,
                "validateDecisionNodeIncomingSuccessions",
            ),
            (
                is(&r.b, e, "JoinNode") && outgoing[e] > 1,
                "validateJoinNodeOutgoingSuccessions",
            ),
            (
                is(&r.b, e, "MergeNode") && outgoing[e] > 1,
                "validateMergeNodeOutgoingSuccessions",
            ),
        ] {
            if bad {
                out.push((
                    unit,
                    super::rule_error(
                        span,
                        rule,
                        format!(
                            "Control node has too many {} successions",
                            if rule.contains("Incoming") {
                                "incoming"
                            } else {
                                "outgoing"
                            }
                        ),
                    ),
                ));
            }
        }
        if is(&r.b, e, "TransitionUsage") {
            let triggered = r.b.elements[e].owned_relationships.iter().any(|&rel| {
                is(&r.b, rel, "TransitionFeatureMembership")
                    && r.b.elements[rel].props.get("kind").and_then(|x| x.as_str())
                        == Some("trigger")
            });
            if triggered
                && g.relations(&r.b, e, "Membership", "memberElement")
                    .iter()
                    .any(|&s| !g.effective_kind(&r.b, s, "StateUsage"))
            {
                out.push((
                    unit,
                    super::rule_error(
                        span,
                        "validateTransitionUsageTriggerActions",
                        "A triggered transition must have a state usage as its source",
                    ),
                ));
            }
        }
        let params: Vec<_> = g.members[e]
            .iter()
            .copied()
            .filter(|&m| {
                r.b.elements[m]
                    .owning_relationship
                    .is_some_and(|rel| is(&r.b, rel, "ParameterMembership"))
            })
            .collect();
        if is(&r.b, e, "AssignmentActionUsage") {
            if let Some((scope, expr)) = params
                .first()
                .and_then(|p| r.b.contract_exprs.get(p))
                .cloned()
            {
                if let Some(t) = expressions::referent(&mut r.b, scope, &expr) {
                    let rule = if !is(&r.b, t, "Feature") {
                        Some((
                            "validateAssignmentActionUsageReferent",
                            "An assignment must refer to a feature",
                        ))
                    } else if !super::structural::variable(&r.b, g, t) {
                        Some((
                            "validateAssignmentActionUsageReferentIsTimeVarying",
                            "An assignment referent must be time varying",
                        ))
                    } else {
                        None
                    };
                    if let Some((rule, msg)) = rule {
                        out.push((unit, super::rule_error(expr.span, rule, msg)));
                    }
                }
            }
        }
        if is(&r.b, e, "SendActionUsage") {
            let needs_payload = r.b.elements[e].owning_relationship.is_some_and(|rel| {
                is(&r.b, rel, "StateSubactionMembership")
                    || is(&r.b, rel, "TransitionFeatureMembership")
            });
            if needs_payload
                && params
                    .first()
                    .is_some_and(|p| !r.b.contract_exprs.contains_key(p))
            {
                out.push((unit, super::rule_error(span, "validateSendActionUsagePayloadArgument", "A send used as a state subaction or transition effect must supply a payload")));
            }
            if let Some((scope, expr)) = params
                .get(2)
                .and_then(|p| r.b.contract_exprs.get(p))
                .cloned()
            {
                if expressions::referent(&mut r.b, scope, &expr)
                    .is_some_and(|t| g.effective_kind(&r.b, t, "PortUsage"))
                {
                    out.push((
                        unit,
                        super::rule_warning(
                            expr.span,
                            "validateSendActionUsageReceiver",
                            "Sending through a port should use 'via'",
                        ),
                    ));
                }
            }
        }
        if is(&r.b, e, "TriggerInvocationExpression") {
            let kind = r.b.elements[e]
                .props
                .get("kind")
                .and_then(|v| v.as_str())
                .unwrap_or("")
                .to_owned();
            let Some((scope, expr)) = r.b.contract_exprs.get(&e).cloned() else {
                continue;
            };
            let (required, rule) = match kind.as_str() {
                "after" => (
                    "ISQ::DurationValue",
                    "validateTriggerInvocationActionAfterArgument",
                ),
                "at" => (
                    "Time::TimeInstantValue",
                    "validateTriggerInvocationActionAtArgument",
                ),
                "when" => (
                    "ScalarValues::Boolean",
                    "validateTriggerInvocationActionWhenArgument",
                ),
                _ => continue,
            };
            let mut bad = expressions::wrong_type(&mut r.b, g, scope, &expr, required);
            if kind == "after" {
                if let Some(t) = expressions::library_type(&mut r.b, required) {
                    if let (Some(actual), Some(expected)) = (
                        super::dimensions::known(r, scope, &expr),
                        r.quantity_dims_of_type(ElementRef(t)),
                    ) {
                        bad |= actual != expected;
                    }
                }
            }
            if bad {
                out.push((
                    unit,
                    super::rule_error(
                        expr.span,
                        rule,
                        format!("A '{kind}' trigger argument must conform to {required}"),
                    ),
                ));
            }
        }
    }
    for (e, (scope, expr)) in super::user_entries(&r.b, model, r.b.transition_guards.iter()) {
        let unit = r.b.unit_of_elem(e);
        let mut bad = expressions::wrong_type(&mut r.b, g, scope, &expr, "ScalarValues::Boolean");
        if let Some(t) = expressions::referent(&mut r.b, scope, &expr) {
            bad |= r
                .declared_multiplicity(ElementRef(t))
                .is_some_and(|m| m != (1.0, 1.0));
        }
        if bad {
            out.push((
                unit,
                super::rule_error(
                    expr.span,
                    "validateTransitionFeatureMembershipGuardExpression",
                    "A transition guard must have a Boolean result with multiplicity 1..1",
                ),
            ));
        }
    }
    out
}
