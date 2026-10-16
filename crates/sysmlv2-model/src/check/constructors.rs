//! Constructor arguments, checked as the feature values they are. `new
//! T(…)` binds each argument to one public feature of `T`: a positional
//! argument the feature at its position in `T`'s constructor sequence
//! (the type's own public features in declaration order, then the
//! inherited ones — `json::constructor_sequence`), a named argument the
//! feature of that name. Reported: an argument binding a feature whose
//! own value, or the value of a feature it redefines, is not a default
//! (`validateFeatureValueOverriding`), and an argument whose evaluated
//! scalar partition can never inhabit the bound feature's declared type
//! (the feature-value discipline of `scalars`); also a positional and a
//! named argument landing on one feature
//! (`validateConstructorExpressionNoDuplicateFeatureRedefinition`, which
//! the expression check reports for two named ones), and a positional
//! argument on a feature nothing can name (an invariant, a result
//! expression — usually a sequence meant as one argument). An argument
//! past the features of the type and its written generals lands on a
//! feature of an implied library base and is not checked; a named
//! argument naming no feature is the resolver's unresolved reference.
//! A lambda body is not entered from the expression around it — its
//! trailing expression is a result expression, checked in the body's
//! own scope, where an argument bound through a body parameter is
//! undecided.
use super::scalars::{
    declared_kinds, declared_type_name, never_conforms_message, scalar_kind_admits,
    value_scalar_kind,
};
use crate::{
    json::{ElementRef, ResolvedModel},
    model::Model,
};
use std::collections::HashMap;
use sysmlv2_syntax::ast::{Arg, Expr, ExprKind, TargetRef};
use sysmlv2_syntax::diag::Diagnostic;
use sysmlv2_syntax::visit::{Visit, walk_expr};

pub(super) fn validate(r: &mut ResolvedModel, model: &Model) -> Vec<(usize, Diagnostic)> {
    let mut out = Vec::new();
    let mut sites: Vec<(usize, usize, Expr)> =
        r.b.values
            .iter()
            .filter(|(o, _)| super::user_owned(&r.b, model, **o))
            .map(|(o, (s, e))| (*o, *s, e.clone()))
            .collect();
    sites.extend(
        r.b.result_exprs
            .iter()
            .filter(|row| super::user_owned(&r.b, model, row.0))
            .cloned(),
    );
    for (owner, scope, expr) in sites {
        let unit = r.b.unit_of_elem(owner);
        if model.is_library_unit(unit) {
            continue;
        }
        let mut found = Constructors { out: Vec::new() };
        found.visit_expr(&expr);
        if found.out.is_empty() {
            continue;
        }
        let origin = r.b.set_identity_origin(owner);
        for (ty, args) in found.out {
            check_site(r, model, unit, scope, ty, args, &mut out);
        }
        r.b.identity_origin_unit = origin;
    }
    out
}

/// Every constructor expression in an expression tree, outside lambda
/// bodies.
struct Constructors<'a> {
    out: Vec<(&'a TargetRef, &'a [Arg])>,
}

impl<'a> Visit<'a> for Constructors<'a> {
    fn visit_expr(&mut self, e: &'a Expr) {
        match &e.kind {
            // A body's expressions bind through its own parameters;
            // evaluated in the site scope they would read whatever those
            // names mean outside.
            ExprKind::Body { .. } => return,
            ExprKind::Constructor { ty, args } => self.out.push((ty, args)),
            _ => {}
        }
        walk_expr(self, e);
    }
}

fn check_site(
    r: &mut ResolvedModel,
    model: &Model,
    unit: usize,
    scope: usize,
    ty: &TargetRef,
    args: &[Arg],
    out: &mut Vec<(usize, Diagnostic)>,
) {
    let TargetRef::Name(qn) = ty else {
        return;
    };
    let Some(elem) = r.b.resolve(scope, qn, 0) else {
        return;
    };
    let sequence = r.b.constructor_feature_sequence(elem);
    if sequence.is_empty() {
        return;
    }
    let type_name = qn.to_display_string();
    // Features already bound, with the spelling of the name that bound
    // them (`None` for a positional argument).
    let mut bound: HashMap<usize, Option<String>> = HashMap::new();
    let mut positional = 0usize;
    for arg in args {
        let spelled = arg.name.as_ref().map(|n| n.to_display_string());
        let slot = match &spelled {
            Some(name) => sequence.iter().find(|(n, _)| n == name),
            None => {
                let at = positional;
                positional += 1;
                sequence.get(at)
            }
        };
        let Some((name, feature)) = slot else {
            continue;
        };
        let (name, feature) = (name.clone(), *feature);
        if let Some(earlier) = bound.insert(feature, spelled.clone()) {
            // Two named arguments on one feature spell one name — the
            // expression check's finding; a positional argument meeting
            // a named one is this check's.
            if earlier.is_none() || spelled.is_none() {
                out.push((
                    unit,
                    super::rule_error(
                        arg.value.span,
                        "validateConstructorExpressionNoDuplicateFeatureRedefinition",
                        format!("A constructor cannot bind `{name}` more than once"),
                    ),
                ));
            }
            continue;
        }
        if name.is_empty() {
            out.push((
                unit,
                Diagnostic::warning(
                    arg.value.span,
                    format!(
                        "positional argument {} binds a feature of `{type_name}` that nothing \
                         can name (an invariant or result expression); a sequence value is \
                         one argument, `({}…)`",
                        positional,
                        if positional > 1 { "…, " } else { "" }
                    ),
                ),
            ));
            continue;
        }
        if let Some(valued) = r.b.non_default_binding(feature) {
            let valued_name = r
                .element_qualified_name(ElementRef(valued))
                .unwrap_or_else(|| format!("@{}", r.element_id(ElementRef(valued))));
            let target_unit = r.b.unit_of_elem(valued);
            let binding_span =
                r.b.values
                    .get(&valued)
                    .map_or(arg.value.span, |(_, v)| v.span);
            // The unit's name and line index alone: a library unit's syntax
            // is not reconstructed for them.
            let (source_name, lines) = model.unit_meta(target_unit);
            let position = lines.line_col(binding_span.start);
            out.push((
                unit,
                super::rule_error(
                    arg.value.span,
                    "validateFeatureValueOverriding",
                    format!(
                        "Constructor argument for `{name}` cannot override the non-default \
                         value of `{valued_name}`, bound at {}:{}:{}; the value must be \
                         default to allow a new value",
                        source_name, position.line, position.col
                    ),
                ),
            ));
            continue;
        }
        let tys = r.b.declared_or_borrowed_typings(feature);
        let Some(kinds) = declared_kinds(&mut r.b, &tys) else {
            continue;
        };
        let Ok(v) = crate::eval::evaluate_expr_in(&mut r.b, scope, &arg.value) else {
            continue; // undecided, not wrong
        };
        let Some(value_kind) = value_scalar_kind(&v) else {
            continue;
        };
        if kinds.iter().any(|&k| scalar_kind_admits(k, value_kind)) {
            continue;
        }
        let ty_name = declared_type_name(&r.b, tys[0]);
        let subject = format!("constructor argument for `{name}`");
        out.push((
            unit,
            Diagnostic::warning(
                arg.value.span,
                never_conforms_message(&subject, &kinds, value_kind, &v, &ty_name),
            ),
        ));
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn findings(src: &str) -> Vec<String> {
        let mut model = Model::new();
        model.add_source("t.sysml", src);
        assert!(!model.has_errors());
        let mut r = ResolvedModel::build(&model);
        let mut out = validate(&mut r, &model);
        out.sort_by_key(|(_, d)| d.span.start);
        out.into_iter()
            .map(|(_, d)| format!("{:?}: {}", d.severity, d.message))
            .collect()
    }

    const DEFS: &str = "package P {
        attribute def String;
        attribute def Integer;
        attribute def Enc :> String;
        attribute def D {
            attribute val : Enc;
            attribute n : Integer = 1;
            attribute d : Integer default 2;
            private attribute hidden : Integer;
        }
        attribute def E :> D {
            attribute :>> val : Enc;
            attribute extra : Integer;
        }
    ";

    #[test]
    fn positional_arguments_take_public_features_in_sequence_order() {
        // `D`'s sequence is val, n, d (`hidden` is private); `E`'s is its
        // own val and extra, then D's n and d (D's val is redefined).
        let out = findings(&format!(
            "{DEFS}
            attribute a : D = new D(3);
            attribute b : D = new D(\"s\", 7);
            attribute c : D = new D(\"s\");
            attribute f : E = new E(\"s\", 7, 8, 9);
            attribute g : E = new E(\"s\", 7);
        }}"
        ));
        assert_eq!(out.len(), 3, "{out:#?}");
        assert!(out[0].contains("Warning") && out[0].contains(
            "constructor argument for `val` evaluates to a number, which can never conform to the declared type `Enc`"
        ), "{}", out[0]);
        assert!(out[1].contains("Error") && out[1].contains(
            "Constructor argument for `n` cannot override the non-default value of `P::D::n`, bound at t.sysml:"
        ) && out[1].contains("[validateFeatureValueOverriding]"), "{}", out[1]);
        assert!(
            out[2].contains("Constructor argument for `n` cannot override"),
            "{}",
            out[2]
        );
    }

    #[test]
    fn named_arguments_bind_by_name() {
        let out = findings(&format!(
            "{DEFS}
            attribute e : D = new D(val = 3);
            attribute g : D = new D(d = 5);
            attribute h : E = new E(val = \"ok\", extra = 1.5);
            attribute i : D = new D(n = 2);
        }}"
        ));
        assert_eq!(out.len(), 3, "{out:#?}");
        assert!(
            out[0].contains("constructor argument for `val` evaluates to a number"),
            "{}",
            out[0]
        );
        assert!(out[1].contains("constructor argument for `extra` 1.5 is not an integer and can never conform to the declared type `Integer`"), "{}", out[1]);
        assert!(
            out[2].contains(
                "Constructor argument for `n` cannot override the non-default value of `P::D::n`"
            ),
            "{}",
            out[2]
        );
    }

    #[test]
    fn arguments_past_the_written_sequence_and_unknown_names_stay_silent() {
        // Past `F`'s one written feature, arguments land on the features
        // of its implied library base, which this check does not model.
        let out = findings(&format!(
            "{DEFS}
            attribute def F {{ attribute val : Enc; }}
            attribute a : F = new F(\"s\", 2, 3, true, 1.5);
            attribute b : D = new D(nope = 3);
            attribute c : D = new D();
        }}"
        ));
        assert_eq!(out, Vec::<String>::new());
    }

    #[test]
    fn result_expressions_are_checked_and_lambda_bodies_are_not() {
        // A body's `x` is its own parameter, not the outer feature.
        let out = findings(&format!(
            "{DEFS}
            calc def Make {{ return : D = new D(true); }}
            attribute x = 3;
            attribute l = (\"a\", \"b\")->collect {{ in x; new D(x) }};
        }}"
        ));
        assert_eq!(out.len(), 1, "{out:#?}");
        assert!(
            out[0].contains("constructor argument for `val` evaluates to a Boolean"),
            "{}",
            out[0]
        );
    }

    #[test]
    fn a_positional_and_a_named_argument_on_one_feature_are_reported() {
        // Two named arguments spelling one name are the expression
        // check's finding; this check reports the positional meeting.
        let out = findings(&format!(
            "{DEFS}
            attribute a : D = new D(\"s\", val = \"t\");
            attribute b : D = new D(val = \"s\", val = \"t\");
        }}"
        ));
        assert_eq!(out.len(), 1, "{out:#?}");
        assert!(
            out[0].contains("A constructor cannot bind `val` more than once")
                && out[0].contains("[validateConstructorExpressionNoDuplicateFeatureRedefinition]"),
            "{}",
            out[0]
        );
    }

    #[test]
    fn a_positional_argument_on_a_nameless_feature_is_reported() {
        // `M`'s second public feature is its anonymous invariant: a
        // second argument is almost always a sequence meant as one.
        let out = findings(&format!(
            "{DEFS}
            attribute def M {{ attribute items : Integer[*]; assert constraint {{ true }} }}
            attribute m : M = new M(1, 2);
            attribute n : M = new M((1, 2));
        }}"
        ));
        assert_eq!(out.len(), 1, "{out:#?}");
        assert!(
            out[0].contains("positional argument 2 binds a feature of `M` that nothing can name"),
            "{}",
            out[0]
        );
    }

    #[test]
    fn typings_are_borrowed_along_the_redefinition_chain() {
        let out = findings(&format!(
            "{DEFS}
            attribute def F :> E {{ attribute :>> val; }}
            attribute def G :> F {{ attribute :>> val; }}
            attribute g : G = new G(3);
        }}"
        ));
        assert_eq!(out.len(), 1, "{out:#?}");
        assert!(
            out[0].contains("constructor argument for `val` evaluates to a number"),
            "{}",
            out[0]
        );
    }
}
