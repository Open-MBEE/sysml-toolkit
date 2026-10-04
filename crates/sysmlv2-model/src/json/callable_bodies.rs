//! The result an invocation of a callable evaluates: its own, or one its
//! written heritage declares.
use super::{Builder, ElementRef, ResolvedModel, ScopeRef};
use std::collections::HashSet;
use sysmlv2_syntax::ast::Expr;

/// How a callable declares its result.
#[derive(Clone, Debug, PartialEq)]
pub enum CallableResult {
    /// A trailing result expression, written in `scope`.
    Expression {
        /// The scope the expression is written in.
        scope: ScopeRef,
        /// The expression.
        expression: Expr,
    },
    /// A return parameter bound to a value (`return r = a - b;`).
    Parameter(ElementRef),
}

/// The result an invocation of a callable evaluates (see
/// [`ResolvedModel::callable_body`]).
#[derive(Clone, Debug, PartialEq)]
pub enum CallableBody {
    /// The result and the callable that declares it: the callee itself, or
    /// the nearest callable in its written heritage that declares one.
    Declared {
        /// The callable that declares the result.
        owner: ElementRef,
        /// The result it declares.
        result: CallableResult,
    },
    /// Different callables equally near the callee each declare a result.
    Ambiguous(Vec<ElementRef>),
}

/// A function or calculation-family metaclass: what an invocation applies.
pub(crate) fn calculation_like(ty: &str) -> bool {
    ty.contains("Calculation")
        || ty.contains("Constraint")
        || ty.contains("Expression")
        || ty == "Function"
        || ty == "Predicate"
}

impl Builder {
    /// The result `callable` declares itself.
    pub(crate) fn own_callable_result(&self, callable: usize) -> Option<CallableResult> {
        if let Some((_, scope, expression)) =
            self.result_exprs.iter().find(|(o, _, _)| *o == callable)
        {
            return Some(CallableResult::Expression {
                scope: ScopeRef(*scope),
                expression: expression.clone(),
            });
        }
        let &ret = self.return_params.get(&callable)?;
        self.values
            .contains_key(&ret)
            .then_some(CallableResult::Parameter(ElementRef(ret)))
    }

    /// See [`ResolvedModel::callable_body`]; statement execution is the
    /// caller's to refuse.
    pub(crate) fn callable_body(&mut self, callee: usize) -> Option<CallableBody> {
        if let Some(result) = self.own_callable_result(callee) {
            return Some(CallableBody::Declared {
                owner: ElementRef(callee),
                result,
            });
        }
        if !calculation_like(self.elements[callee].ty) || self.is_parameter(callee) {
            return None;
        }
        let mut seen = HashSet::from([callee]);
        let mut level = vec![callee];
        while !level.is_empty() {
            let mut next = Vec::new();
            for e in level {
                for general in self.explicit_supertype_elems(e) {
                    if seen.insert(general) {
                        next.push(general);
                    }
                }
            }
            let mut declared: Vec<_> = next
                .iter()
                .filter_map(|&general| Some((general, self.own_callable_result(general)?)))
                .collect();
            match declared.len() {
                0 => level = next,
                1 => {
                    let (owner, result) = declared.remove(0);
                    return Some(CallableBody::Declared {
                        owner: ElementRef(owner),
                        result,
                    });
                }
                _ => {
                    return Some(CallableBody::Ambiguous(
                        declared
                            .into_iter()
                            .map(|(owner, _)| ElementRef(owner))
                            .collect(),
                    ));
                }
            }
        }
        None
    }
}

impl ResolvedModel {
    /// The result an invocation of `callee` evaluates: the trailing result
    /// expression or bound return parameter it declares, else — for a
    /// calculation-family definition or usage — the nearest one its written
    /// heritage declares, breadth-first: a usage's definition's, a
    /// definition's general's. Evaluate an inherited result in the callee's
    /// context, where its arguments stand for the parameters they redefine.
    /// A function-typed parameter stands for an unknown calculation and
    /// inherits none. `None` when no result is declared, or the callee's
    /// body requires statement execution.
    pub fn callable_body(&mut self, callee: ElementRef) -> Option<CallableBody> {
        if self.b.indexed_calculation_requires_execution(callee.0) {
            return None;
        }
        self.b.callable_body(callee.0)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::model::Model;

    #[test]
    fn a_callable_without_a_result_takes_the_nearest_one_written() {
        let mut model = Model::new();
        model.add_source(
            "bodies.sysml",
            "calc def Diff { in a; in b; return r = a - b; }
             calc def Sum { in a; in b; a + b }
             calc def D3 :> Diff { in x; }
             calc def Deeper :> D3;
             calc def Own :> Diff { in x; x * 2 }
             calc typed : Sum;
             calc def Both :> Diff, Sum;
             calc def Holder { in fn : Diff; in g : Sum; }
             calc def Empty { in x; }",
        );
        assert!(!model.has_errors());
        let mut r = ResolvedModel::build(&model);
        let diff = r.resolve_qualified("Diff").unwrap();
        let sum = r.resolve_qualified("Sum").unwrap();
        let ret = r.resolve_qualified("Diff::r").unwrap();
        for (name, owner) in [("D3", diff), ("Deeper", diff), ("Diff", diff)] {
            let callee = r.resolve_qualified(name).unwrap();
            assert_eq!(
                r.callable_body(callee),
                Some(CallableBody::Declared {
                    owner,
                    result: CallableResult::Parameter(ret),
                }),
                "{name}"
            );
        }
        let typed = r.resolve_qualified("typed").unwrap();
        assert!(matches!(
            r.callable_body(typed),
            Some(CallableBody::Declared {
                owner,
                result: CallableResult::Expression { .. },
            }) if owner == sum
        ));
        let own = r.resolve_qualified("Own").unwrap();
        assert!(matches!(
            r.callable_body(own),
            Some(CallableBody::Declared { owner, .. }) if owner == own
        ));
        let both = r.resolve_qualified("Both").unwrap();
        assert_eq!(
            r.callable_body(both),
            Some(CallableBody::Ambiguous(vec![diff, sum]))
        );
        for name in ["Holder::fn", "Holder::g", "Empty"] {
            let callee = r.resolve_qualified(name).unwrap();
            assert_eq!(r.callable_body(callee), None, "{name}");
        }
    }
}
