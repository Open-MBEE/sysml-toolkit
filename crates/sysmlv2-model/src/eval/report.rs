//! Bounded observations of failures hidden by inherited-default fallback.
//!
//! Reporting does not change evaluation's result or consume its semantic
//! budgets. A clean report does not certify concrete values or conformance.

use super::{EvalError, Value};
use crate::json::{ElementRef, ScopeRef};
use sysmlv2_syntax::Span;

const MAX_EVENTS: usize = 256;
const MAX_PATH: usize = 64;
const MAX_BYTES: usize = 1 << 20;

/// One feature-value dependency in evaluation order. This is not a complete
/// expression or calculation call stack.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct EvaluationDependency {
    /// Feature whose value was requested.
    pub requested: ElementRef,
    /// Feature declaring the selected value expression.
    pub origin: ElementRef,
    /// Featuring context used to evaluate that expression.
    pub receiver: ScopeRef,
}

/// A failed inherited default replaced by a compatibility placeholder.
#[derive(Clone, Debug, PartialEq)]
pub struct InheritedDefaultFailure {
    /// Feature whose inherited default failed.
    pub requested: ElementRef,
    /// Feature declaring that default expression.
    pub origin: ElementRef,
    /// Featuring context in which the failure occurred.
    pub receiver: ScopeRef,
    /// Source unit of the default declaration, independent of its receiver.
    pub source_unit: usize,
    /// Source span of the selected default expression.
    pub source_span: Span,
    /// Original failure, retained without changing its category or message.
    pub error: EvalError,
    /// Feature dependency ancestry, ending with this attempted default.
    pub dependency_path: Vec<EvaluationDependency>,
}

/// Compatibility evaluation result plus causes hidden by default fallback.
///
/// Reporting retains at most 256 events, 64 feature dependencies per event,
/// and 1 MiB of accounted collector/event/path/error-string storage. These
/// limits are separate from evaluation's semantic budgets. If any diagnostic
/// or dependency ancestry cannot be retained completely,
/// [`Self::diagnostics_truncated`] is set and checked conversion rejects the
/// report. Evaluation itself continues with the compatibility behavior.
#[derive(Clone, Debug, PartialEq)]
pub struct EvaluationReport {
    /// The same result returned by the corresponding compatibility API.
    pub result: Result<Value, EvalError>,
    /// First failures observed on branches actually evaluated.
    pub inherited_default_failures: Vec<InheritedDefaultFailure>,
    /// Diagnostic events or dependency ancestry exceeded reporting limits.
    /// Evaluation continues normally; checked conversion rejects this report.
    pub diagnostics_truncated: bool,
}

impl EvaluationReport {
    /// Return a value only when evaluation succeeded without hidden failures or
    /// truncated diagnostics. Unbound/indeterminate values remain values; this
    /// does not certify complete evaluability or model conformance. Rejection
    /// returns the complete report in a box.
    pub fn into_checked_result(self) -> Result<Value, Box<Self>> {
        if self.result.is_ok()
            && self.inherited_default_failures.is_empty()
            && !self.diagnostics_truncated
        {
            // The checked branch guarantees this is Ok; matching avoids an
            // unwrap and preserves the whole report in the error branch below.
            match self.result {
                Ok(value) => Ok(value),
                Err(_) => unreachable!(),
            }
        } else {
            Err(Box::new(self))
        }
    }
}

/// One optional boxed collector per evaluator. Legacy entrypoints use None,
/// avoiding the fixed active-stack storage as well as path/event allocations. Accounting is independent of evaluator
/// step/allocation limits so observation cannot alter compatibility results.
pub(super) struct Collector {
    active: [Option<EvaluationDependency>; MAX_PATH],
    active_len: usize,
    overflow_depth: usize,
    failures: Vec<InheritedDefaultFailure>,
    payload_bytes: usize,
    truncated: bool,
}

impl Default for Collector {
    fn default() -> Self {
        Self {
            active: [None; MAX_PATH],
            active_len: 0,
            overflow_depth: 0,
            failures: Vec::new(),
            payload_bytes: 0,
            truncated: false,
        }
    }
}

fn fits(parts: &[usize]) -> Option<usize> {
    parts.iter().try_fold(0usize, |total, &part| {
        total.checked_add(part).filter(|&sum| sum <= MAX_BYTES)
    })
}

fn error_capacity(error: &EvalError) -> usize {
    match error {
        EvalError::Unresolved(s)
        | EvalError::Unsupported(s)
        | EvalError::Type(s)
        | EvalError::Cycle(s)
        | EvalError::Budget(s) => s.capacity(),
        EvalError::DivisionByZero => 0,
    }
}

impl Collector {
    pub(super) fn push(&mut self, dependency: EvaluationDependency) {
        if self.active_len < MAX_PATH && self.overflow_depth == 0 {
            self.active[self.active_len] = Some(dependency);
            self.active_len += 1;
        } else {
            // Evaluation already bounds total operations. Saturation is a
            // defensive guard; reaching usize::MAX nested calls is impossible.
            self.overflow_depth = self.overflow_depth.saturating_add(1);
        }
    }

    pub(super) fn pop(&mut self) {
        if self.overflow_depth != 0 {
            self.overflow_depth -= 1;
        } else if self.active_len != 0 {
            self.active_len -= 1;
            self.active[self.active_len] = None;
        } else {
            debug_assert!(false, "unbalanced evaluation dependency stack");
        }
    }

    pub(super) fn record(
        &mut self,
        dependency: EvaluationDependency,
        source_unit: usize,
        source_span: Span,
        error: EvalError,
    ) {
        if self.failures.len() >= MAX_EVENTS {
            self.truncated = true;
            return;
        }
        // Keep a prefix and the terminal attempted default if ancestry is too
        // deep. Never mark deep but wholly successful evaluation truncated.
        let lost_path = self.overflow_depth != 0;
        self.truncated |= lost_path;
        let path_len = if lost_path { MAX_PATH } else { self.active_len };
        let Some(path_bytes) = path_len.checked_mul(size_of::<EvaluationDependency>()) else {
            self.truncated = true;
            return;
        };
        // Reserve a bounded event table once, after checking the payload. This
        // includes Vec capacity rather than only occupied event slots.
        let event_capacity = self.failures.capacity().max(MAX_EVENTS);
        let Some(event_bytes) = event_capacity.checked_mul(size_of::<InheritedDefaultFailure>())
        else {
            self.truncated = true;
            return;
        };
        let Some(payload_bytes) = fits(&[self.payload_bytes, error_capacity(&error), path_bytes])
        else {
            self.truncated = true;
            return;
        };
        if fits(&[size_of::<Self>(), event_bytes, payload_bytes]).is_none() {
            self.truncated = true;
            return;
        }
        if self.failures.capacity() == 0 {
            self.failures.reserve_exact(MAX_EVENTS);
        }
        let mut dependency_path = Vec::with_capacity(path_len);
        let retained_prefix = if lost_path { MAX_PATH - 1 } else { path_len };
        dependency_path.extend(self.active[..retained_prefix].iter().flatten().copied());
        if lost_path {
            dependency_path.push(dependency);
        }
        // Account actual capacities too; allocator capacity is permitted to
        // exceed the requested amount. Never retain an over-budget event.
        let actual_event_bytes = self
            .failures
            .capacity()
            .checked_mul(size_of::<InheritedDefaultFailure>());
        let actual_path_bytes = dependency_path
            .capacity()
            .checked_mul(size_of::<EvaluationDependency>());
        let retained = actual_event_bytes
            .zip(actual_path_bytes)
            .and_then(|(events, path)| {
                let payload = fits(&[self.payload_bytes, error_capacity(&error), path])?;
                fits(&[size_of::<Self>(), events, payload]).map(|_| payload)
            });
        let Some(retained) = retained else {
            // A first reserve may report more capacity than requested. Drop
            // that empty table rather than retaining an over-budget allocation.
            // Nonempty accepted tables never grow beyond their fixed capacity.
            if self.failures.is_empty() {
                self.failures = Vec::new();
            }
            self.truncated = true;
            return;
        };
        self.payload_bytes = retained;
        self.failures.push(InheritedDefaultFailure {
            requested: dependency.requested,
            origin: dependency.origin,
            receiver: dependency.receiver,
            source_unit,
            source_span,
            error,
            dependency_path,
        });
    }

    pub(super) fn finish(self, result: Result<Value, EvalError>) -> EvaluationReport {
        EvaluationReport {
            result,
            inherited_default_failures: self.failures,
            diagnostics_truncated: self.truncated,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn dep(index: usize) -> EvaluationDependency {
        EvaluationDependency {
            requested: ElementRef(index),
            origin: ElementRef(index + 1),
            receiver: ScopeRef(index + 2),
        }
    }

    #[test]
    fn retains_first_events_and_checked_conversion_rejects_truncation() {
        let mut collector = Collector::default();
        for index in 0..MAX_EVENTS + 3 {
            collector.push(dep(index));
            collector.record(dep(index), 7, Span::default(), EvalError::DivisionByZero);
            collector.pop();
        }
        let report = collector.finish(Ok(Value::Integer(9)));
        assert_eq!(report.inherited_default_failures.len(), MAX_EVENTS);
        assert_eq!(
            report.inherited_default_failures[0].requested,
            ElementRef(0)
        );
        assert_eq!(
            report.inherited_default_failures[MAX_EVENTS - 1].requested,
            ElementRef(MAX_EVENTS - 1)
        );
        assert!(report.diagnostics_truncated);
        assert!(report.into_checked_result().is_err());
    }

    #[test]
    fn accounts_string_capacity_not_length_and_recovers_for_new_query() {
        let mut message = String::with_capacity(MAX_BYTES);
        message.push('x');
        let mut collector = Collector::default();
        collector.push(dep(0));
        collector.record(dep(0), 7, Span::default(), EvalError::Unsupported(message));
        collector.pop();
        let report = collector.finish(Ok(Value::Integer(9)));
        assert!(report.inherited_default_failures.is_empty());
        assert!(report.diagnostics_truncated);
        assert!(report.into_checked_result().is_err());
        assert_eq!(
            Collector::default()
                .finish(Ok(Value::Integer(9)))
                .into_checked_result()
                .unwrap(),
            Value::Integer(9)
        );
        assert_eq!(fits(&[usize::MAX, 1]), None);
    }

    #[test]
    fn cumulative_payload_budget_stops_before_event_count_cap() {
        let mut collector = Collector::default();
        for index in 0..40 {
            let mut message = String::with_capacity(64 * 1024);
            message.push('x');
            collector.push(dep(index));
            collector.record(dep(index), 7, Span::default(), EvalError::Type(message));
            collector.pop();
        }
        assert!(
            fits(&[
                size_of::<Collector>(),
                collector.failures.capacity() * size_of::<InheritedDefaultFailure>(),
                collector.payload_bytes,
            ])
            .is_some()
        );
        let report = collector.finish(Ok(Value::Integer(9)));
        assert!(report.diagnostics_truncated);
        assert!(!report.inherited_default_failures.is_empty());
        assert!(report.inherited_default_failures.len() < 16);
        for (index, failure) in report.inherited_default_failures.iter().enumerate() {
            assert_eq!(failure.requested, ElementRef(index));
        }
    }

    #[test]
    fn bounds_ancestry_preserving_terminal_and_balances_overflow() {
        let mut collector = Collector::default();
        for index in 0..MAX_PATH + 3 {
            collector.push(dep(index));
        }
        collector.record(
            dep(MAX_PATH + 2),
            7,
            Span::default(),
            EvalError::Cycle("x".into()),
        );
        for _ in 0..MAX_PATH + 3 {
            collector.pop();
        }
        assert_eq!(collector.active_len, 0);
        assert_eq!(collector.overflow_depth, 0);
        collector.push(dep(91));
        collector.record(dep(91), 7, Span::default(), EvalError::DivisionByZero);
        collector.pop();
        let report = collector.finish(Ok(Value::Integer(9)));
        assert!(report.diagnostics_truncated);
        assert_eq!(
            report.inherited_default_failures[0].dependency_path.len(),
            MAX_PATH
        );
        assert_eq!(
            report.inherited_default_failures[0].dependency_path[0],
            dep(0)
        );
        assert_eq!(
            *report.inherited_default_failures[0]
                .dependency_path
                .last()
                .unwrap(),
            dep(MAX_PATH + 2)
        );
        assert_eq!(
            report.inherited_default_failures[1].dependency_path,
            [dep(91)]
        );
    }

    #[test]
    fn deep_success_does_not_claim_lost_diagnostics_and_errors_preserve_report() {
        let mut collector = Collector::default();
        for index in 0..MAX_PATH + 3 {
            collector.push(dep(index));
        }
        for _ in 0..MAX_PATH + 3 {
            collector.pop();
        }
        assert!(
            !collector
                .finish(Ok(Value::Indeterminate))
                .diagnostics_truncated
        );
        let report = Collector::default().finish(Err(EvalError::DivisionByZero));
        let report = report.into_checked_result().unwrap_err();
        assert_eq!(report.result, Err(EvalError::DivisionByZero));
    }
}
