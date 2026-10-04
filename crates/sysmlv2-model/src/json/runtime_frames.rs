//! Query-local admission proofs for monotonic runtime argument visibility.
//!
//! This provider proves eligibility at one declaration boundary. Callers must
//! intersect the result with the prior visible set and restore their masks on
//! return; a successful proof never re-enables an already hidden activation.

use super::parameter_context::{descendant, explicit_ancestor};
use super::{
    Builder, ElementRef, ResolvedModel, ScopeRef, provider_completeness::ProviderCompleteness,
};
use std::collections::HashMap;

/// One active calculation or lambda application. External query name bindings
/// are not runtime frames and retain their separate compatibility contract.
#[derive(Clone, Copy, Debug)]
pub struct RuntimeFrame {
    /// Actual calculation declaration, or `None` for a lambda application.
    pub callee: Option<ElementRef>,
    /// Declaration scope of this activation. A source-less query lambda has no
    /// model scope; using the global scope would incorrectly admit all callees.
    pub lexical_scope: Option<ScopeRef>,
    /// Actual featuring context used to evaluate this activation's defaults.
    /// It can differ from an inherited default's lexical declaration scope.
    pub receiver_scope: ScopeRef,
    /// Eligibility inherited from every surrounding declaration boundary.
    pub visible: bool,
}

impl RuntimeFrame {
    /// Start a calculation activation in its own body/receiver scope.
    pub fn calculation(callee: ElementRef, scope: ScopeRef) -> Self {
        Self {
            callee: Some(callee),
            lexical_scope: Some(scope),
            receiver_scope: scope,
            visible: true,
        }
    }

    /// Start a distinct lambda activation, including inside calculations.
    pub fn lambda(lexical_scope: Option<ScopeRef>, receiver_scope: ScopeRef) -> Self {
        Self {
            callee: None,
            lexical_scope,
            receiver_scope,
            visible: true,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
struct AdmissionKey {
    callee: Option<ElementRef>,
    declaration: ScopeRef,
    frame_receiver: ScopeRef,
    lexical: ScopeRef,
    receiver: ScopeRef,
}

/// Memoized proofs for one immutable-model evaluation. Discard before mutating
/// identities, relationship endpoints, imports, or other model configuration.
#[derive(Default)]
pub struct RuntimeFrameProof {
    providers: ProviderCompleteness,
    known: HashMap<AdmissionKey, bool>,
}

fn charge(steps: &mut usize, amount: usize) -> Option<()> {
    *steps = steps.saturating_add(amount);
    (*steps <= crate::eval::MAX_STEPS).then_some(())
}

impl RuntimeFrameProof {
    /// Whether its proofs answer as a fresh one's would (see
    /// [`ProviderCompleteness::current`]).
    pub(crate) fn current(&self, b: &Builder) -> bool {
        self.providers.current(b)
    }

    /// Whether an existing visible activation remains eligible when entering
    /// a model declaration. `None` means incomplete evidence or exhausted
    /// budget and must be propagated as unsupported. Hidden frames stay hidden.
    ///
    /// Syntactic lambda bodies are lexical continuations: callers preserve
    /// the current visible set and push a new frame there, rather than applying
    /// this declaration boundary (or inventing a root scope for query lambdas).
    pub fn permits(
        &mut self,
        model: &mut ResolvedModel,
        frame: RuntimeFrame,
        lexical: ScopeRef,
        receiver: ScopeRef,
        steps: &mut usize,
    ) -> Option<bool> {
        self.permits_builder(&mut model.b, frame, lexical, receiver, steps)
    }

    pub(crate) fn permits_builder(
        &mut self,
        b: &mut Builder,
        frame: RuntimeFrame,
        lexical: ScopeRef,
        receiver: ScopeRef,
        steps: &mut usize,
    ) -> Option<bool> {
        charge(steps, 1)?;
        if !frame.visible {
            return Some(false);
        }
        if !b.semantic_ready {
            return None;
        }
        b.scopes.get(lexical.0)?;
        b.scopes.get(receiver.0)?;
        let Some(declaration) = frame.lexical_scope else {
            return frame.callee.is_none().then_some(false);
        };
        let key = AdmissionKey {
            callee: frame.callee,
            declaration,
            frame_receiver: frame.receiver_scope,
            lexical,
            receiver,
        };
        if let Some(&known) = self.known.get(&key) {
            return Some(known);
        }
        let result = self.prove(b, frame, declaration, lexical, receiver, steps)?;
        self.known.insert(key, result);
        Some(result)
    }

    fn prove(
        &mut self,
        b: &mut Builder,
        frame: RuntimeFrame,
        declaration: ScopeRef,
        lexical: ScopeRef,
        receiver: ScopeRef,
        steps: &mut usize,
    ) -> Option<bool> {
        // Ordinary nested lexical capture needs no inheritance approximation.
        if descendant(b, lexical.0, declaration.0, steps)? {
            return Some(true);
        }
        let Some(callee) = frame.callee else {
            return Some(false);
        };
        let callee_scope = *b.elem_scope.get(&callee.0)?;
        // A value from an ancestor declaration may use the active specializing
        // calculation's arguments only in that calculation's actual context.
        if !descendant(b, receiver.0, callee_scope, steps)? {
            return Some(false);
        }
        if !self.providers.scope(b, callee_scope, steps) {
            return None;
        }
        let Some(owner) = b.nearest_scope_owner(lexical.0) else {
            return Some(false);
        };
        explicit_ancestor(b, callee.0, owner, steps)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::model::Model;

    fn model() -> ResolvedModel {
        let mut m = Model::new();
        m.add_source(
            "frames.sysml",
            "calc def Base { in p; attribute v=p; calc def Nested {Base::p}
            attribute values=(1,2)->collect {in lambdaInput; lambdaInput}; }
            calc def Child :> Base {in q :>> Base::p;}
            calc def Other {Base::p}
            package Constants {attribute value=Base::p;}",
        );
        assert!(!m.has_errors());
        ResolvedModel::build(&m)
    }

    fn scope(r: &mut ResolvedModel, name: &str) -> (ElementRef, ScopeRef) {
        let element = r.resolve_qualified(name).unwrap();
        (element, r.element_scope(element).unwrap())
    }

    #[test]
    fn frames_distinguish_lexical_and_receiver_admission() {
        let mut r = model();
        let (base, base_scope) = scope(&mut r, "Base");
        let (child, child_scope) = scope(&mut r, "Child");
        let (_, nested) = scope(&mut r, "Base::Nested");
        let (_, other) = scope(&mut r, "Other");
        let (_, constants) = scope(&mut r, "Constants");
        let mut proof = RuntimeFrameProof::default();
        let base_frame = RuntimeFrame::calculation(base, base_scope);
        assert_eq!(
            proof.permits(&mut r, base_frame, nested, nested, &mut 0),
            Some(true)
        );
        assert_eq!(
            proof.permits(&mut r, base_frame, other, other, &mut 0),
            Some(false)
        );
        assert_eq!(
            proof.permits(&mut r, base_frame, constants, base_scope, &mut 0),
            Some(false)
        );
        let child_frame = RuntimeFrame::calculation(child, child_scope);
        assert_eq!(
            proof.permits(&mut r, child_frame, base_scope, child_scope, &mut 0),
            Some(true)
        );
        assert_eq!(
            proof.permits(&mut r, child_frame, base_scope, base_scope, &mut 0),
            Some(false)
        );
    }

    #[test]
    fn cached_admission_never_reactivates_a_hidden_frame() {
        let mut r = model();
        let (base, s) = scope(&mut r, "Base");
        let mut frame = RuntimeFrame::calculation(base, s);
        let mut proof = RuntimeFrameProof::default();
        assert_eq!(proof.permits(&mut r, frame, s, s, &mut 0), Some(true));
        frame.visible = false;
        assert_eq!(proof.permits(&mut r, frame, s, s, &mut 0), Some(false));
        frame.visible = true;
        let mut exhausted = crate::eval::MAX_STEPS;
        assert_eq!(proof.permits(&mut r, frame, s, s, &mut exhausted), None);
        assert_eq!(proof.permits(&mut r, frame, s, s, &mut 0), Some(true));
    }

    #[test]
    fn lambdas_have_their_own_declared_scope_or_no_declaration_scope() {
        let mut r = model();
        let (_, base_scope) = scope(&mut r, "Base");
        let p =
            r.b.elements
                .iter()
                .position(|e| {
                    e.props.get("declaredName").and_then(|v| v.as_str()) == Some("lambdaInput")
                })
                .unwrap();
        let lambda_scope = ScopeRef(r.b.owner_scope_of(p).unwrap());
        let mut proof = RuntimeFrameProof::default();
        let frame = RuntimeFrame::lambda(Some(lambda_scope), base_scope);
        assert_eq!(
            proof.permits(&mut r, frame, lambda_scope, base_scope, &mut 0),
            Some(true)
        );
        assert_eq!(
            proof.permits(&mut r, frame, base_scope, base_scope, &mut 0),
            Some(false)
        );
        let query_frame = RuntimeFrame::lambda(None, base_scope);
        assert_eq!(
            proof.permits(&mut r, query_frame, lambda_scope, base_scope, &mut 0),
            Some(false)
        );
    }
}
