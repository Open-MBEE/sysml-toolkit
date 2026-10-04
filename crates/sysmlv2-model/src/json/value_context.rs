//! Bounded, identity-based receiver selection for authored value expressions.
use super::{
    Builder, ElementRef, ResolvedModel, ScopeRef, provider_completeness::ProviderCompleteness,
};
use crate::metaclass::conforms;
use std::collections::{HashMap, HashSet};

/// Proven evaluation context for a stored value expression.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ValueScopeDecision {
    /// The caller has no applicable featuring receiver; use declaration scope.
    Lexical(ScopeRef),
    /// A complete, identity-based proof admits this featuring scope.
    Receiver(ScopeRef),
    /// Missing/ambiguous evidence or a resource limit prevents safe selection.
    Unsupported,
}

fn charge(steps: &mut usize, count: usize) -> Option<()> {
    *steps = steps.saturating_add(count);
    (*steps <= crate::eval::MAX_STEPS).then_some(())
}

/// Proof cache for one evaluation/query over one unchanged resolved model.
/// Do not reuse this cache for another model or after declaration/identity
/// mutation. IDs and relationships may change between queries; no facts here
/// are serialized.
#[derive(Default)]
pub struct ValueScopeResolver {
    providers: ProviderCompleteness,
    // Depth is part of the key: a shallow proof cannot bypass a later depth cap.
    reaches: HashMap<(usize, usize, usize), bool>,
}

impl ValueScopeResolver {
    /// Whether its proofs answer as a fresh resolver's would (see
    /// [`ProviderCompleteness::current`]).
    pub(crate) fn current(&self, b: &Builder) -> bool {
        self.providers.current(b)
    }

    /// Select a scope using query-local proofs. Do not retain this resolver
    /// across mutations of model declarations or identity bindings.
    pub fn select(
        &mut self,
        model: &mut ResolvedModel,
        element: ElementRef,
        receiver: Option<ScopeRef>,
        steps: &mut usize,
    ) -> ValueScopeDecision {
        self.select_builder(
            &mut model.b,
            element.0,
            receiver.map(|scope| scope.0),
            steps,
        )
    }

    pub(crate) fn select_builder(
        &mut self,
        b: &mut Builder,
        element: usize,
        receiver: Option<usize>,
        steps: &mut usize,
    ) -> ValueScopeDecision {
        self.select_inner(b, element, receiver, steps)
            .unwrap_or(ValueScopeDecision::Unsupported)
    }

    /// [`Self::select_builder`] for a value `element` reads through a
    /// relationship rather than an authored expression: `lexical` is the
    /// scope its written spelling resolves from.
    pub(crate) fn select_builder_at(
        &mut self,
        b: &mut Builder,
        element: usize,
        lexical: usize,
        receiver: Option<usize>,
        steps: &mut usize,
    ) -> ValueScopeDecision {
        (|| {
            charge(steps, 1)?;
            b.elements.get(element)?;
            self.select_from(b, element, lexical, receiver, steps)
        })()
        .unwrap_or(ValueScopeDecision::Unsupported)
    }

    fn select_inner(
        &mut self,
        b: &mut Builder,
        element: usize,
        receiver: Option<usize>,
        steps: &mut usize,
    ) -> Option<ValueScopeDecision> {
        charge(steps, 1)?;
        b.elements.get(element)?;
        let lexical = b.values.get(&element)?.0;
        self.select_from(b, element, lexical, receiver, steps)
    }

    fn select_from(
        &mut self,
        b: &mut Builder,
        element: usize,
        lexical: usize,
        receiver: Option<usize>,
        steps: &mut usize,
    ) -> Option<ValueScopeDecision> {
        b.scopes.get(lexical)?;
        let Some(receiver) = receiver else {
            return Some(ValueScopeDecision::Lexical(ScopeRef(lexical)));
        };
        b.scopes.get(receiver)?;
        if receiver == lexical {
            return Some(ValueScopeDecision::Receiver(ScopeRef(lexical)));
        }
        let Some(owner) = b.owner_elem(element) else {
            return Some(ValueScopeDecision::Lexical(ScopeRef(lexical)));
        };
        if !conforms(b.elements.get(owner)?.ty, "Type") {
            return Some(ValueScopeDecision::Lexical(ScopeRef(lexical)));
        }

        // Lambda/local scopes and nested declarations are not automatically the
        // featuring receiver. Prefer the nearest enclosing Type proven related
        // to the value's actual owner. An unrelated Type does not end the walk:
        // Child::Nested can read Base::v through its enclosing Child receiver.
        let mut candidate_scope = Some(receiver);
        let mut seen_scopes = HashSet::new();
        for _ in 0..=super::MAX_RESOLUTION_DEPTH {
            let Some(scope) = candidate_scope else {
                return Some(ValueScopeDecision::Lexical(ScopeRef(lexical)));
            };
            charge(steps, 1)?;
            if !seen_scopes.insert(scope) {
                return None;
            }
            let context = b.scopes.get(scope)?;
            let candidate = context.owner;
            candidate_scope = context.parent;
            if let Some(candidate) = candidate {
                if conforms(b.elements.get(candidate)?.ty, "Type") {
                    if candidate == owner {
                        return Some(ValueScopeDecision::Receiver(ScopeRef(scope)));
                    }
                    if !self.providers.scope(b, scope, steps) {
                        return None;
                    }
                    if self.semantically_reaches(
                        b,
                        candidate,
                        owner,
                        0,
                        &mut HashSet::new(),
                        steps,
                    )? {
                        return Some(ValueScopeDecision::Receiver(ScopeRef(scope)));
                    }
                }
            }
        }
        None
    }

    /// Complete closure of the implemented semantic bases, using stored UUID
    /// endpoints and the shared implied plan. Lookup-only name bases are not
    /// specialization evidence.
    /// Complete the closure after a match: another branch may be unresolved or
    /// cyclic, invalidating any claim that the receiver context is supported.
    fn semantically_reaches(
        &mut self,
        b: &mut Builder,
        current: usize,
        target: usize,
        depth: usize,
        active: &mut HashSet<usize>,
        steps: &mut usize,
    ) -> Option<bool> {
        charge(steps, 1)?;
        if depth > super::MAX_RESOLUTION_DEPTH {
            return None;
        }
        let key = (current, target, depth);
        if let Some(&found) = self.reaches.get(&key) {
            return Some(found);
        }
        if !conforms(b.elements.get(current)?.ty, "Type") || !active.insert(current) {
            return None;
        }
        let result = (|| {
            // Conjugation replaces ordinary supertypes. The legacy lookup
            // context can still include both on a malformed mixed declaration,
            // so it cannot safely supply inherited expression dependencies.
            let relationships = &b.elements[current].owned_relationships;
            charge(steps, relationships.len())?;
            let conjugated = relationships
                .iter()
                .any(|&r| conforms(b.elements[r].ty, "Conjugation"));
            if conjugated
                && relationships
                    .iter()
                    .any(|&r| conforms(b.elements[r].ty, "Specialization"))
            {
                return None;
            }
            let scope = *b.elem_scope.get(&current)?;
            if !self.providers.scope(b, scope, steps) {
                return None;
            }
            let mut found = current == target;
            for parent in b.value_context_bases(current, steps)? {
                found |= self.semantically_reaches(b, parent, target, depth + 1, active, steps)?;
            }
            Some(found)
        })();
        active.remove(&current);
        if let Some(found) = result {
            self.reaches.insert(key, found);
        }
        result
    }
}

impl ResolvedModel {
    /// Select the evaluation scope for an authored feature value. Qualified,
    /// aliased and ID-bound reads use the same already-resolved element identity.
    /// Nested lexical scopes may use a proven enclosing receiver. An incomplete
    /// proof must be propagated as unsupported rather than silently defaulted.
    pub fn value_scope_decision_with_steps(
        &mut self,
        element: ElementRef,
        receiver: Option<ScopeRef>,
        steps: &mut usize,
    ) -> ValueScopeDecision {
        ValueScopeResolver::default().select_builder(
            &mut self.b,
            element.0,
            receiver.map(|scope| scope.0),
            steps,
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::model::Model;

    fn resolved() -> ResolvedModel {
        let mut m = Model::new();
        let unit = m.add_source(
            "contexts.kerml",
            "package P {
                class Base { feature p = 1; feature v = p; }
                class Child specializes Base { feature redefines p = 2; class Nested; }
                class Other { feature p = 3; alias v for Base::v; }
                class Broken specializes Base, missing;
                class CycleA specializes Base, CycleB;
                class CycleB specializes CycleA;
                feature instanceFeature : Child;
                feature constantValue = 8;
            }",
        );
        assert!(unit.diagnostics.is_empty(), "{:?}", unit.diagnostics);
        ResolvedModel::build(&m)
    }

    #[test]
    fn own_inherited_typed_nested_and_unrelated_scopes_are_distinct() {
        let mut r = resolved();
        let value = r.resolve_qualified("P::Base::v").unwrap();
        let lexical = r.value_expr(value).unwrap().0;
        let mut proof = ValueScopeResolver::default();
        let mut steps = 0;
        for (name, selected) in [
            ("P::Base", Some("P::Base")),
            ("P::Child", Some("P::Child")),
            ("P::instanceFeature", Some("P::instanceFeature")),
            ("P::Child::Nested", Some("P::Child")),
            ("P::Other", None),
        ] {
            let element = r.resolve_qualified(name).unwrap();
            let scope = r.element_scope(element).unwrap();
            let expected = selected.map_or(ValueScopeDecision::Lexical(lexical), |name| {
                let owner = r.resolve_qualified(name).unwrap();
                ValueScopeDecision::Receiver(r.element_scope(owner).unwrap())
            });
            assert_eq!(
                proof.select_builder(&mut r.b, value.0, Some(scope.0), &mut steps),
                expected
            );
        }
        assert_eq!(
            proof.select_builder(&mut r.b, value.0, None, &mut steps),
            ValueScopeDecision::Lexical(lexical)
        );
    }

    #[test]
    fn package_values_and_imported_aliases_do_not_gain_unrelated_receivers() {
        let mut r = resolved();
        let base_value = r.resolve_qualified("P::Base::v").unwrap();
        let alias = r.resolve_qualified("P::Other::v").unwrap();
        assert_eq!(alias, base_value);
        let other = r.resolve_qualified("P::Other").unwrap();
        let other_scope = r.element_scope(other).unwrap();
        for value in [base_value, r.resolve_qualified("P::constantValue").unwrap()] {
            let lexical = r.value_expr(value).unwrap().0;
            assert_eq!(
                r.value_scope_decision_with_steps(value, Some(other_scope), &mut 0),
                ValueScopeDecision::Lexical(lexical)
            );
        }
    }

    #[test]
    fn missing_or_cyclic_contexts_never_become_lexical_fallback() {
        let mut r = resolved();
        let value = r.resolve_qualified("P::Base::v").unwrap();
        for name in ["P::Broken", "P::CycleA"] {
            let owner = r.resolve_qualified(name).unwrap();
            let scope = r.element_scope(owner).unwrap();
            assert_eq!(
                r.value_scope_decision_with_steps(value, Some(scope), &mut 0),
                ValueScopeDecision::Unsupported
            );
        }
        let owner = r.resolve_qualified("P::Child").unwrap();
        let scope = r.element_scope(owner).unwrap();
        let mut exhausted = crate::eval::MAX_STEPS;
        assert_eq!(
            r.value_scope_decision_with_steps(value, Some(scope), &mut exhausted),
            ValueScopeDecision::Unsupported
        );
        assert_eq!(
            r.value_scope_decision_with_steps(value, Some(scope), &mut 0),
            ValueScopeDecision::Receiver(scope)
        );
    }

    #[test]
    fn conjugation_admits_a_receiver_but_mixed_specialization_does_not() {
        let mut model = Model::new();
        let unit = model.add_source(
            "conjugated-context.kerml",
            "classifier Base { feature p = 1; feature v = p; }
             classifier Other { feature p = 9; }
             classifier Context conjugates Base { feature ownLiteral = 8; }
             classifier Donor specializes Other;",
        );
        assert!(unit.diagnostics.is_empty(), "{:?}", unit.diagnostics);
        let mut r = ResolvedModel::build(&model);
        let value = r.resolve_qualified("Base::v").unwrap();
        let base = r.resolve_qualified("Base").unwrap();
        let context = r.resolve_qualified("Context").unwrap();
        let own_literal = r.resolve_qualified("Context::ownLiteral").unwrap();
        let scope = r.element_scope(context).unwrap();
        for _ in 0..2 {
            assert_eq!(
                r.value_scope_decision_with_steps(value, Some(scope), &mut 0),
                ValueScopeDecision::Receiver(scope)
            );
        }

        // Form a graph forbidden by the specific-not-conjugated constraint.
        // Type::supertypes still selects only the conjugated Base, while the
        // legacy lookup can retain an ordinary specialization provider too.
        let donor = r.resolve_qualified("Donor").unwrap();
        let relationship = *r.b.elements[donor.0]
            .owned_relationships
            .iter()
            .find(|&&rel| conforms(r.b.elements[rel].ty, "Specialization"))
            .unwrap();
        r.b.elements[context.0]
            .owned_relationships
            .push(relationship);
        assert_eq!(
            r.b.value_context_bases(context.0, &mut 0),
            Some(vec![base.0])
        );
        for _ in 0..2 {
            // Each query gets a new proof cache after the graph mutation.
            assert_eq!(
                r.value_scope_decision_with_steps(value, Some(scope), &mut 0),
                ValueScopeDecision::Unsupported
            );
            assert_eq!(
                r.value_scope_decision_with_steps(own_literal, Some(scope), &mut 0),
                ValueScopeDecision::Receiver(scope)
            );
            assert_eq!(r.evaluate(own_literal), Ok(crate::eval::Value::Integer(8)));
        }
    }

    #[test]
    fn receiver_proof_uses_stored_identity_after_id_remapping() {
        let mut r = resolved();
        let value = r.resolve_qualified("P::Base::v").unwrap();
        let base = r.resolve_qualified("P::Base").unwrap();
        let child = r.resolve_qualified("P::Child").unwrap();
        let scope = r.element_scope(child).unwrap();
        assert_eq!(
            r.value_scope_decision_with_steps(value, Some(scope), &mut 0),
            ValueScopeDecision::Receiver(scope)
        );
        r.override_ids(&HashMap::from([(
            r.element_id(base),
            "99999999-9999-4999-8999-999999999999".parse().unwrap(),
        )]));
        // Never reuse an evaluation-local proof across this mutation.
        assert_eq!(
            r.value_scope_decision_with_steps(value, Some(scope), &mut 0),
            ValueScopeDecision::Receiver(scope)
        );
    }
}
