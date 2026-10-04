//! Receiver-qualified admission of generalized runtime parameter references.
use super::{
    Builder, ElementRef, ResolvedModel, ScopeRef, provider_completeness::ProviderCompleteness,
};
use std::collections::{HashMap, HashSet};

/// The runtime input declaration selected within one active calculation frame.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RuntimeParameterSelection {
    /// A unique input of the active calculation matches or redefines the referent.
    Selected(ElementRef),
    /// The reference has no contextual parameter in this frame.
    NotApplicable,
    /// Incomplete, cyclic or ambiguous relationships prevent safe selection.
    Unsupported,
}

pub(super) fn descendant(
    b: &Builder,
    mut scope: usize,
    ancestor: usize,
    steps: &mut usize,
) -> Option<bool> {
    b.scopes.get(ancestor)?;
    for _ in 0..=super::MAX_RESOLUTION_DEPTH {
        charge(steps, 1)?;
        let context = b.scopes.get(scope)?;
        if scope == ancestor {
            return Some(true);
        }
        match context.parent {
            Some(parent) => scope = parent,
            None => return Some(false),
        }
    }
    None
}

fn charge(steps: &mut usize, amount: usize) -> Option<()> {
    *steps = steps.saturating_add(amount);
    (*steps <= crate::eval::MAX_STEPS).then_some(())
}

/// Recorded explicit edges only: resolving a missing endpoint here could use
/// the currently executing expression's source instead of its declaration.
pub(super) fn explicit_ancestor(
    b: &mut Builder,
    callee: usize,
    ancestor: usize,
    steps: &mut usize,
) -> Option<bool> {
    b.ensure_spec_index();
    let mut stack = vec![(callee, 0)];
    let mut seen = HashSet::new();
    let mut found = false;
    while let Some((element, depth)) = stack.pop() {
        charge(steps, 1)?;
        if depth > super::MAX_RESOLUTION_DEPTH {
            return None;
        }
        b.elements.get(element)?;
        if !seen.insert(element) {
            continue;
        }
        found |= element == ancestor;
        for &index in b.spec_index.as_ref()?.get(&element).into_iter().flatten() {
            charge(steps, 1)?;
            let target = b.spec_resolved.get(index).copied().flatten()?;
            stack.push((target, depth + 1));
        }
    }
    Some(found)
}

struct Redefinitions {
    target: usize,
    known: HashMap<(usize, usize), bool>,
    active: HashSet<usize>,
}

impl Redefinitions {
    fn reaches(
        &mut self,
        b: &mut Builder,
        element: usize,
        depth: usize,
        steps: &mut usize,
    ) -> Option<bool> {
        charge(steps, 1)?;
        if depth > super::MAX_RESOLUTION_DEPTH || element >= b.elements.len() {
            return None;
        }
        if let Some(&reaches) = self.known.get(&(element, depth)) {
            return Some(reaches);
        }
        if !self.active.insert(element) {
            return None;
        }
        let result = (|| {
            if !crate::metaclass::conforms(b.elements[element].ty, "Feature") {
                return None;
            }
            let targets = b.cardinality_redefinition_targets(element, steps)?;
            charge(steps, targets.len())?;
            let mut reaches = element == self.target;
            // Complete the whole closure even after finding the target: a
            // second edge may be missing or cyclic rather than another alias.
            for target in targets {
                reaches |= self.reaches(b, target, depth + 1, steps)?;
            }
            Some(reaches)
        })();
        self.active.remove(&element);
        if let Some(reaches) = result {
            self.known.insert((element, depth), reaches);
        }
        result
    }
}

impl Builder {
    pub(crate) fn runtime_parameter_visible_with_steps(
        &self,
        parameter: usize,
        lexical_scope: usize,
        steps: &mut usize,
    ) -> Option<bool> {
        charge(steps, 1)?;
        if parameter >= self.elements.len() || lexical_scope >= self.scopes.len() {
            return None;
        }
        let declaration = self.owner_scope_of(parameter)?;
        descendant(self, lexical_scope, declaration, steps)
    }

    pub(crate) fn runtime_parameter_selection(
        &mut self,
        callee: usize,
        lexical_scope: usize,
        receiver_scope: usize,
        target: usize,
    ) -> RuntimeParameterSelection {
        self.runtime_parameter_selection_with_steps(
            callee,
            lexical_scope,
            receiver_scope,
            target,
            &mut 0,
        )
    }

    pub(crate) fn runtime_parameter_selection_with_steps(
        &mut self,
        callee: usize,
        lexical_scope: usize,
        receiver_scope: usize,
        target: usize,
        steps: &mut usize,
    ) -> RuntimeParameterSelection {
        use RuntimeParameterSelection::{NotApplicable, Selected, Unsupported};
        if charge(steps, 1).is_none() {
            return Unsupported;
        }
        let Some(&callee_scope) = self.elem_scope.get(&callee) else {
            return Unsupported;
        };
        match descendant(self, receiver_scope, callee_scope, steps) {
            Some(true) => {}
            Some(false) => return NotApplicable,
            None => return Unsupported,
        }
        let Some(lexically_inside) = descendant(self, lexical_scope, callee_scope, steps) else {
            return Unsupported;
        };
        if !ProviderCompleteness::default().scope(self, callee_scope, steps) {
            return Unsupported;
        }
        if !lexically_inside {
            let Some(owner) = self.nearest_scope_owner(lexical_scope) else {
                return NotApplicable;
            };
            match explicit_ancestor(self, callee, owner, steps) {
                Some(true) => {}
                Some(false) => return NotApplicable,
                None => return Unsupported,
            }
        }
        let Some(parameters) = self.calc_parameter_bindings(callee) else {
            return Unsupported;
        };
        let mut closure = Redefinitions {
            target,
            known: HashMap::new(),
            active: HashSet::new(),
        };
        let mut selected = None;
        for parameter in parameters {
            match closure.reaches(self, parameter.element.0, 0, steps) {
                Some(true) => {
                    if selected.replace(parameter.element).is_some() {
                        return Unsupported;
                    }
                }
                Some(false) => {}
                None => return Unsupported,
            }
        }
        selected.map_or(NotApplicable, Selected)
    }
}

impl ResolvedModel {
    /// Whether an exact runtime parameter binding is lexically visible from
    /// this expression's declaration scope. A matching element identity alone
    /// does not allow an unrelated calculation to capture its caller's input.
    /// `None` means the scope is unavailable or the shared proof budget is
    /// exhausted; it must not be treated as permission to use the binding.
    pub fn runtime_parameter_visible_with_steps(
        &self,
        parameter: ElementRef,
        lexical_scope: ScopeRef,
        steps: &mut usize,
    ) -> Option<bool> {
        self.b
            .runtime_parameter_visible_with_steps(parameter.0, lexical_scope.0, steps)
    }

    /// Select a generalized input reference within one active calculation
    /// frame, after checking runtime bindings for the exact reference identity.
    /// Receiver scope must be inside the callee; lexical scope must be inside
    /// it or owned by a proven explicit ancestor. Only a unique, complete
    /// Redefinition closure admits a parameter. An unsupported result must not
    /// fall through to a declaration default, and a selected input must still
    /// have a value in that same frame.
    pub fn runtime_parameter_selection(
        &mut self,
        callee: ElementRef,
        lexical_scope: ScopeRef,
        receiver_scope: ScopeRef,
        target: ElementRef,
    ) -> RuntimeParameterSelection {
        self.b
            .runtime_parameter_selection(callee.0, lexical_scope.0, receiver_scope.0, target.0)
    }

    /// As [`Self::runtime_parameter_selection`], charging proof work against
    /// an evaluation-wide step count. Repeated frame queries share the same
    /// budget rather than each receiving a fresh allowance. Exhaustion returns
    /// [`RuntimeParameterSelection::Unsupported`].
    pub fn runtime_parameter_selection_with_steps(
        &mut self,
        callee: ElementRef,
        lexical_scope: ScopeRef,
        receiver_scope: ScopeRef,
        target: ElementRef,
        steps: &mut usize,
    ) -> RuntimeParameterSelection {
        self.b.runtime_parameter_selection_with_steps(
            callee.0,
            lexical_scope.0,
            receiver_scope.0,
            target.0,
            steps,
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::model::Model;

    fn resolved(source: &str) -> ResolvedModel {
        let mut model = Model::new();
        model.add_source("parameter-context.sysml", source);
        assert!(!model.has_errors());
        ResolvedModel::build(&model)
    }

    #[test]
    fn generalized_input_requires_matching_receiver_and_lexical_context() {
        let mut model = resolved(
            "calc def Base { in p default 1; attribute v = p; }
             calc def Child :> Base { in q :>> Base::p; calc def Nested { q } }
             calc def Other { Base::p }
             package Constants { attribute global = Base::p; }",
        );
        let child = model.resolve_qualified("Child").unwrap();
        let base = model.resolve_qualified("Base").unwrap();
        let q = model.resolve_qualified("Child::q").unwrap();
        let p = model.resolve_qualified("Base::p").unwrap();
        let child_scope = model.element_scope(child).unwrap();
        let base_scope = model.element_scope(base).unwrap();
        for name in ["Child", "Child::Nested", "Base"] {
            let owner = model.resolve_qualified(name).unwrap();
            let lexical = model.element_scope(owner).unwrap();
            assert_eq!(
                model.runtime_parameter_selection(child, lexical, child_scope, p),
                RuntimeParameterSelection::Selected(q),
                "{name}",
            );
        }
        for name in ["Other", "Constants"] {
            let owner = model.resolve_qualified(name).unwrap();
            let lexical = model.element_scope(owner).unwrap();
            assert_eq!(
                model.runtime_parameter_selection(child, lexical, child_scope, p),
                RuntimeParameterSelection::NotApplicable,
                "{name}",
            );
        }
        assert_eq!(
            model.runtime_parameter_selection(child, base_scope, base_scope, p),
            RuntimeParameterSelection::NotApplicable,
        );
    }

    #[test]
    fn competing_inputs_and_incomplete_closures_are_unsupported() {
        let mut model = resolved(
            "calc def Base { in p; }
             calc def Child :> Base { in q :>> Base::p; }
             calc def Ambiguous :> Base { in q :>> Base::p; in r :>> Base::p; }",
        );
        let child = model.resolve_qualified("Child").unwrap();
        let ambiguous = model.resolve_qualified("Ambiguous").unwrap();
        let p = model.resolve_qualified("Base::p").unwrap();
        let q = model.resolve_qualified("Child::q").unwrap();
        let child_scope = model.element_scope(child).unwrap();
        let ambiguous_scope = model.element_scope(ambiguous).unwrap();
        assert_eq!(
            model.runtime_parameter_selection(ambiguous, ambiguous_scope, ambiguous_scope, p),
            RuntimeParameterSelection::Unsupported,
        );
        model.b.ensure_spec_index();
        let index = model.b.spec_index.as_ref().unwrap().get(&q.0).unwrap()[0];
        let saved = model.b.spec_resolved[index];
        model.b.spec_resolved[index] = None;
        assert_eq!(
            model.runtime_parameter_selection(child, child_scope, child_scope, p),
            RuntimeParameterSelection::Unsupported,
        );
        model.b.spec_resolved[index] = Some(q.0);
        assert_eq!(
            model.runtime_parameter_selection(child, child_scope, child_scope, p),
            RuntimeParameterSelection::Unsupported,
        );
        model.b.spec_resolved[index] = saved;
        assert_eq!(
            model.runtime_parameter_selection(child, child_scope, child_scope, p),
            RuntimeParameterSelection::Selected(q),
        );
    }

    #[test]
    fn repeated_selections_charge_shared_budget_and_recover_in_a_new_query() {
        let mut model = resolved(
            "calc def Base { in p; }
             calc def Child :> Base { in q :>> Base::p; }",
        );
        let child = model.resolve_qualified("Child").unwrap();
        let p = model.resolve_qualified("Base::p").unwrap();
        let q = model.resolve_qualified("Child::q").unwrap();
        let scope = model.element_scope(child).unwrap();
        let mut steps = 0;
        for _ in 0..2 {
            let before = steps;
            assert_eq!(
                model.runtime_parameter_selection_with_steps(child, scope, scope, p, &mut steps),
                RuntimeParameterSelection::Selected(q),
            );
            assert!(steps > before);
        }
        steps = crate::eval::MAX_STEPS;
        assert_eq!(
            model.runtime_parameter_selection_with_steps(child, scope, scope, p, &mut steps),
            RuntimeParameterSelection::Unsupported,
        );
        assert!(steps > crate::eval::MAX_STEPS);
        assert_eq!(
            model.runtime_parameter_selection(child, scope, scope, p),
            RuntimeParameterSelection::Selected(q),
        );
    }

    #[test]
    fn exact_bindings_require_lexical_containment_including_lambda_scopes() {
        let mut model = resolved(
            "calc def Base { in p; calc def Nested { Base::p }
                 attribute values = (1,2)->collect { in lambdaInput; lambdaInput }; }
             calc def Other { Base::p }
             package Constants { attribute bridge = Base::p; }",
        );
        let p = model.resolve_qualified("Base::p").unwrap();
        let mut steps = 0;
        for (name, expected) in [
            ("Base", true),
            ("Base::Nested", true),
            ("Other", false),
            ("Constants", false),
        ] {
            let owner = model.resolve_qualified(name).unwrap();
            let lexical = model.element_scope(owner).unwrap();
            assert_eq!(
                model.runtime_parameter_visible_with_steps(p, lexical, &mut steps),
                Some(expected),
                "{name}"
            );
        }
        let lambda_parameter = model
            .b
            .elements
            .iter()
            .position(|element| {
                element
                    .props
                    .get("declaredName")
                    .and_then(|value| value.as_str())
                    == Some("lambdaInput")
            })
            .unwrap();
        let lambda_scope = ScopeRef(model.b.owner_scope_of(lambda_parameter).unwrap());
        assert_eq!(
            model.runtime_parameter_visible_with_steps(p, lambda_scope, &mut steps),
            Some(true)
        );
        assert_eq!(
            model.runtime_parameter_visible_with_steps(
                ElementRef(lambda_parameter),
                lambda_scope,
                &mut steps
            ),
            Some(true)
        );
        let base_scope = model.b.owner_scope_of(p.0).unwrap();
        assert_eq!(
            model.runtime_parameter_visible_with_steps(
                ElementRef(lambda_parameter),
                ScopeRef(base_scope),
                &mut steps
            ),
            Some(false)
        );
        steps = crate::eval::MAX_STEPS;
        assert_eq!(
            model.runtime_parameter_visible_with_steps(p, lambda_scope, &mut steps),
            None
        );
        steps = 0;
        assert_eq!(
            model.runtime_parameter_visible_with_steps(p, lambda_scope, &mut steps),
            Some(true)
        );
        assert_eq!(
            model.runtime_parameter_visible_with_steps(
                ElementRef(usize::MAX),
                lambda_scope,
                &mut steps
            ),
            None
        );
    }
}
