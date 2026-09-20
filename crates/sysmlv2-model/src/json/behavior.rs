//! Behavior and expression structure over the resolved model: the derived
//! properties of states, transitions, the control and communication
//! action kinds, expressions and functions, multiplicity ranges, filter
//! memberships and the membership-side identity strings. Each function
//! documents the specification rule it implements (KerML/SysML clause
//! 8.3, `spec-refs/derived-properties.json`); the dispatch is in
//! `derived.rs`.
//!
//! Parameters. `ActionUsage::inputParameter(i)` reads `inputParameters()`
//! `= input->select(f | f.owner = self)`, the owned parameters whose
//! direction is `in` or `inout`. A parameter's direction is constrained
//! to `ParameterMembership::parameterDirection()` — `in` by default,
//! `out` for a ReturnParameterMembership (KerML
//! `checkParameterMembershipDirection`) — so an owned member parameter
//! with no spelled direction takes that default here
//! ([`ResolvedModel::effective_direction`], which the `input`/`output`/
//! `directedFeature`/`parameter` families read too), as the pilot's
//! lowering of the action kinds relies on (a node's expression and body
//! parameters carry no direction on the wire). `argument(i)` is
//! `inputParameter(i)`'s `FeatureValue.value`. One lowering shape is
//! compensated for rather than read literally: an accept action's
//! trigger (`accept x at t`) is lowered as a TriggerInvocationExpression
//! that is itself a parameter member, where the pilot's grammar makes it
//! the payload parameter's value (API-GAPS issue 20) — it is not counted
//! as an input parameter, and an accept's `payloadArgument` falls back to
//! it.

use super::derived::{Reference, dangling_id};
use super::{ElementRef, ResolvedModel};
use crate::metaclass::conforms;

impl ResolvedModel {
    // ---- states and transitions ----

    /// `StateUsage::entryAction` / `doAction` / `exitAction` (and on
    /// StateDefinition): the owned member of the StateSubactionMembership
    /// with the given `kind`.
    pub(super) fn d_state_subaction(&mut self, e: ElementRef, kind: &str) -> Option<ElementRef> {
        let rels = self.owned_relationships_of_kind(e, "StateSubactionMembership");
        rels.into_iter()
            .find(|&r| self.prop_str(r.0, "kind") == Some(kind))
            .and_then(|r| self.d_owned_member_element(r))
    }

    /// `TransitionUsage::triggerAction` / `guardExpression` /
    /// `effectAction`: the transition features of the owned
    /// TransitionFeatureMemberships with the given `kind`, of the given
    /// metaclass (`AcceptActionUsage`, `Expression`, `ActionUsage`).
    pub(super) fn d_transition_features(
        &mut self,
        e: ElementRef,
        kind: &str,
        cast: &str,
    ) -> Vec<ElementRef> {
        let rels = self.owned_relationships_of_kind(e, "TransitionFeatureMembership");
        rels.into_iter()
            .filter(|&r| self.prop_str(r.0, "kind") == Some(kind))
            .filter_map(|r| self.d_owned_member_element(r))
            .filter(|&f| self.is_kind(f, cast))
            .collect()
    }

    /// `TransitionUsage::succession = ownedMember->selectByKind(Succession)->at(1)`.
    pub(super) fn d_succession(&mut self, e: ElementRef) -> Option<ElementRef> {
        self.d_owned_members(e)
            .into_iter()
            .find(|&m| self.is_kind(m, "Succession"))
    }

    /// `TransitionUsage::source = sourceFeature().featureTarget` as an
    /// ActionUsage, where `sourceFeature()` is the first Feature among the
    /// members of the non-feature memberships whose feature target is an
    /// ActionUsage — the `first S` membership, or the owning membership of
    /// a synthesized chain feature (`first a.b`).
    pub(super) fn d_transition_source(&mut self, e: ElementRef) -> Option<Reference> {
        self.ensure_by_id();
        let memberships: Vec<ElementRef> = self
            .d_owned_memberships(e)
            .into_iter()
            .filter(|&m| !self.is_kind(m, "FeatureMembership"))
            .collect();
        for m in memberships {
            let Some(member) = self.d_member_element(m) else {
                continue;
            };
            let target = match member {
                Reference::Element(f) if self.is_kind(f, "Feature") => self.d_feature_target(f),
                Reference::Element(_) => continue,
                outside => outside,
            };
            if let Some(t) = self.cast(target, "ActionUsage") {
                return Some(t);
            }
        }
        None
    }

    /// `TransitionUsage::target = succession.targetFeature->first().featureTarget`
    /// as an ActionUsage. The succession's target end is its second
    /// connector end: the grammar leaves the transition succession's
    /// source end unspelled (the source is the transition's own), so
    /// `targetFeature` — the related features past the first — reads the
    /// target end by position rather than through `relatedFeature`, which
    /// an unspelled end does not enter.
    pub(super) fn d_transition_target(&mut self, e: ElementRef) -> Option<Reference> {
        self.ensure_by_id();
        let succession = self.d_succession(e)?;
        let end = self
            .d_ends(self.d_owned_features(succession))
            .into_iter()
            .nth(1)?;
        let target = self.d_referenced_feature_target(end)?;
        self.cast(target, "ActionUsage")
    }

    // ---- parameters and arguments ----

    /// The feature's direction as the specification constrains it: the
    /// spelled `direction`, else the default of its owning
    /// ParameterMembership (`in`; `out` for a ReturnParameterMembership),
    /// else none. A TriggerInvocationExpression owned as a parameter
    /// member is an accept action's trigger value, not a parameter (see
    /// the module documentation), and has none.
    pub(super) fn effective_direction(&self, f: ElementRef) -> Option<&str> {
        if let Some(d) = self.prop_str(f.0, "direction") {
            return Some(d);
        }
        if self.b.elements[f.0].ty == "TriggerInvocationExpression" {
            return None;
        }
        let m = self.b.elements[f.0].owning_relationship?;
        let ty = self.b.elements[m].ty;
        if conforms(ty, "ReturnParameterMembership") {
            Some("out")
        } else if conforms(ty, "ParameterMembership") {
            Some("in")
        } else {
            None
        }
    }

    /// `inputParameters() = input->select(f | f.owner = self)`: the owned
    /// features whose effective direction is `in` or `inout`, in feature
    /// order.
    pub(super) fn d_input_parameters(&self, e: ElementRef) -> Vec<ElementRef> {
        self.d_owned_features(e)
            .into_iter()
            .filter(|&f| matches!(self.effective_direction(f), Some("in" | "inout")))
            .collect()
    }

    /// `inputParameter(i)` (1-based).
    pub(super) fn d_input_parameter(&self, e: ElementRef, i: usize) -> Option<ElementRef> {
        self.d_input_parameters(e)
            .into_iter()
            .nth(i.checked_sub(1)?)
    }

    /// `argument(i)`: the value expression of `inputParameter(i)`'s
    /// FeatureValue.
    pub(super) fn d_argument(&self, e: ElementRef, i: usize) -> Option<ElementRef> {
        let p = self.d_input_parameter(e, i)?;
        self.d_argument_of(p)
    }

    /// The argument an input parameter carries: its FeatureValue's value
    /// — or, for a trigger invocation's argument, which this lowering owns
    /// as the parameter itself without the Feature-and-FeatureValue
    /// wrapper (API-GAPS issue 20), the expression that is the parameter.
    fn d_argument_of(&self, p: ElementRef) -> Option<ElementRef> {
        self.d_feature_value_of(p).or_else(|| {
            let owner = self.b.elements[p.0]
                .owning_relationship
                .and_then(|m| self.d_owning_related_element_ro(m))?;
            (self.is_kind(p, "Expression")
                && self.b.elements[owner].ty == "TriggerInvocationExpression")
                .then_some(p)
        })
    }

    /// The owner of a relationship, read without building the owner map:
    /// the element whose owned relationships list it.
    fn d_owning_related_element_ro(&self, rel: usize) -> Option<usize> {
        self.b.elements[rel]
            .props
            .get("owningRelatedElement")
            .and_then(|v| v.as_reference())
            .and_then(|id| self.by_id.get(&id).copied())
    }

    /// `AcceptActionUsage::payloadArgument = argument(1)`: the payload
    /// parameter's value, else the trigger this lowering owns beside the
    /// payload (the pilot's grammar makes the trigger the payload's value;
    /// API-GAPS issue 20).
    pub(super) fn d_accept_payload_argument(&self, e: ElementRef) -> Option<ElementRef> {
        self.d_argument(e, 1).or_else(|| {
            self.d_owned_features(e)
                .into_iter()
                .find(|&f| self.b.elements[f.0].ty == "TriggerInvocationExpression")
        })
    }

    /// The value expression of the feature's owned FeatureValue.
    fn d_feature_value_of(&self, f: ElementRef) -> Option<ElementRef> {
        self.owned_relationships_of_kind(f, "FeatureValue")
            .into_iter()
            .next()
            .and_then(|fv| self.d_owned_member_element(fv))
    }

    /// `inputParameter(i)` cast to `kind`. An expression-valued parameter
    /// (`ifArgument`, `whileArgument`, `untilArgument`) is, in the
    /// grammar's lowering, a reference feature whose FeatureValue owns the
    /// expression rather than the expression itself; the rule's
    /// `oclAsType(Expression)` is read through that value.
    pub(super) fn d_parameter_as(&self, e: ElementRef, i: usize, kind: &str) -> Option<ElementRef> {
        let p = self.d_input_parameter(e, i)?;
        if self.is_kind(p, kind) {
            return Some(p);
        }
        if kind == "Expression" {
            return self
                .d_feature_value_of(p)
                .filter(|&v| self.is_kind(v, kind));
        }
        None
    }

    /// `ForLoopActionUsage::loopVariable = ownedFeature->first()` as a
    /// ReferenceUsage.
    pub(super) fn d_loop_variable(&self, e: ElementRef) -> Option<ElementRef> {
        self.d_owned_features(e)
            .into_iter()
            .next()
            .filter(|&f| self.is_kind(f, "ReferenceUsage"))
    }

    // ---- references through subsetting ----

    /// `referencedFeatureTarget() = ownedReferenceSubsetting.referencedFeature.featureTarget`.
    pub(super) fn d_referenced_feature_target(&mut self, e: ElementRef) -> Option<Reference> {
        self.ensure_by_id();
        let sub = self
            .owned_relationships_of_kind(e, "ReferenceSubsetting")
            .into_iter()
            .next()?;
        let atom = self.b.elements[sub.0]
            .props
            .get("referencedFeature")?
            .clone();
        Some(match self.reference_of(&atom)? {
            Reference::Element(f) => self.d_feature_target(f),
            outside => outside,
        })
    }

    /// `EventOccurrenceUsage::eventOccurrence` and its narrowings
    /// (`performedAction`, `exhibitedState`, `useCaseIncluded`,
    /// `assertedConstraint`, `satisfiedRequirement`): `referencedFeatureTarget()`
    /// cast to `kind`, or the element itself when it references nothing.
    pub(super) fn d_referenced_or_self(&mut self, e: ElementRef, kind: &str) -> Option<Reference> {
        match self.d_referenced_feature_target(e) {
            Some(target) => self.cast(target, kind),
            None => Some(Reference::Element(e)),
        }
    }

    /// `UseCaseUsage::includedUseCase = ownedUseCase->selectByKind(IncludeUseCaseUsage).useCaseIncluded`.
    pub(super) fn d_included_use_cases(&mut self, e: ElementRef) -> Vec<Reference> {
        let includes: Vec<ElementRef> = self
            .d_owned_features(e)
            .into_iter()
            .filter(|&f| self.is_kind(f, "IncludeUseCaseUsage"))
            .collect();
        includes
            .into_iter()
            .filter_map(|i| self.d_referenced_or_self(i, "UseCaseUsage"))
            .collect()
    }

    // ---- expressions and functions ----

    /// `Expression::result` / `Function::result`: the owned member
    /// parameter of the first ReturnParameterMembership (the inherited
    /// result waits for the closure policy).
    pub(super) fn d_result(&mut self, e: ElementRef) -> Option<ElementRef> {
        self.d_feature_memberships(e)
            .into_iter()
            .find(|&m| self.is_kind(m, "ReturnParameterMembership"))
            .and_then(|m| self.d_owned_member_element(m))
    }

    /// The types of `e` of the given kind: `Expression::function`,
    /// `BooleanExpression::predicate`, `Connector::association`,
    /// `Flow::interaction`, `MetadataFeature::metaclass` — each
    /// `type->selectByKind(Kind)`.
    pub(super) fn d_types_of_kind(&mut self, e: ElementRef, kind: &str) -> Vec<Reference> {
        let types = self.d_types(e);
        types
            .into_iter()
            .filter_map(|t| self.cast(t, kind))
            .collect()
    }

    /// `InstantiationExpression::instantiatedType`: for an
    /// OperatorExpression, `resolveGlobal` of the operator's function in
    /// `BaseFunctions`, `DataFunctions` or `ControlFunctions` — an element
    /// when the library is loaded, an external id through a library name
    /// table, else null; for an invocation or constructor, the member of
    /// the expression's first non-feature membership (the `fn`/`type`
    /// member the lowering writes), a Type.
    pub(super) fn d_instantiated_type(&mut self, e: ElementRef) -> Option<Reference> {
        self.ensure_by_id();
        if self.is_kind(e, "OperatorExpression") {
            let operator = self.prop_str(e.0, "operator")?.to_string();
            let candidates: Vec<(String, String)> =
                ["BaseFunctions", "DataFunctions", "ControlFunctions"]
                    .iter()
                    .map(|ns| (format!("{ns}::'{operator}'"), format!("{ns}::{operator}")))
                    .collect();
            return self.library_element_named(&candidates);
        }
        if self.b.elements[e.0].ty == "TriggerInvocationExpression" {
            // SysML `TriggerInvocationExpression::instantiatedType()`:
            // `resolveGlobal('Triggers::TriggerWhen' | 'TriggerAt' | 'TriggerAfter')` by kind.
            let name = match self.prop_str(e.0, "kind") {
                Some("when") => "TriggerWhen",
                Some("at") => "TriggerAt",
                _ => "TriggerAfter",
            };
            let qn = format!("Triggers::{name}");
            return self.library_element_named(&[(qn.clone(), qn)]);
        }
        let memberships: Vec<ElementRef> = self
            .d_owned_memberships(e)
            .into_iter()
            .filter(|&m| !self.is_kind(m, "FeatureMembership"))
            .collect();
        let members: Vec<Reference> = memberships
            .into_iter()
            .filter_map(|m| self.d_member_element(m))
            .collect();
        members.into_iter().find_map(|t| self.cast(t, "Type"))
    }

    /// A library element by qualified name — `(quoted spelling, raw
    /// spelling)` candidates in order: an element of a loaded library, or
    /// an external id through the library name table
    /// ([`Self::set_library_names`]); a user element of the same name is
    /// not it (`resolveGlobal` names the library).
    pub(super) fn library_element_named(
        &mut self,
        candidates: &[(String, String)],
    ) -> Option<Reference> {
        for (quoted, raw) in candidates {
            if let Some(f) = self
                .resolve_qualified(quoted)
                .filter(|&f| self.is_library_element(f))
            {
                return Some(Reference::Element(f));
            }
            if let Some(&id) = self.external_by_name.get(raw) {
                return Some(Reference::External(id));
            }
        }
        None
    }

    /// `InvocationExpression::argument` / `ConstructorExpression::argument`:
    /// for each input parameter of the instantiated type (each feature,
    /// for a constructor) in order, the value of the owned parameter that
    /// redefines it — explicitly, or positionally (the lowering's implied
    /// parameter redefinition). When the instantiated type is outside the
    /// model, or its parameters are not visible at the passthrough level
    /// (inherited), the owned parameters' values in order — the positional
    /// reading.
    pub(super) fn d_arguments(&mut self, e: ElementRef) -> Vec<Reference> {
        self.ensure_by_id();
        let params = self.d_input_parameters(e);
        let callee = self.d_instantiated_type(e);
        let targets: Vec<ElementRef> = match callee {
            Some(Reference::Element(callee)) if self.is_kind(e, "ConstructorExpression") => {
                self.d_features(callee)
            }
            Some(Reference::Element(callee)) => {
                // The callee's inputs — its inherited ones too under the
                // closure policy.
                let features = self.d_features(callee);
                self.d_directed(features, Some(true))
            }
            _ => Vec::new(),
        };
        if targets.is_empty() {
            return params
                .into_iter()
                .filter_map(|p| self.d_argument_of(p))
                .map(Reference::Element)
                .collect();
        }
        let inputs = targets;
        // Explicit redefinition targets per owned parameter; the
        // positional ones take the inputs left in order.
        let redefined: Vec<Option<usize>> = params
            .iter()
            .map(|&p| {
                self.owned_relationships_of_kind(p, "Redefinition")
                    .into_iter()
                    .find_map(|r| self.prop_target(r.0, "redefinedFeature"))
            })
            .collect();
        let mut positional = params
            .iter()
            .zip(&redefined)
            .filter(|(_, r)| r.is_none())
            .map(|(&p, _)| p);
        let mut out = Vec::new();
        for inp in inputs {
            let explicit = params
                .iter()
                .zip(&redefined)
                .find(|(_, r)| **r == Some(inp.0))
                .map(|(&p, _)| p);
            let p = match explicit.or_else(|| positional.next()) {
                Some(p) => p,
                None => break,
            };
            if let Some(v) = self.d_argument_of(p) {
                out.push(Reference::Element(v));
            }
        }
        out
    }

    /// `FeatureReferenceExpression::referent`: the member of the first
    /// non-parameter membership, a Feature.
    pub(super) fn d_referent(&mut self, e: ElementRef) -> Option<Reference> {
        self.ensure_by_id();
        let m = self
            .d_owned_memberships(e)
            .into_iter()
            .find(|&m| !self.is_kind(m, "ParameterMembership"))?;
        let member = self.d_member_element(m)?;
        self.cast(member, "Feature")
    }

    /// `AssignmentActionUsage::referent` and
    /// `MetadataAccessExpression::referencedElement`: the first member of
    /// the non-feature memberships (a Feature for the assignment).
    pub(super) fn d_unowned_member(&mut self, e: ElementRef, kind: &str) -> Option<Reference> {
        self.ensure_by_id();
        let memberships: Vec<ElementRef> = self
            .d_owned_memberships(e)
            .into_iter()
            .filter(|&m| !self.is_kind(m, "FeatureMembership"))
            .collect();
        let members: Vec<Reference> = memberships
            .into_iter()
            .filter_map(|m| self.d_member_element(m))
            .collect();
        members.into_iter().find_map(|t| self.cast(t, kind))
    }

    /// `Function::expression = step->selectByKind(Expression)`, over the
    /// (passthrough) steps.
    pub(super) fn d_function_expressions(&mut self, e: ElementRef) -> Vec<ElementRef> {
        self.d_features(e)
            .into_iter()
            .filter(|&f| self.is_kind(f, "Expression"))
            .collect()
    }

    // ---- multiplicity and filters ----

    /// `MultiplicityRange::bound`: the owned member Expressions, in order
    /// (one: the upper bound; two: lower then upper).
    pub(super) fn d_bounds(&self, e: ElementRef) -> Vec<ElementRef> {
        self.d_owned_members(e)
            .into_iter()
            .filter(|&m| self.is_kind(m, "Expression"))
            .collect()
    }

    /// `Package::filterCondition` / `ViewUsage::viewCondition`:
    /// `ownedMembership->selectByKind(ElementFilterMembership).condition`.
    pub(super) fn d_filter_conditions(&self, e: ElementRef) -> Vec<ElementRef> {
        self.owned_relationships_of_kind(e, "ElementFilterMembership")
            .into_iter()
            .filter_map(|m| self.d_owned_member_element(m))
            .collect()
    }

    // ---- memberships ----

    /// `Membership::memberElementId = memberElement.elementId` (and the
    /// OwningMembership redefinition): the id as the interchange spells
    /// it — an unresolved spelling by its deterministic dangling id.
    pub(super) fn d_member_element_id(&mut self, m: ElementRef) -> Option<String> {
        Some(match self.d_member_element(m)? {
            Reference::Element(e) => self.element_id(e).to_string(),
            Reference::External(id) => id.to_string(),
            Reference::Unresolved(spelling) => dangling_id(&spelling),
        })
    }

    /// `OwningMembership::ownedMemberName = ownedMemberElement.name` and
    /// `ownedMemberShortName = ownedMemberElement.shortName`.
    pub(super) fn d_owned_member_name(&mut self, m: ElementRef, short: bool) -> Option<String> {
        let member = self.d_owned_member_element(m)?;
        if short {
            self.element_short_name(member)
        } else {
            self.element_effective_name(member)
        }
    }

    // ---- typing residue ----

    /// `OccurrenceUsage::individualDefinition`: the first occurrence
    /// definition with `isIndividual` — a property test, which a target
    /// outside the model cannot pass.
    pub(super) fn d_individual_definition(&mut self, e: ElementRef) -> Option<Reference> {
        let types = self.d_types(e);
        types
            .into_iter()
            .filter_map(|t| t.element())
            .find(|&t| {
                self.is_kind(t, "OccurrenceDefinition") && self.prop_bool(t.0, "isIndividual")
            })
            .map(Reference::Element)
    }

    /// `Flow::payloadFeature = ownedFeature->selectByKind(PayloadFeature)->first()`.
    pub(super) fn d_payload_feature(&self, e: ElementRef) -> Option<ElementRef> {
        self.d_owned_features(e)
            .into_iter()
            .find(|&f| self.is_kind(f, "PayloadFeature"))
    }

    /// `Flow::payloadType = payloadFeature.type`.
    pub(super) fn d_payload_type(&mut self, e: ElementRef) -> Vec<Reference> {
        match self.d_payload_feature(e) {
            Some(p) => self.d_types(p),
            None => Vec::new(),
        }
    }

    /// `PortDefinition::conjugatedPortDefinition`: the owned member that
    /// is a ConjugatedPortDefinition; `PortConjugation::conjugatedPortDefinition`:
    /// the owning type.
    pub(super) fn d_conjugated_port_definition(&mut self, e: ElementRef) -> Option<ElementRef> {
        if self.is_kind(e, "PortConjugation") {
            return self
                .d_owning_type_any(e)
                .filter(|&o| self.is_kind(o, "ConjugatedPortDefinition"));
        }
        self.d_owned_members(e)
            .into_iter()
            .find(|&m| self.is_kind(m, "ConjugatedPortDefinition"))
    }

    // ---- helpers ----

    /// A kind test on a reference: an element of the model passes when
    /// its metaclass conforms; a target outside the model is reported as
    /// it is — the model cannot classify it, and a reference the model
    /// holds is not dropped for that (a well-formed model's typing
    /// constraints make the test hold wherever the reference resolved).
    pub(super) fn cast(&self, r: Reference, kind: &str) -> Option<Reference> {
        match r {
            Reference::Element(e) => self.is_kind(e, kind).then_some(Reference::Element(e)),
            outside => Some(outside),
        }
    }

    pub(super) fn prop_str(&self, e: usize, key: &str) -> Option<&str> {
        self.b.elements[e].props.get(key).and_then(|v| v.as_str())
    }

    pub(super) fn prop_bool(&self, e: usize, key: &str) -> bool {
        self.b.elements[e]
            .props
            .get(key)
            .and_then(|v| v.as_bool())
            .unwrap_or(false)
    }
}
