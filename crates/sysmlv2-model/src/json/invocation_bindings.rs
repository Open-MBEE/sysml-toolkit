//! Checked direct argument bindings over authored or current admitted positional evidence.
use super::{
    ElementRef, ResolvedModel, TypeInputIssue, membership_evidence,
    semantic::certified_types::Stamp, semantic_ownership, structural_index::StoredStructure,
    type_relations,
};
use crate::metaclass::conforms;
use crate::metaclass::is_a;
use std::collections::{HashMap, HashSet};

/// A supplied argument and the exact input it directly redefines.
#[derive(Clone, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub struct InvocationBinding {
    pub input: ElementRef,
    pub parameter: ElementRef,
    pub value: ElementRef,
}
/// Complete supplied arguments in callee input order. Omitted inputs remain in
/// `inputs` but do not produce a binding. This is not an arity/default/evaluability
/// certificate or a promise that all Invocation constraints are satisfied.
#[derive(Clone, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub struct InvocationBindings {
    pub callee: ElementRef,
    pub inputs: Vec<ElementRef>,
    pub bindings: Vec<InvocationBinding>,
}
/// A failed proof never denotes an empty argument list.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub enum InvocationBindingIssue {
    InvalidElement,
    InvalidRelationship,
    IncompleteInputs(TypeInputIssue),
    IncompleteProvider,
    UnsupportedConfiguration,
    UnmappedArgument,
    DuplicateArgument,
    StaleEvidence,
    WorkLimit,
}
#[derive(Clone, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub struct InvocationBindingReport {
    pub arguments: Result<InvocationBindings, InvocationBindingIssue>,
    pub steps: usize,
}
use InvocationBindingIssue::*;
fn charge(steps: &mut usize, n: usize) -> Result<(), InvocationBindingIssue> {
    *steps = steps.saturating_add(n);
    if *steps > crate::eval::MAX_STEPS {
        Err(WorkLimit)
    } else {
        Ok(())
    }
}
impl ResolvedModel {
    /// Certify supplied arguments of ordinary InvocationExpressions and admitted
    /// canonical numeric OperatorExpressions calling exact loaded library Functions.
    /// Each argument must have one checked owned direct Redefinition.
    /// Named authored mappings are supported without truncating after an omitted
    /// earlier input. Positional mappings additionally require the current shared
    /// published dynamic plan and agreement with complete input order. Missing
    /// plans and defaults remain qualified; constructors have a separate report.
    /// This query publishes no rows.
    pub fn invocation_binding_report(&mut self, receiver: ElementRef) -> InvocationBindingReport {
        self.invocation_binding_report_with_budget(receiver, 0)
    }
    pub(in crate::json) fn invocation_binding_report_with_budget(
        &mut self,
        receiver: ElementRef,
        initial: usize,
    ) -> InvocationBindingReport {
        let mut steps = initial;
        let arguments = self
            .b
            .checked_invocation_bindings(receiver.0, &mut steps, None);
        InvocationBindingReport {
            arguments: if steps > crate::eval::MAX_STEPS {
                Err(WorkLimit)
            } else {
                arguments
            },
            steps,
        }
    }
}
impl super::Builder {
    pub(super) fn checked_invocation_bindings(
        &mut self,
        receiver: usize,
        steps: &mut usize,
        proposed: Option<&mut HashMap<usize, Vec<usize>>>,
    ) -> Result<InvocationBindings, InvocationBindingIssue> {
        self.checked_invocation_bindings_in_batch(
            receiver,
            steps,
            proposed,
            &mut super::constructor_bindings::ConstructorBatchEvidence::default(),
        )
    }
    pub(super) fn checked_invocation_bindings_in_batch(
        &mut self,
        receiver: usize,
        steps: &mut usize,
        mut proposed: Option<&mut HashMap<usize, Vec<usize>>>,
        batch: &mut super::constructor_bindings::ConstructorBatchEvidence,
    ) -> Result<InvocationBindings, InvocationBindingIssue> {
        charge(steps, 1)?;
        // A feature chain expression is the `'.'` operator's: its one
        // source parameter binds through the same static callee row.
        let kind = self.elements.get(receiver).ok_or(InvalidElement)?.ty;
        let operator = matches!(kind, "OperatorExpression" | "FeatureChainExpression");
        if (!operator && self.elements[receiver].ty != "InvocationExpression")
            || self.positional_planning
        {
            return Err(UnsupportedConfiguration);
        }
        let raw = StoredStructure::for_query(self, steps).ok_or(IncompleteProvider)?;
        let callee = if operator {
            // The operator's function is the static plan's typing row (the
            // function the operator names in the base, data or control
            // function library): an operator without one stays out.
            self.static_operator_callee(receiver, steps)
                .ok_or(UnsupportedConfiguration)?
        } else {
            membership_evidence::first_unowned_member(
                self,
                &raw,
                receiver,
                "FeatureMembership",
                "Function",
                None,
                steps,
            )
            .ok_or(InvalidRelationship)?
        };
        let features = batch
            .features(self, callee, steps)
            .map_err(|issue| match issue {
                super::ConstructorBindingIssue::IncompleteFeatures(issue) => {
                    IncompleteInputs(issue)
                }
                super::ConstructorBindingIssue::WorkLimit => WorkLimit,
                _ => IncompleteProvider,
            })?;
        let inputs = features.inputs;
        if operator {
            // The admitted generic parameter rule pairs direct owned slots;
            // inherited-only or interleaved-output signatures stay qualified.
            charge(
                steps,
                inputs
                    .len()
                    .saturating_add(features.directed_features.len()),
            )?;
            let mut directed = features.directed_features.iter().filter(|feature| {
                let membership = self.elements[feature.0].owning_relationship;
                !membership.is_some_and(|m| self.elements[m].ty == "ReturnParameterMembership")
            });
            for input in &inputs {
                let membership = self.elements[input.0]
                    .owning_relationship
                    .ok_or(InvalidRelationship)?;
                if semantic_ownership::checked_relationship_carrier(self, &raw, membership, steps)
                    != Some(Some(callee))
                    || directed.next() != Some(input)
                {
                    return Err(UnsupportedConfiguration);
                }
            }
        }
        let raw = StoredStructure::for_query(self, steps).ok_or(IncompleteProvider)?;
        if !operator
            && membership_evidence::first_unowned_member(
                self,
                &raw,
                receiver,
                "FeatureMembership",
                "Function",
                None,
                steps,
            ) != Some(callee)
        {
            return Err(StaleEvidence);
        }
        let domains = raw
            .membership_domains(self, steps)
            .ok_or(IncompleteProvider)?;
        let inverse = raw.typing(self, steps).ok_or(IncompleteProvider)?;
        if !raw.ids_unique
            || raw.annotations_incomplete
            || inverse.sources_incomplete
            || self.metadata_associations_incomplete
            || !domains.owner_complete(receiver)
            || raw.metadata_annotation_targets.contains(&receiver)
            || self
                .metadata_of
                .get(&receiver)
                .is_some_and(|m| !m.is_empty())
            || !semantic_ownership::owned_feature_projection_complete(self, receiver)
        {
            return Err(IncompleteProvider);
        }
        let stamp = Stamp::capture_builder(self);
        charge(steps, inputs.len())?;
        let eligible: HashSet<_> = inputs.iter().map(|e| e.0).collect();
        let relationships =
            semantic_ownership::owned_relationships(self, receiver).ok_or(IncompleteProvider)?;
        charge(steps, relationships.len())?;
        let relationships: Vec<_> = relationships.iter().collect();
        let mut seen = HashSet::new();
        let mut mapped = HashMap::new();
        let mut argument_position = 0;
        for relationship in relationships {
            if !seen.insert(relationship)
                || semantic_ownership::checked_relationship_carrier(self, &raw, relationship, steps)
                    != Some(Some(receiver))
            {
                return Err(InvalidRelationship);
            }
            let kind = self.elements[relationship].ty;
            if !conforms(kind, "FeatureMembership") {
                continue;
            }
            let parameter = membership_evidence::member(self, &raw, receiver, relationship, steps)
                .ok_or(InvalidRelationship)?;
            if !domains.owner_complete(parameter)
                || raw.metadata_annotation_targets.contains(&parameter)
                || self
                    .metadata_of
                    .get(&parameter)
                    .is_some_and(|m| !m.is_empty())
                || self.elements[parameter].ty != "Feature"
            {
                return Err(IncompleteProvider);
            }
            let direction = membership_evidence::parameter_direction(self, &raw, parameter, steps)
                .ok_or(InvalidRelationship)?;
            let valuation = membership_evidence::valuation(self, &raw, parameter, steps)
                .ok_or(InvalidRelationship)?;
            if conforms(kind, "ReturnParameterMembership") {
                if direction != Some("out") || valuation.is_some() {
                    return Err(UnsupportedConfiguration);
                }
                continue;
            }
            if kind != "ParameterMembership" || direction != Some("in") {
                return Err(UnsupportedConfiguration);
            }
            let position = argument_position;
            argument_position += 1;
            let (value_membership, value) = valuation.ok_or(UnmappedArgument)?;
            for key in ["isInitial", "isDefault"] {
                if self.elements[value_membership]
                    .props
                    .get(key)
                    .and_then(|v| v.as_bool())
                    == Some(true)
                {
                    return Err(UnsupportedConfiguration);
                }
            }
            let owned = semantic_ownership::owned_relationships(self, parameter)
                .ok_or(IncompleteProvider)?;
            charge(steps, owned.len())?;
            let owned: Vec<_> = owned.iter().collect();
            let mut target = None;
            let mut witnessed = HashSet::new();
            for rel in owned.iter().copied().chain(
                inverse
                    .relationships
                    .get(&parameter)
                    .into_iter()
                    .flatten()
                    .copied(),
            ) {
                charge(steps, 1)?;
                if !witnessed.insert(rel) {
                    continue;
                }
                let row = &self.elements[rel];
                // Extra owned features, conjugation or value-affecting metadata
                // require a broader provider; do not silently drop them.
                if is_a!(row, "FeatureMembership") || is_a!(row, "Conjugation") {
                    return Err(UnsupportedConfiguration);
                }
                if !is_a!(row, "Redefinition") {
                    continue;
                }
                if target.is_some() {
                    return Err(UnsupportedConfiguration);
                }
                if !owned.contains(&rel)
                    || semantic_ownership::checked_relationship_carrier(self, &raw, rel, steps)
                        != Some(Some(parameter))
                    || !self.static_chain_row_current(rel)
                    || !self.result_redefinition_row_current(rel)
                {
                    return Err(InvalidRelationship);
                }
                let implied = match row.props.get("isImplied") {
                    None => false,
                    Some(v) => v.as_bool().ok_or(InvalidRelationship)?,
                };
                let mapped_input = type_relations::endpoint_with_carrier(
                    self,
                    parameter,
                    Some(parameter),
                    rel,
                    &["specific", "subsettingFeature", "redefiningFeature"],
                    &["general", "subsettedFeature", "redefinedFeature"],
                    "Feature",
                    steps,
                )
                .ok_or(InvalidRelationship)?;
                if !eligible.contains(&mapped_input) {
                    return Err(UnmappedArgument);
                }
                if implied {
                    // Generic parameter ordinals include output parameters. An
                    // input-only position cannot repair a declined shared plan.
                    // Source flags alone never admit a purported implied edge.
                    if self.is_authored(rel)
                        || inputs.get(position) != Some(&ElementRef(mapped_input))
                        || !self.semantic_ownership.as_ref().is_some_and(|view| {
                            view.matches_suffix(self)
                                && view.generated_relationship_owner(rel) == Some(parameter)
                        })
                    {
                        return Err(UnsupportedConfiguration);
                    }
                    // The row is the positional planner's, over the callee
                    // typing the static plan gives the receiver, or the
                    // dynamic plan's where that plan is in effect: the
                    // effective positional table is the proof either way,
                    // and a stale dynamic plan over this receiver is none.
                    if !self.dynamic_evidence_current(receiver) {
                        return Err(StaleEvidence);
                    }
                    let positional = self
                        .effective_positional_redefinitions()
                        .ok_or(StaleEvidence)?;
                    if self
                        .effective_dynamic_plan()
                        .is_some_and(|plan| plan.incomplete_bases.contains(&receiver))
                        || positional.incomplete.contains(&receiver)
                    {
                        return Err(IncompleteProvider);
                    }
                    let targets = positional.targets.get(&parameter).ok_or(UnmappedArgument)?;
                    charge(steps, targets.len().saturating_add(1))?;
                    if targets.as_slice() != [mapped_input] {
                        return Err(UnsupportedConfiguration);
                    }
                } else if !self.is_authored(rel) {
                    return Err(InvalidRelationship);
                }
                target = Some(mapped_input);
            }
            let input = if let Some(target) = target {
                target
            } else if let Some(proposed) = proposed.as_deref_mut().filter(|_| operator) {
                let target = inputs.get(position).ok_or(UnmappedArgument)?.0;
                proposed.insert(parameter, vec![target]);
                target
            } else {
                return Err(UnmappedArgument);
            };
            if mapped
                .insert(
                    input,
                    InvocationBinding {
                        input: ElementRef(input),
                        parameter: ElementRef(parameter),
                        value: ElementRef(value),
                    },
                )
                .is_some()
            {
                return Err(DuplicateArgument);
            }
        }
        charge(steps, inputs.len())?;
        let bindings = inputs.iter().filter_map(|i| mapped.remove(&i.0)).collect();
        if !stamp.current_builder(self) {
            return Err(StaleEvidence);
        }
        Ok(InvocationBindings {
            callee: ElementRef(callee),
            inputs,
            bindings,
        })
    }
}

impl super::Builder {
    /// The function an operator expression's static callee typing names,
    /// read as the planner planned it and required to stand as a current
    /// row of the expression: `None` where the operator resolves to no
    /// loaded library function, or the row is not there or not current.
    pub(super) fn static_operator_callee(
        &mut self,
        receiver: usize,
        steps: &mut usize,
    ) -> Option<usize> {
        charge(steps, 2).ok()?;
        let names = self.implied_names();
        let callee = self.instantiation_callee(receiver, &names)?;
        if !is_a!(self.elements[callee], "Function") {
            return None;
        }
        let callee_id = self.elements[callee].id;
        let rows: Vec<usize> = semantic_ownership::owned_relationships(self, receiver)?
            .iter()
            .collect();
        charge(steps, rows.len()).ok()?;
        rows.into_iter()
            .any(|row| {
                is_a!(self.elements[row], "FeatureTyping")
                    && !self.is_authored(row)
                    && self.static_chain_row_current(row)
                    && self.elements[row]
                        .props
                        .get("type")
                        .and_then(|v| v.as_reference())
                        == Some(callee_id)
            })
            .then_some(callee)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        json::{ClosurePolicy, PropertyError},
        model::{GraphFormat, Model},
    };
    const LIB: &str = "standard library package Base {classifier Anything; feature things:Anything;} standard library package Occurrences {class Occurrence specializes Base::Anything; feature occurrences:Occurrence subsets Base::things;} standard library package Performances {behavior Performance specializes Occurrences::Occurrence; function Evaluation specializes Performance {return result;} step performances:Performance subsets Occurrences::occurrences; expr evaluations:Evaluation subsets performances;}";
    fn fixture(source: &str, format: GraphFormat) -> (ResolvedModel, ElementRef) {
        let mut m = Model::with_graph_format(format);
        assert!(
            m.add_library_source("binding-library.kerml", LIB)
                .diagnostics
                .is_empty()
        );
        let parsed = m.add_source("bindings.kerml", source);
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let r = ResolvedModel::build(&m);
        let call = ElementRef(
            r.b.elements
                .iter()
                .position(|e| e.ty == "InvocationExpression")
                .unwrap(),
        );
        (r, call)
    }
    #[test]
    fn accepted_call_that_becomes_unadmitted_cannot_reuse_old_family() {
        let (mut r, call) = fixture(
            "function F {in p; return result;} feature call=F(1);",
            GraphFormat::CanonicalV3,
        );
        r.implied_relationships(call);
        assert!(r.invocation_binding_report(call).arguments.is_ok());
        let f = r.resolve_qualified("F").unwrap();
        assert_eq!(r.feature_type_report(call).function, Ok(Some(f)));
        // The callee typing and the argument's redefinition are the static
        // plan's rows; the dynamic plan lists the call and adds nothing.
        let current = r.b.effective_dynamic_plan().unwrap();
        assert!(current.affected_owners.contains(&call.0));
        assert!(current.tail.is_empty());
        let callee = r.b.elements[call.0]
            .owned_relationships
            .iter()
            .copied()
            .find(|&row| {
                is_a!(r.b.elements[row], "Membership")
                    && !is_a!(r.b.elements[row], "FeatureMembership")
            })
            .unwrap();
        r.b.elements[callee]
            .props
            .insert("memberElement", serde_json::json!({"@ref":"Missing"}));
        assert!(r.invocation_binding_report(call).arguments.is_err());
        // An edit transaction retracts the shared tail before replanning. The
        // unsupported call may then be locally qualified, never retain old
        // dynamic rows under a new accepted plan with a smaller owner set.
        r.discard_owned_result_tail();
        r.implied_relationships(call);
        // The static prediction changed with the callee (no typing row for
        // it now), which cannot rewrite the old rows: the dynamic plan
        // declines until a rebuild, and the stale rows certify nothing —
        // the audit reads the callee from the membership, which names
        // nothing.
        assert!(r.b.effective_dynamic_plan().is_none());
        assert!(r.invocation_binding_report(call).arguments.is_err());
        assert!(r.feature_type_report(call).function.is_err());
    }

    #[test]
    fn operator_bindings_follow_the_static_callee_row_on_both_formats() {
        use crate::json::ModelLevelEvaluability::{Evaluable, Unknown};
        for format in [GraphFormat::LegacyV2, GraphFormat::CanonicalV3] {
            let mut m = Model::with_graph_format(format);
            m.add_library_source("binding-library.kerml", LIB);
            m.add_library_source(
                "numeric-functions.kerml",
                "standard library package DataFunctions {function '+' {in a; in b; return r;} function '<' {in a; in b; return r;}} ",
            );
            m.add_source("operator.kerml", "feature sum=1+2; feature less=1<2;");
            let mut r = ResolvedModel::build(&m);
            let calls: Vec<_> = r
                .elements()
                .filter(|&e| r.element_type(e) == "OperatorExpression")
                .collect();
            assert_eq!(calls.len(), 2);
            // Before the rows exist no positional proof is published.
            assert!(r.invocation_binding_report(calls[0]).arguments.is_err());
            // The eligibility proof does not wait on the binding provider:
            // the operator's designated function is resolved by name and the
            // operands are the expression's own parameters' values.
            assert_eq!(
                r.model_level_evaluability(calls[0]).classification,
                Evaluable
            );
            for (call, name) in calls.iter().copied().zip(["+", "<"]) {
                let _ = r.implied_relationships(call);
                let report = r.invocation_binding_report(call).arguments.unwrap();
                assert_eq!(report.bindings.len(), 2, "{format:?} {name}");
                let function = r
                    .resolve_qualified(&format!("DataFunctions::'{name}'"))
                    .unwrap();
                assert_eq!(report.callee, function, "{format:?} {name}");
            }
            assert_eq!(
                r.model_level_evaluability(calls[0]).classification,
                Evaluable
            );
            // An operator naming no library function has no row and no
            // bindings.
            r.b.elements[calls[0].0]
                .props
                .insert("operator", serde_json::json!("missing"));
            assert!(r.invocation_binding_report(calls[0]).arguments.is_err());
            assert!(matches!(
                r.model_level_evaluability(calls[0]).classification,
                Unknown(_)
            ));
        }
    }
    #[test]
    fn operator_callee_is_the_first_library_package_declaring_it() {
        // The callee is the planner's: `BaseFunctions` before
        // `DataFunctions`, by the loaded library's declared names; a package
        // that declares nothing of the name (an import, an alias to nothing)
        // does not take the operator.
        for (earlier, package) in [
            (
                "standard library package BaseFunctions {public import Missing::*;}",
                "DataFunctions",
            ),
            (
                "standard library package BaseFunctions {function '+' {in a; in b; return r;}}",
                "BaseFunctions",
            ),
            (
                "standard library package BaseFunctions {alias '+' for Missing::unknown;}",
                "DataFunctions",
            ),
        ] {
            let mut m = Model::with_graph_format(GraphFormat::CanonicalV3);
            m.add_library_source("binding-library.kerml", LIB);
            m.add_library_source("earlier.kerml", earlier);
            m.add_library_source(
                "numeric.kerml",
                "standard library package DataFunctions {function '+' {in a; in b; return r;}}",
            );
            m.add_source("operator.kerml", "feature sum=1+2;");
            let mut r = ResolvedModel::build(&m);
            let call = r
                .elements()
                .find(|&e| r.element_type(e) == "OperatorExpression")
                .unwrap();
            r.implied_relationships(call);
            let report = r
                .invocation_binding_report(call)
                .arguments
                .unwrap_or_else(|e| panic!("{earlier}: {e:?}"));
            let function = r.resolve_qualified(&format!("{package}::'+'")).unwrap();
            assert_eq!(report.callee, function, "{earlier}");
        }
        // The real designated packages use private imports. They cannot
        // contribute an externally selected operator and do not block proof.
        let mut m = Model::with_graph_format(GraphFormat::CanonicalV3);
        m.add_library_source("binding-library.kerml", LIB);
        m.add_library_source("numeric.kerml", "standard library package BaseFunctions {private import Base::*;} standard library package DataFunctions {private import Base::Anything; function '+' {in a; in b; return r;}}");
        m.add_source("operator.kerml", "feature sum=1+2;");
        let mut r = ResolvedModel::build(&m);
        // Serialized imports may omit the normative default-private flag.
        for index in 0..r.b.elements.len() {
            let row = &mut r.b.elements[index];
            if is_a!(row, "Import") {
                let old = row.props.to_json();
                row.props = crate::properties::Properties::new();
                for (key, value) in old {
                    if key != "visibility" {
                        row.props.insert(&key, value);
                    }
                }
            }
        }
        let call = r
            .elements()
            .find(|&e| r.element_type(e) == "OperatorExpression")
            .unwrap();
        r.implied_relationships(call);
        assert_eq!(
            r.invocation_binding_report(call)
                .arguments
                .unwrap()
                .bindings
                .len(),
            2
        );
    }
    #[test]
    fn unavailable_numeric_operator_does_not_poison_valid_invocations() {
        let (mut r, call) = fixture(
            "function F {in a; return r;} feature x=F(1); feature unsupported=1+2;",
            GraphFormat::CanonicalV3,
        );
        let _ = r.implied_relationships(call);
        assert_eq!(
            r.invocation_binding_report(call)
                .arguments
                .unwrap()
                .bindings
                .len(),
            1
        );
    }
    #[test]
    fn named_arguments_preserve_input_order_and_do_not_truncate_at_omissions() {
        for format in [GraphFormat::LegacyV2, GraphFormat::CanonicalV3] {
            for args in ["b=2, a=1", "b=2", ""] {
                let (mut r, call) = fixture(
                    &format!("function F {{in a; in b; return r;}} feature x=F({args});"),
                    format,
                );
                let len = r.b.elements.len();
                let a = r.resolve_qualified("F::a").unwrap();
                let b = r.resolve_qualified("F::b").unwrap();
                let report = r.invocation_binding_report(call);
                let result = report.arguments.unwrap();
                assert_eq!(result.inputs, [a, b]);
                let expected = match args {
                    "" => vec![],
                    "b=2" => vec![b],
                    _ => vec![a, b],
                };
                assert_eq!(
                    result.bindings.iter().map(|b| b.input).collect::<Vec<_>>(),
                    expected
                );
                assert_eq!(r.b.elements.len(), len);
                assert!(r.b.implied.is_none());
                assert_eq!(
                    r.invocation_binding_report(call).arguments,
                    Ok(result.clone())
                );
                r.set_closure_policy(ClosurePolicy::Closure {
                    include_implied: true,
                });
                assert_eq!(
                    r.property(call, "argument")
                        .unwrap()
                        .as_array()
                        .unwrap()
                        .len(),
                    result.bindings.len()
                );
            }
        }
    }
    #[test]
    fn positional_bindings_require_a_current_published_plan_and_aligned_inputs() {
        for format in [GraphFormat::LegacyV2, GraphFormat::CanonicalV3] {
            for source in [
                "function F {in a; in b; return r;} feature x=F(1,2);",
                "function F {in a; in b; return r;} feature x=F(1,b=2);",
            ] {
                let (mut r, call) = fixture(source, format);
                assert!(r.invocation_binding_report(call).arguments.is_err());
                r.set_closure_policy(ClosurePolicy::Closure {
                    include_implied: true,
                });
                let _ = r.implied_relationships(call);
                let count = r.b.elements.len();
                let report = r
                    .invocation_binding_report(call)
                    .arguments
                    .unwrap_or_else(|e| panic!("{source}: {e:?}"));
                assert_eq!(report.bindings.len(), 2);
                assert_eq!(
                    report.bindings.iter().map(|b| b.input).collect::<Vec<_>>(),
                    report.inputs
                );
                assert_eq!(
                    r.property(call, "argument")
                        .unwrap()
                        .as_array()
                        .unwrap()
                        .len(),
                    2
                );
                assert_eq!(r.b.elements.len(), count);
                assert_eq!(
                    r.invocation_binding_report_with_budget(call, crate::eval::MAX_STEPS)
                        .arguments,
                    Err(WorkLimit)
                );
                assert_eq!(r.invocation_binding_report(call).arguments, Ok(report));
            }
        }
    }
    #[test]
    fn admitted_positional_bindings_replay_across_prepared_library_paths() {
        use crate::{libcache::LibraryCache, prepared::PreparedLibrary};
        use std::sync::Arc;
        for format in [GraphFormat::LegacyV2, GraphFormat::CanonicalV3] {
            let mut base = Model::with_graph_format(format);
            base.add_library_source("binding-library.kerml", LIB);
            base.record_library_cache();
            ResolvedModel::build(&base);
            let cache =
                LibraryCache::from_bytes(&base.take_recorded_library_cache().unwrap().to_bytes())
                    .unwrap();
            let prepared = base.prepare_library().unwrap();
            let decoded = Arc::new(
                PreparedLibrary::from_bytes(&prepared.to_bytes(131).unwrap(), 131).unwrap(),
            );
            let mut expected = None;
            for mode in 0..4 {
                let mut m = Model::with_graph_format(format);
                match mode {
                    2 => Arc::clone(&prepared).install(&mut m).unwrap(),
                    3 => Arc::clone(&decoded).install(&mut m).unwrap(),
                    _ => {
                        m.add_library_source("binding-library.kerml", LIB);
                        if mode == 1 {
                            m.set_library_cache(cache.clone());
                        }
                    }
                }
                m.add_source(
                    "bindings.kerml",
                    "function F {in a; in b; return r;} feature x=F(1,b=2);",
                );
                let mut r = ResolvedModel::build(&m);
                let call = r
                    .elements()
                    .find(|&e| r.element_type(e) == "InvocationExpression")
                    .unwrap();
                let before =
                    crate::full::resolved_to_full_json(&mut r, &m, Default::default()).unwrap();
                let report = r.invocation_binding_report(call).arguments.unwrap();
                let ids: Vec<_> = report
                    .bindings
                    .iter()
                    .map(|b| {
                        (
                            r.element_id(b.input),
                            r.element_id(b.parameter),
                            r.element_id(b.value),
                        )
                    })
                    .collect();
                if let Some(ref expected) = expected {
                    assert_eq!(&ids, expected);
                } else {
                    expected = Some(ids);
                }
                assert_eq!(
                    crate::full::resolved_to_full_json(&mut r, &m, Default::default()).unwrap(),
                    before
                );
            }
        }
    }
    #[test]
    fn output_first_and_authored_implied_flags_never_supply_positional_proof() {
        // A function's parameters are its own, then the inherited ones
        // after them: `F(1, 2)` binds the two `A` declares.
        let (mut r, call) = fixture(
            "function A {in a; in b; return r;} function F specializes A; feature x=F(1,2);",
            GraphFormat::LegacyV2,
        );
        r.set_closure_policy(ClosurePolicy::Closure {
            include_implied: true,
        });
        let _ = r.to_full_json_strict();
        assert!(r.invocation_binding_report(call).arguments.is_ok());
        // An output before the input takes no position: the argument binds
        // `a` (KerML `validateInvocationExpressionParameterRedefinition`).
        let (mut r, call) = fixture(
            "function F {out feature priorOutput; in a; return r;} feature x=F(1);",
            GraphFormat::LegacyV2,
        );
        r.set_closure_policy(ClosurePolicy::Closure {
            include_implied: true,
        });
        let _ = r.to_full_json_strict();
        let report = r.invocation_binding_report(call).arguments.unwrap();
        assert_eq!(report.bindings.len(), 1);
        assert_eq!(
            report.bindings[0].input,
            r.resolve_qualified("F::a").unwrap()
        );
        // A third argument with two inputs stays unmapped.
        let (mut r, call) = fixture(
            "function F {in a; in b; return r;} feature x=F(1,2,3);",
            GraphFormat::LegacyV2,
        );
        r.set_closure_policy(ClosurePolicy::Closure {
            include_implied: true,
        });
        let _ = r.to_full_json_strict();
        assert!(r.invocation_binding_report(call).arguments.is_err());
        let (mut r, call) = fixture(
            "function F {in a; return r;} feature x=F(a=1);",
            GraphFormat::LegacyV2,
        );
        let binding = r
            .invocation_binding_report(call)
            .arguments
            .unwrap()
            .bindings
            .remove(0);
        let relationship = r.b.elements[binding.parameter.0]
            .owned_relationships
            .iter()
            .copied()
            .find(|&i| r.b.elements[i].ty == "Redefinition")
            .unwrap();
        r.b.set(relationship, "isImplied", serde_json::json!(true));
        let _ = r.to_full_json_strict();
        assert!(r.invocation_binding_report(call).arguments.is_err());
    }
    #[test]
    fn positional_snapshot_rejects_same_length_input_and_generated_endpoint_edits() {
        for change in [0, 1, 2] {
            let (mut r, call) = fixture(
                "function F {in a; in b; return r;} feature x=F(1,2);",
                GraphFormat::CanonicalV3,
            );
            let _ = r.to_full_json_strict();
            let mapping = r.invocation_binding_report(call).arguments.unwrap();
            let a = mapping.inputs[0];
            let b = mapping.inputs[1];
            match change {
                0 => r.b.set(a.0, "direction", serde_json::json!("out")),
                1 => {
                    let p = mapping.bindings[0].parameter.0;
                    let rel = semantic_ownership::owned_relationships(&r.b, p)
                        .unwrap()
                        .iter()
                        .find(|&i| r.b.elements[i].ty == "Redefinition")
                        .unwrap();
                    r.b.set(
                        rel,
                        "redefinedFeature",
                        serde_json::json!({"@id":r.element_id(b)}),
                    );
                }
                _ => {
                    let f = r.resolve_qualified("F").unwrap();
                    let mut rows = r.b.elements[f.0].owned_relationships.to_vec();
                    rows.swap(0, 1);
                    r.b.elements[f.0].owned_relationships = rows.into();
                }
            }
            assert!(r.invocation_binding_report(call).arguments.is_err());
        }
    }
    #[test]
    fn inherited_inputs_and_missing_earlier_inputs_keep_supplied_values() {
        let (mut r, call) = fixture(
            "function B {in a; in b; return r;} function F specializes B; feature x=F(b=2);",
            GraphFormat::LegacyV2,
        );
        let b = r.resolve_qualified("B::b").unwrap();
        assert_eq!(
            r.invocation_binding_report(call)
                .arguments
                .unwrap()
                .bindings[0]
                .input,
            b
        );
    }
    #[test]
    fn duplicate_unknown_and_unproved_positional_arguments_are_qualified() {
        for args in ["a=1,a=2", "z=1", "1", "a=1,b=2,c=3"] {
            let (mut r, call) = fixture(
                &format!("function F {{in a; in b; return r;}} feature x=F({args});"),
                GraphFormat::LegacyV2,
            );
            assert!(
                r.invocation_binding_report(call).arguments.is_err(),
                "{args}"
            );
        }
    }
    #[test]
    fn malformed_values_and_same_length_redefinition_edits_never_reuse_old_bindings() {
        for key in [
            "redefinedFeature",
            "isDefault",
            "isInitial",
            "ownedMemberParameter",
        ] {
            let (mut r, call) = fixture(
                "function F {in a; return r;} feature x=F(a=1);",
                GraphFormat::LegacyV2,
            );
            let report = r.invocation_binding_report(call).arguments.unwrap();
            let param = report.bindings[0].parameter.0;
            let row = match key {
                "ownedMemberParameter" => r.b.elements[param].owning_relationship.unwrap(),
                "redefinedFeature" => r.b.elements[param]
                    .owned_relationships
                    .iter()
                    .copied()
                    .find(|&e| r.b.elements[e].ty == "Redefinition")
                    .unwrap(),
                _ => r.b.elements[param]
                    .owned_relationships
                    .iter()
                    .copied()
                    .find(|&e| r.b.elements[e].ty == "FeatureValue")
                    .unwrap(),
            };
            r.b.elements[row].props.insert(key, serde_json::Value::Null);
            assert!(
                r.invocation_binding_report(call).arguments.is_err(),
                "{key}"
            );
        }
    }
    #[test]
    fn inverse_orphan_value_is_not_an_absence_or_unique_value_proof() {
        let (mut r, call) = fixture(
            "function F {in a; return r;} feature x=F(a=1);",
            GraphFormat::LegacyV2,
        );
        let binding = r
            .invocation_binding_report(call)
            .arguments
            .unwrap()
            .bindings
            .remove(0);
        let param = binding.parameter.0;
        let value = r.b.elements[param]
            .owned_relationships
            .iter()
            .copied()
            .find(|&e| r.b.elements[e].ty == "FeatureValue")
            .unwrap();
        r.b.elements[param].owned_relationships = r.b.elements[param]
            .owned_relationships
            .iter()
            .copied()
            .filter(|&e| e != value)
            .collect::<Vec<_>>()
            .into();
        let id = r.b.elements[param].id;
        r.b.elements[value]
            .props
            .insert("featureWithValue", serde_json::json!({"@id":id}));
        assert!(r.invocation_binding_report(call).arguments.is_err());
    }
    #[test]
    fn budget_retry_and_policy_are_explicit() {
        let (mut r, call) = fixture(
            "function F {in a; return r;} feature x=F(a=1);",
            GraphFormat::LegacyV2,
        );
        assert_eq!(
            r.invocation_binding_report_with_budget(call, crate::eval::MAX_STEPS)
                .arguments,
            Err(WorkLimit)
        );
        assert!(r.invocation_binding_report(call).arguments.is_ok());
        assert_eq!(
            r.property(call, "argument"),
            Err(PropertyError::Approximate)
        );
    }
}
