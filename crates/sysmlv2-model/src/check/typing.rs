//! Explicit typing restrictions from the abstract-syntax property types.
//!
//! Metaclass inheritance comes from the pinned XMI, so e.g. a requirement
//! definition is also a predicate, and an interface definition is also an
//! association structure. This is separate from user-model specialization.

use crate::{
    json::{ElementRef, ResolvedModel},
    metaclass,
    model::Model,
};
use std::collections::BTreeMap;
use sysmlv2_syntax::{Span, diag::Diagnostic};

/// (allowed metaclass, at most one non-redundant explicit type).
fn restriction(usage: &str) -> Option<(&'static str, bool)> {
    Some(match usage {
        "AttributeUsage" => ("DataType", false),
        "EnumerationUsage" => ("EnumerationDefinition", true),
        "OccurrenceUsage" | "ItemUsage" | "PartUsage" | "EventOccurrenceUsage" => ("Class", false),
        "PortUsage" => ("PortDefinition", false),
        "ConnectionUsage" => ("AssociationStructure", false),
        "InterfaceUsage" => ("InterfaceDefinition", false),
        "AllocationUsage" => ("AllocationDefinition", false),
        "FlowUsage" | "SuccessionFlowUsage" => ("Interaction", false),
        "ActionUsage" | "PerformActionUsage" => ("Behavior", false),
        "StateUsage" | "ExhibitStateUsage" => ("StateDefinition", false),
        "CalculationUsage" => ("Function", true),
        "ConstraintUsage" | "AssertConstraintUsage" => ("Predicate", true),
        "RequirementUsage" | "SatisfyRequirementUsage" | "ConcernUsage" => {
            ("RequirementDefinition", true)
        }
        "CaseUsage" => ("CaseDefinition", true),
        "AnalysisCaseUsage" => ("AnalysisCaseDefinition", true),
        "VerificationCaseUsage" => ("VerificationCaseDefinition", true),
        "UseCaseUsage" | "IncludeUseCaseUsage" => ("UseCaseDefinition", true),
        "RenderingUsage" => ("RenderingDefinition", true),
        "ViewUsage" => ("ViewDefinition", true),
        "ViewpointUsage" => ("ViewpointDefinition", true),
        "ReferenceUsage" => ("Classifier", false),
        // Metadata has a dedicated rule and diagnostic in check.rs.
        _ => return None,
    })
}

/// A usage typed by a definition its own kind cannot take — the pair the
/// typing check reports, exposed so a repair can rewrite the usage
/// keyword to the kind the definition belongs to.
#[derive(Clone, Debug)]
pub struct IncompatibleTyping {
    pub usage: ElementRef,
    pub target: ElementRef,
    /// Index into [`crate::model::Model::units`] of the usage.
    pub unit: usize,
    /// Span of the type name as written.
    pub span: Span,
    /// The metaclass family the usage's kind admits.
    pub allowed: &'static str,
}

/// One usage's declared typings with the restriction its kind places on
/// them.
struct TypingGroup {
    owner: usize,
    allowed: &'static str,
    /// The kind requires exactly one non-redundant type.
    single: bool,
    targets: Vec<(usize, Span)>,
}

/// The user usages with declared typings, grouped, each with its kind's
/// restriction. `model` filters library units by unit; without it the
/// element boundary does.
fn typing_groups(r: &ResolvedModel, model: Option<&Model>) -> Vec<TypingGroup> {
    let mut groups: BTreeMap<usize, Vec<(usize, Span)>> = BTreeMap::new();
    for (i, (owner, kind, _, name)) in r.b.spec_targets.iter().enumerate() {
        if *kind != "FeatureTyping" {
            continue;
        }
        let library = match model {
            Some(model) => model.is_library_unit(r.b.unit_of_elem(*owner)),
            None => *owner < r.b.lib_boundary,
        };
        if library {
            continue;
        }
        if let Some(target) = r.b.spec_resolved.get(i).copied().flatten() {
            groups.entry(*owner).or_default().push((target, name.span));
        }
    }
    let mut out = Vec::new();
    for (owner, targets) in groups {
        let ty = r.b.elements[owner].ty;
        let Some((mut allowed, mut single)) = restriction(ty) else {
            continue;
        };
        // Directed data/structural usages are parameters. They may carry
        // data or occurrence values, while kind-specific parameters such as
        // ports retain their narrower typing restrictions.
        if r.b.elements[owner]
            .props
            .get("direction")
            .is_some_and(|v| v.is_string())
            && matches!(
                ty,
                "AttributeUsage" | "PartUsage" | "ItemUsage" | "OccurrenceUsage"
            )
        {
            allowed = "Classifier";
        }
        if ty == "AttributeUsage"
            && targets
                .iter()
                .any(|(t, _)| metaclass::conforms(r.b.elements[*t].ty, "EnumerationDefinition"))
        {
            single = true;
        }
        out.push(TypingGroup {
            owner,
            allowed,
            single,
            targets,
        });
    }
    out
}

/// Every user usage typed by a definition its kind cannot take, as
/// [`validate`] reports them.
pub(super) fn incompatible_typings(r: &ResolvedModel) -> Vec<IncompatibleTyping> {
    let mut out = Vec::new();
    for g in typing_groups(r, None) {
        let unit = r.b.unit_of_elem(g.owner);
        for (target, span) in &g.targets {
            if !metaclass::conforms(r.b.elements[*target].ty, g.allowed) {
                out.push(IncompatibleTyping {
                    usage: ElementRef(g.owner),
                    target: ElementRef(*target),
                    unit,
                    span: *span,
                    allowed: g.allowed,
                });
            }
        }
    }
    out
}

pub(super) fn validate(r: &mut ResolvedModel, model: &Model) -> Vec<(usize, Diagnostic)> {
    let mut out = Vec::new();
    for g in typing_groups(r, Some(model)) {
        let ty = r.b.elements[g.owner].ty;
        let allowed = g.allowed;
        let unit = r.b.unit_of_elem(g.owner);
        let mut compatible = true;
        for (target, span) in &g.targets {
            let target_ty = r.b.elements[*target].ty;
            if !metaclass::conforms(target_ty, allowed) {
                compatible = false;
                out.push((
                    unit,
                    Diagnostic::error(
                        *span,
                        format!(
                            "{ty} must be typed by {allowed}; the declared type is a {target_ty}"
                        ),
                    ),
                ));
            }
        }
        if !g.single || !compatible {
            continue;
        }
        // Repeating a type is handled by the duplicate-specialization rule.
        // A general explicitly restated beside its specialization is also
        // redundant, not a second independent type.
        let mut distinct: Vec<usize> = g.targets.iter().map(|(t, _)| *t).collect();
        distinct.sort_unstable();
        distinct.dedup();
        let minimal: Vec<usize> = distinct
            .iter()
            .copied()
            .filter(|&t| {
                !distinct
                    .iter()
                    .any(|&other| other != t && r.b.conforms_upward(other, t))
            })
            .collect();
        if minimal.len() > 1 {
            out.push((
                unit,
                Diagnostic::error(
                    g.targets[1].1,
                    format!(
                        "{ty} must have exactly one non-redundant type; found {}",
                        minimal.len()
                    ),
                ),
            ));
        }
    }
    out
}
