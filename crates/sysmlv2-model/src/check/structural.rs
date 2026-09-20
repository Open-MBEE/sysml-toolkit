//! Static ownership, specialization, and feature-property constraints.
use super::facts::{Facts, flag, is};
use crate::{
    json::{Builder, ResolvedModel},
    model::Model,
};
use sysmlv2_syntax::{Span, diag::Diagnostic};

fn occurrence(b: &Builder, g: &Facts, e: usize) -> bool {
    is(b, e, "Class")
        || is(b, e, "OccurrenceUsage")
        || g.typed(b, e).iter().any(|&t| is(b, t, "Class"))
}
pub(super) fn variable(b: &Builder, g: &Facts, e: usize) -> bool {
    if flag(b, e, "isVariable") {
        return true;
    }
    if !is(b, e, "Usage") {
        return false;
    }
    // SysML derives variability from an occurrence owning type. A portion
    // is a time slice/snapshot rather than a variable feature.
    !flag(b, e, "isPortion")
        && !b.elements[e]
            .props
            .get("portionKind")
            .is_some_and(|p| p.is_string())
        && g.featuring(b, e).is_some_and(|o| occurrence(b, g, o))
}
pub(super) fn validate(r: &ResolvedModel, model: &Model, g: &Facts) -> Vec<(usize, Diagnostic)> {
    let b = &r.b;
    let mut out = Vec::new();
    let mut report = |e: usize, span: Span, rule: &'static str, msg: &str| {
        let unit = b.unit_of_elem(e);
        if !model.is_library_unit(unit) {
            out.push((unit, super::rule_error(span, rule, msg)));
        }
    };
    for (i, (e, kind, _, qn)) in b.spec_targets.iter().enumerate() {
        if !matches!(*kind, "Subclassification" | "Subsetting") || !is(b, *e, "Classifier") {
            continue;
        }
        let Some(t) = b.spec_resolved.get(i).copied().flatten() else {
            continue;
        };
        let cases = [
            (
                is(b, *e, "DataType") && (is(b, t, "Class") || is(b, t, "Association")),
                "validateDataTypeSpecialization",
                "A data type cannot specialize a class or association",
            ),
            (
                is(b, *e, "Class")
                    && (is(b, t, "DataType")
                        || (is(b, t, "Association") && !is(b, *e, "Association"))),
                "validateClassSpecialization",
                "A class cannot specialize a data type or an unrelated association family",
            ),
            (
                is(b, *e, "Structure") && is(b, t, "Behavior") && !is(b, t, "Structure"),
                "validateStructureSpecialization",
                "A structure cannot specialize a behavior",
            ),
            (
                is(b, *e, "Behavior") && is(b, t, "Structure") && !is(b, t, "Behavior"),
                "validateBehaviorSpecialization",
                "A behavior cannot specialize a structure",
            ),
        ];
        for (bad, rule, msg) in cases {
            if bad {
                report(*e, qn.span, rule, msg);
            }
        }
    }
    for (i, (e, kind, _, qn)) in b.spec_targets.iter().enumerate() {
        let Some(t) = b.spec_resolved.get(i).copied().flatten() else {
            continue;
        };
        if !matches!(*kind, "Subsetting" | "Redefinition") {
            continue;
        }
        if *kind == "Redefinition" {
            if g.featuring(b, *e).is_some() && g.featuring(b, *e) == g.featuring(b, t) {
                report(
                    *e,
                    qn.span,
                    "validateRedefinitionFeaturingTypes",
                    "Redefining and redefined features cannot have the same owning type",
                );
            }
            if flag(b, t, "isEnd") && !flag(b, *e, "isEnd") {
                report(
                    *e,
                    qn.span,
                    "validateRedefinitionEndConformance",
                    "A feature redefining an end must itself be an end",
                );
            }
            let from = b.elements[*e]
                .props
                .get("direction")
                .and_then(|v| v.as_str());
            let to = g
                .featuring(b, *e)
                .and_then(|o| g.direction_through(b, o, t));
            if from.is_some() && to.is_some() && from != to && to != Some("inout") {
                report(
                    *e,
                    qn.span,
                    "validateRedefinitionDirectionConformance",
                    "A redefining feature must have a compatible direction",
                );
            }
            if g.featuring(b, *e).is_none() && g.featuring(b, t).is_none() {
                report(
                    *e,
                    qn.span,
                    "validateRedefinitionFeaturingTypes",
                    "A package-level feature cannot redefine another package-level feature",
                );
            }
        }
        if flag(b, *e, "isVariable") && !flag(b, *e, "isConstant") && flag(b, t, "isConstant") {
            report(
                *e,
                qn.span,
                "validateSubsettingConstantConformance",
                "A variable subset of a constant feature must be constant",
            );
        }
        if b.elements[*e]
            .props
            .get("isUnique")
            .and_then(|v| v.as_bool())
            == Some(false)
            && flag(b, t, "isUnique")
        {
            report(
                *e,
                qn.span,
                "validateSubsettingUniquenessConformance",
                "A subset of a unique feature must be unique",
            );
        }
    }
    // Owners of result expressions, indexed once for the per-type walk.
    let result_owners: std::collections::HashSet<usize> =
        b.result_exprs.iter().map(|(o, _, _)| *o).collect();
    for e in 0..b.explicit_len() {
        if model.is_library_unit(b.unit_of_elem(e)) {
            continue;
        }
        let span = g.span(b, e);
        let ty = b.elements[e].ty;
        let variation = flag(b, e, "isVariation") || is(b, e, "EnumerationDefinition");
        if variation {
            for &m in &g.members[e] {
                if is(b, m, "Usage")
                    && !is(b, m, "MetadataUsage")
                    && !is(b, m, "EnumerationUsage")
                    && b.elements[m].owning_relationship.is_some_and(|rel| {
                        is(b, rel, "FeatureMembership") && !is(b, rel, "VariantMembership")
                    })
                {
                    report(
                        m,
                        g.span(b, m),
                        if is(b, e, "Definition") {
                            "validateDefinitionVariationMembership"
                        } else {
                            "validateUsageVariationMembership"
                        },
                        "A usage owned by a variation must be a variant",
                    );
                }
            }
            if g.supers[e]
                .iter()
                .any(|&s| flag(b, s, "isVariation") || is(b, s, "EnumerationDefinition"))
            {
                report(
                    e,
                    span,
                    if is(b, e, "Definition") {
                        "validateDefinitionVariationSpecialization"
                    } else {
                        "validateUsageVariationSpecialization"
                    },
                    "A variation cannot specialize another variation",
                );
            }
        }
        for (kind, membership, rule) in [
            (
                "CaseDefinition",
                "ObjectiveMembership",
                "validateCaseDefinitionOnlyOneObjective",
            ),
            (
                "CaseUsage",
                "ObjectiveMembership",
                "validateCaseUsageOnlyOneObjective",
            ),
            (
                "RequirementDefinition",
                "SubjectMembership",
                "validateRequirementDefinitionOnlyOneSubject",
            ),
            (
                "RequirementUsage",
                "SubjectMembership",
                "validateRequirementUsageOnlyOneSubject",
            ),
        ] {
            if !is(b, e, kind) {
                continue;
            }
            let owns_role = g.members[e].iter().any(|&m| {
                b.elements[m]
                    .owning_relationship
                    .is_some_and(|rel| is(b, rel, membership))
            });
            if !owns_role
                && g.effective_members(b, e)
                    .iter()
                    .filter(|&&m| {
                        b.elements[m]
                            .owning_relationship
                            .is_some_and(|rel| is(b, rel, membership))
                    })
                    .count()
                    > 1
            {
                report(
                    e,
                    span,
                    rule,
                    "At most one effective member with this parameter role is allowed",
                );
            }
        }
        for (kind, key, one, self_rule) in [
            (
                "Unioning",
                "unioningType",
                "validateOwnedUnioningNotOne",
                "validateTypeUnioningTypesNotSelf",
            ),
            (
                "Intersecting",
                "intersectingType",
                "validateOwnedIntersectingNotOne",
                "validateTypeIntersectingTypesNotSelf",
            ),
            (
                "Differencing",
                "differencingType",
                "validateOwnedDifferencingNotOne",
                "validateTypeDifferencingTypesNotSelf",
            ),
        ] {
            let targets = g.relations(b, e, kind, key);
            if targets.len() == 1 {
                report(
                    e,
                    span,
                    one,
                    "A type operation must have zero or at least two operands",
                );
            }
            if targets.contains(&e) {
                report(
                    e,
                    span,
                    self_rule,
                    "A type operation cannot name its own type as an operand",
                );
            }
        }
        if ty == "LibraryPackage" && flag(b, e, "isStandard") {
            report(
                e,
                span,
                "validateLibraryPackageNotStandard",
                "A user library package must not be marked standard",
            );
        }
        if is(b, e, "Feature") {
            let is_var = variable(b, g, e);
            if flag(b, e, "isVariable") && !g.featuring(b, e).is_some_and(|o| occurrence(b, g, o)) {
                report(
                    e,
                    span,
                    "validateFeatureIsVariable",
                    "A variable feature must be owned by an occurrence type",
                );
            }
            if flag(b, e, "isVariable") && flag(b, e, "isPortion") {
                report(
                    e,
                    span,
                    "validateFeaturePortionNotVariable",
                    "A portion cannot be variable",
                );
            }
            if flag(b, e, "isConstant") && !is_var {
                report(
                    e,
                    span,
                    "validateFeatureConstantIsVariable",
                    "Only a variable feature can be constant",
                );
            }
            for &rel in &b.elements[e].owned_relationships {
                if b.elements[rel].ty == "FeatureValue" && flag(b, rel, "isInitial") && !is_var {
                    report(
                        e,
                        span,
                        "validateFeatureValueIsInitial",
                        "An initialized feature must be variable",
                    );
                }
            }
        }
        if is(b, e, "OccurrenceUsage") {
            let typed = g.typed(b, e);
            let n = typed
                .iter()
                .filter(|&&t| flag(b, t, "isIndividual") && is(b, t, "Definition"))
                .count();
            if n > 1 {
                report(
                    e,
                    span,
                    "validateOccurrenceUsageIndividualDefinition",
                    "At most one individual definition may type an occurrence",
                );
            }
            if flag(b, e, "isIndividual") && n != 1 && !typed.is_empty() {
                report(
                    e,
                    span,
                    "validateOccurrenceUsageIndividualUsage",
                    "An individual usage must be typed by one individual definition",
                );
            }
            if b.elements[e]
                .props
                .get("portionKind")
                .is_some_and(|p| p.is_string())
                && !g.featuring(b, e).is_some_and(|o| {
                    is(b, o, "OccurrenceDefinition") || is(b, o, "OccurrenceUsage")
                })
            {
                report(
                    e,
                    span,
                    "validateOccurrenceUsageIsPortion",
                    "A snapshot or timeslice must be owned by an occurrence definition or usage",
                );
            }
        }
        if let Some(owner) = g.owner[e] {
            if is(b, e, "Usage") && !is(b, e, "PortUsage") && flag(b, e, "isComposite") {
                let rule = match b.elements[owner].ty {
                    "PortDefinition" => Some("validatePortDefinitionOwnedUsagesNotComposite"),
                    "PortUsage" => Some("validatePortUsageNestedUsagesNotComposite"),
                    _ => None,
                };
                if let Some(rule) = rule {
                    report(
                        e,
                        span,
                        rule,
                        "A non-port usage owned by a port must be referential",
                    );
                }
            }
            if is(b, e, "PortUsage")
                && (is(b, owner, "PortDefinition") || is(b, owner, "PortUsage"))
                && g.owner[owner]
                    .is_some_and(|o| is(b, o, "PortDefinition") || is(b, o, "PortUsage"))
                && b.elements[e]
                    .owning_relationship
                    .is_some_and(|rel| b.elements[rel].ty == "VariantMembership")
                && flag(b, e, "isComposite")
            {
                report(
                    e,
                    span,
                    "validatePortUsageIsReference",
                    "A port nested in a port must be referential",
                );
            }
            if flag(b, e, "isEnd")
                && (is(b, owner, "InterfaceDefinition") || is(b, owner, "InterfaceUsage"))
                && !is(b, e, "PortUsage")
            {
                let rule = if is(b, owner, "InterfaceDefinition") {
                    "validateInterfaceDefinitionEnd"
                } else {
                    "validateInterfaceUsageEnd"
                };
                report(e, span, rule, "An interface end must be a port");
            }
        }
        let required = match ty {
            "PerformActionUsage" => Some(("ActionUsage", "validatePerformActionUsageReference")),
            "ExhibitStateUsage" => Some(("StateUsage", "validateExhibitStateUsageReference")),
            "IncludeUseCaseUsage" => Some(("UseCaseUsage", "validateIncludeUseCaseUsageReference")),
            "SatisfyRequirementUsage" => Some((
                "RequirementUsage",
                "validateSatisfyRequirementUsageReference",
            )),
            "AssertConstraintUsage" => {
                Some(("ConstraintUsage", "validateAssertConstraintUsageReference"))
            }
            "EventOccurrenceUsage" => {
                Some(("OccurrenceUsage", "validateEventOccurrenceUsageReferent"))
            }
            _ => None,
        };
        if let Some((required, rule)) = required {
            for target in g.relations(b, e, "ReferenceSubsetting", "referencedFeature") {
                if !g.effective_kind(b, target, required) {
                    report(e, span, rule, &format!("{ty} must reference a {required}"));
                }
            }
        }
        if is(b, e, "ViewDefinition") || is(b, e, "ViewUsage") {
            let count = g.members[e]
                .iter()
                .filter(|&&m| {
                    b.elements[m]
                        .owning_relationship
                        .is_some_and(|rel| b.elements[rel].ty == "ViewRenderingMembership")
                })
                .count();
            if count > 1 {
                report(
                    e,
                    span,
                    if is(b, e, "ViewDefinition") {
                        "validateViewDefinitionOnlyOnvViewRendering"
                    } else {
                        "validateViewUsageOnlyOneRendering"
                    },
                    "A view may have at most one rendering",
                );
            }
        }
        if is(b, e, "Function") || is(b, e, "Expression") {
            let results = g
                .closure(e)
                .into_iter()
                .filter(|t| result_owners.contains(t))
                .count();
            if results > 1 {
                report(
                    e,
                    span,
                    if is(b, e, "Function") {
                        "validateFunctionResultExpressionMembership"
                    } else {
                        "validateExpressionResultExpressionMembership"
                    },
                    "Only one owned or inherited result expression is allowed",
                );
            }
            let returns = g.members[e]
                .iter()
                .filter(|&&m| {
                    b.elements[m]
                        .owning_relationship
                        .is_some_and(|r| b.elements[r].ty == "ReturnParameterMembership")
                })
                .count();
            if returns > 1 {
                report(
                    e,
                    span,
                    if is(b, e, "Function") {
                        "validateFunctionResultParameterMembership"
                    } else {
                        "validateExpressionResultParameterMembership"
                    },
                    "Only one return parameter is allowed",
                );
            }
        }
        if is(b, e, "Type")
            && g.members[e]
                .iter()
                .filter(|&&m| is(b, m, "Multiplicity"))
                .count()
                > 1
        {
            report(
                e,
                span,
                "validateTypeOwnedMultiplicity",
                "Only one multiplicity is allowed",
            );
        }
        for (rel, rule) in [
            (
                "ReferenceSubsetting",
                "validateFeatureOwnedReferenceSubsetting",
            ),
            ("CrossSubsetting", "validateFeatureOwnedCrossSubsetting"),
        ] {
            if b.elements[e]
                .owned_relationships
                .iter()
                .filter(|&&r| b.elements[r].ty == rel)
                .count()
                > 1
            {
                report(
                    e,
                    span,
                    rule,
                    "At most one relationship of this kind is allowed",
                );
            }
        }
        let chain = g.relations(b, e, "FeatureChaining", "chainingFeature");
        if b.elements[e]
            .owned_relationships
            .iter()
            .filter(|&&r| b.elements[r].ty == "FeatureChaining")
            .count()
            == 1
        {
            report(
                e,
                span,
                "validateFeatureChainingFeatureNotOne",
                "A feature chain must have at least two features",
            );
        }
        if chain.contains(&e) {
            report(
                e,
                span,
                "validateFeatureChainingFeaturesNotSelf",
                "A feature cannot chain through itself",
            );
        }
        if is(b, e, "StateDefinition") || is(b, e, "StateUsage") {
            let definition = is(b, e, "StateDefinition");
            for kind in ["entry", "do", "exit"] {
                let n = g.members[e]
                    .iter()
                    .filter(|&&m| {
                        b.elements[m].owning_relationship.is_some_and(|r| {
                            b.elements[r].ty == "StateSubactionMembership"
                                && b.elements[r].props.get("kind").and_then(|v| v.as_str())
                                    == Some(kind)
                        })
                    })
                    .count();
                if n > 1 {
                    report(
                        e,
                        span,
                        if definition {
                            "validateStateDefinitionSubactionKind"
                        } else {
                            "validateStateUsageSubactionKind"
                        },
                        "A state may have at most one subaction of each kind",
                    );
                }
            }
            if flag(b, e, "isParallel")
                && g.members[e]
                    .iter()
                    .any(|&m| is(b, m, "TransitionUsage") || is(b, m, "Succession"))
            {
                report(
                    e,
                    span,
                    if definition {
                        "validateStateDefinitionParallelSubactions"
                    } else {
                        "validateStateUsageParallelSubactions"
                    },
                    "A parallel state cannot own successions or transitions",
                );
            }
        }
        if is(b, e, "ControlNode")
            && !g.owner[e].is_some_and(|o| is(b, o, "ActionDefinition") || is(b, o, "ActionUsage"))
        {
            report(
                e,
                span,
                "validateControlNodeOwningType",
                "A control node must be owned by an action",
            );
        }
        if is(b, e, "Association") {
            let ends: Vec<_> = g.members[e]
                .iter()
                .copied()
                .filter(|&m| flag(b, m, "isEnd"))
                .collect();
            if ends.len() == 1 && g.supers[e].is_empty() {
                report(
                    e,
                    span,
                    "validateAssociationRelatedTypes",
                    "An association must have at least two related types",
                );
            }
            for end in ends {
                let types = g.typed(b, end);
                let minimal = types
                    .iter()
                    .filter(|&&t| !types.iter().any(|&u| u != t && g.closure(u).contains(&t)))
                    .count();
                if minimal > 1 {
                    report(
                        end,
                        g.span(b, end),
                        "validateAssociationEndTypes",
                        "An association end must have exactly one non-redundant type",
                    );
                }
            }
        }
        if b.elements[e]
            .owning_relationship
            .is_some_and(|r| b.elements[r].ty == "RequirementVerificationMembership")
        {
            let valid = g.owner[e].is_some_and(|o| {
                b.elements[o]
                    .owning_relationship
                    .is_some_and(|r| b.elements[r].ty == "ObjectiveMembership")
                    && g.owner[o].is_some_and(|c| {
                        is(b, c, "VerificationCaseDefinition") || is(b, c, "VerificationCaseUsage")
                    })
            });
            if !valid {
                report(
                    e,
                    span,
                    "validateRequirementVerificationMembershipOwningType",
                    "A requirement verification must be in the objective of a verification case",
                );
            }
        }
        if is(b, e, "MetadataFeature") {
            let types = g.typed(b, e);
            if !types.is_empty() && types.iter().all(|&t| flag(b, t, "isAbstract")) {
                report(
                    e,
                    span,
                    "validateMetadataFeatureMetadataNotAbstract",
                    "Metadata must have a concrete type",
                );
            }
        }
    }
    out
}
