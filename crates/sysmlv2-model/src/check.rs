//! Referential checks over a resolved multi-file model.

use sysmlv2_syntax::diag::Diagnostic;

mod actions;
mod chains;
mod connectors;
mod dimensions;
mod directions;
mod distinguishability;
mod endpoints;
mod expressions;
pub(crate) mod facts;
mod invocations;
mod multiplicities;
mod multiplicity_domains;
mod relationships;
mod scalars;
mod specialization;
mod structural;
mod typing;
mod values;

pub use distinguishability::InheritedNameCollision;
pub use typing::IncompatibleTyping;

/// Every inherited-name collision among the user elements — the pairs
/// the semantic check reports as `validateNamespaceDistinguishibility` —
/// for repairs that spell the missing redefinition.
pub fn inherited_name_collisions(
    r: &mut crate::json::ResolvedModel,
) -> Vec<InheritedNameCollision> {
    distinguishability::collisions(r)
}

/// Whether `metaclass` is `base` or one of its specializations in the
/// KerML/SysML metamodel (`PortDefinition` conforms to `Definition`).
#[must_use]
pub fn metaclass_conforms(metaclass: &str, base: &str) -> bool {
    crate::metaclass::conforms(metaclass, base)
}

/// Every user usage typed by a definition its own kind cannot take — the
/// pairs the semantic check reports as `X must be typed by Y` — for
/// repairs that rewrite the usage keyword.
#[must_use]
pub fn incompatible_typings(r: &crate::json::ResolvedModel) -> Vec<IncompatibleTyping> {
    typing::incompatible_typings(r)
}

/// Semantic diagnostics whose rule names occur in the pinned XMI. Labels
/// introduced by later validator versions are tracked separately in the
/// external-fixture contracts and do not enlarge the normative denominator.
pub const IMPLEMENTED_NORMATIVE_SEMANTIC_RULES: &[&str] = &[
    "validateAssertConstraintUsageReference",
    "validateAssignmentActionUsageReferent",
    "validateAssociationBinarySpecialization",
    "validateAssociationEndTypes",
    "validateAssociationRelatedTypes",
    "validateBehaviorSpecialization",
    "validateBindingConnectorIsBinary",
    "validateCaseDefinitionOnlyOneObjective",
    "validateCaseUsageOnlyOneObjective",
    "validateClassSpecialization",
    "validateConnectorRelatedFeatures",
    "validateConstructorExpressionNoDuplicateFeatureRedefinition",
    "validateControlNodeIncomingSuccessions",
    "validateControlNodeOutgoingSuccessions",
    "validateControlNodeOwningType",
    "validateCrossSubsettingCrossedFeature",
    "validateCrossSubsettingCrossingFeature",
    "validateDataTypeSpecialization",
    "validateDecisionNodeIncomingSuccessions",
    "validateDecisionNodeOutgoingSuccessions",
    "validateDefinitionVariationSpecialization",
    "validateExhibitStateUsageReference",
    "validateExpressionResultExpressionMembership",
    "validateExpressionResultParameterMembership",
    "validateFeatureChainingFeatureConformance",
    "validateFeatureChainingFeatureNotOne",
    "validateFeatureChainingFeaturesNotSelf",
    "validateFeatureConstantIsVariable",
    "validateFeatureCrossFeatureSpecialization",
    "validateFeatureCrossFeatureType",
    "validateFeatureIsVariable",
    "validateFeatureOwnedCrossSubsetting",
    "validateFeatureOwnedReferenceSubsetting",
    "validateFeaturePortionNotVariable",
    "validateFeatureReferenceExpressionReferentIsFeature",
    "validateFeatureValueIsInitial",
    "validateFeatureValueOverriding",
    "validateForkNodeIncomingSuccessions",
    "validateFunctionResultExpressionMembership",
    "validateFunctionResultParameterMembership",
    "validateIncludeUseCaseUsageReference",
    "validateInstantiationExpressionInstantiatedType",
    "validateInvocationExpressionInstantiatedType",
    "validateJoinNodeOutgoingSuccessions",
    "validateMergeNodeIncomingSuccessions",
    "validateMergeNodeOutgoingSuccessions",
    "validateMetadataFeatureAnnotatedElement",
    "validateMetadataFeatureBody",
    "validateNamespaceDistinguishibility",
    "validateOccurrenceUsageIndividualDefinition",
    "validateOccurrenceUsageIndividualUsage",
    "validateOccurrenceUsageIsPortion",
    "validatePerformActionUsageReference",
    "validatePortDefinitionOwnedUsagesNotComposite",
    "validatePortUsageIsReference",
    "validatePortUsageNestedUsagesNotComposite",
    "validateRedefinitionDirectionConformance",
    "validateRedefinitionEndConformance",
    "validateRedefinitionFeaturingTypes",
    "validateRequirementDefinitionOnlyOneSubject",
    "validateRequirementUsageOnlyOneSubject",
    "validateRequirementVerificationMembershipOwningType",
    "validateSatisfyRequirementUsageReference",
    "validateStateDefinitionParallelSubactions",
    "validateStateUsageParallelSubactions",
    "validateStructureSpecialization",
    "validateSubsettingConstantConformance",
    "validateSubsettingFeaturingTypes",
    "validateSubsettingUniquenessConformance",
    "validateTransitionFeatureMembershipGuardExpression",
    "validateTransitionUsageSuccession",
    "validateTransitionUsageTriggerActions",
    "validateTypeDifferencingTypesNotSelf",
    "validateTypeIntersectingTypesNotSelf",
    "validateTypeOwnedMultiplicity",
    "validateTypeUnioningTypesNotSelf",
    "validateUsageVariationSpecialization",
    "validateViewDefinitionOnlyOneViewRendering",
    "validateViewUsageOnlyOneViewRendering",
];

/// Referential checks over a resolved multi-file model:
/// unresolved references, unresolvable alias targets, circular
/// namespace imports, and user root declarations that share a name with
/// a standard-library root (reported as library-winning or ambiguous), attributed to the
/// unit they were written in (index into [`crate::model::Model::units`]).
///
/// Unresolved names, aliases, import cycles and root collisions are warnings;
/// ambiguous references are errors. The resolver covers 99.9%+ of the corpus, but a
/// small long tail of legitimate spellings is still beyond it (and some
/// corpus files contain genuine reference errors) — so unresolved names
/// must not fail conforming models. Library units are skipped.
pub fn validate_model(model: &crate::model::Model) -> Vec<(usize, Diagnostic)> {
    let mut r = crate::json::ResolvedModel::build(model);
    validate_model_with(&mut r, model)
}

/// [`validate_model`] over an already-built [`crate::json::ResolvedModel`] —
/// lets one build serve both referential and semantic checks (the
/// builder's unresolved list stays readable; run this before
/// [`validate_semantics_with`]).
pub fn validate_model_with(
    r: &mut crate::json::ResolvedModel,
    model: &crate::model::Model,
) -> Vec<(usize, Diagnostic)> {
    let report = crate::json::resolution_report_from(&mut r.b);
    // The alias-specific finding subsumes the generic unresolved one at the
    // same location.
    let alias_spans: std::collections::HashSet<(usize, u32)> = report
        .unresolved_aliases
        .iter()
        .map(|(unit, qn)| (*unit, qn.span.start))
        .collect();
    let blocked: std::collections::HashMap<(usize, u32), (String, &'static str)> = report
        .blocked
        .iter()
        .map(|b| {
            let member = r
                .element_qualified_name(b.member)
                .unwrap_or_else(|| b.name.to_display_string());
            ((b.unit, b.name.span.start), (member, b.visibility))
        })
        .collect();
    let mut out = Vec::new();
    for (unit, qn) in report.unresolved {
        if model.is_library_unit(unit) || alias_spans.contains(&(unit, qn.span.start)) {
            continue;
        }
        let message = match blocked.get(&(unit, qn.span.start)) {
            Some((member, visibility)) => format!(
                "unresolved reference `{}` — `{member}` exists but is {visibility}",
                qn.to_display_string()
            ),
            None => format!("unresolved reference `{}`", qn.to_display_string()),
        };
        out.push((unit, Diagnostic::warning(qn.span, message)));
    }
    for (unit, qn) in report.ambiguous {
        if model.is_library_unit(unit) {
            continue;
        }
        out.push((
            unit,
            Diagnostic::error(
                qn.span,
                format!(
                    "ambiguous reference `{}` resolves to multiple memberships",
                    qn.to_display_string()
                ),
            ),
        ));
    }
    for (unit, qn) in report.unresolved_aliases {
        if model.is_library_unit(unit) {
            continue;
        }
        out.push((
            unit,
            Diagnostic::warning(
                qn.span,
                format!("alias target `{}` does not resolve", qn.to_display_string()),
            ),
        ));
    }
    for (unit, qn) in report.import_cycles {
        if model.is_library_unit(unit) {
            continue;
        }
        out.push((
            unit,
            Diagnostic::warning(
                qn.span,
                format!(
                    "circular namespace import: `{}` transitively imports this \
                     namespace back",
                    qn.to_display_string()
                ),
            ),
        ));
    }
    for s in report.shadowed_roots {
        if model.is_library_unit(s.unit) {
            continue;
        }
        let tail = if s.resolves_to_library {
            "references resolve to the library"
        } else {
            "references to the name are ambiguous"
        };
        out.push((
            s.unit,
            Diagnostic::warning(
                s.span,
                format!(
                    "root {} `{}` shadows the standard library {} `{}`; {tail}",
                    root_kind_word(s.metaclass),
                    s.name,
                    root_kind_word(s.library_metaclass),
                    s.name,
                ),
            ),
        ));
    }
    // Report in source order per unit.
    out.sort_by_key(|(unit, d)| (*unit, d.span.start));
    out
}

/// The everyday word for a root declaration's metaclass in the
/// root-shadowing finding.
fn root_kind_word(metaclass: &str) -> &'static str {
    match metaclass {
        "Package" | "LibraryPackage" => "package",
        "Namespace" => "namespace",
        _ => "declaration",
    }
}

/// Whether element `e` belongs to a user unit. A build lowers its library
/// units before any user unit, so every element below the library boundary
/// is a library one: those are answered without locating their unit.
pub(crate) fn user_owned(b: &crate::json::Builder, model: &crate::model::Model, e: usize) -> bool {
    e >= b.lib_boundary && !model.is_library_unit(b.unit_of_elem(e))
}

/// The rows of a builder table that user elements own, copied once so a
/// pass can evaluate against `&mut r.b` while walking them. Library rows
/// never produce findings; skipping them by reference leaves the shared
/// library prefix untouched.
pub(crate) fn user_rows<'a, T: Clone + 'a>(
    b: &crate::json::Builder,
    model: &crate::model::Model,
    rows: impl IntoIterator<Item = &'a T>,
    owner: impl Fn(&T) -> usize,
) -> Vec<T> {
    rows.into_iter()
        .filter(|row| user_owned(b, model, owner(row)))
        .cloned()
        .collect()
}

/// A finding reporting the semantic rule `rule` names. The identifier
/// lands in the finding's `code`; it also stays spelled at the end of
/// the message, where the command-line and editor surfaces read it.
pub(crate) fn rule_error(
    span: sysmlv2_syntax::Span,
    rule: &'static str,
    message: impl std::fmt::Display,
) -> Diagnostic {
    Diagnostic::error(span, format!("{message} [{rule}]")).with_code(normative_rule(rule))
}

/// [`rule_error`] at warning severity.
pub(crate) fn rule_warning(
    span: sysmlv2_syntax::Span,
    rule: &'static str,
    message: impl std::fmt::Display,
) -> Diagnostic {
    Diagnostic::warning(span, format!("{message} [{rule}]")).with_code(normative_rule(rule))
}

/// The identifier of a rule in the spelling the pinned abstract syntax
/// uses. Two rules reached this implementation through an imported probe
/// suite that names them differently; their messages keep that spelling,
/// which the imported contracts are keyed by, while the finding carries
/// the pinned one.
fn normative_rule(rule: &'static str) -> &'static str {
    match rule {
        "validateViewDefinitionOnlyOnvViewRendering" => {
            "validateViewDefinitionOnlyOneViewRendering"
        }
        "validateViewUsageOnlyOneRendering" => "validateViewUsageOnlyOneViewRendering",
        other => other,
    }
}

/// [`user_rows`] over a table keyed by owning element.
pub(crate) fn user_entries<'a, V: Clone + 'a>(
    b: &crate::json::Builder,
    model: &crate::model::Model,
    entries: impl IntoIterator<Item = (&'a usize, &'a V)>,
) -> Vec<(usize, V)> {
    entries
        .into_iter()
        .filter(|(&e, _)| user_owned(b, model, e))
        .map(|(&e, v)| (e, v.clone()))
        .collect()
}

/// KerML 8.4-style semantic constraints over the resolved graph,
/// attributed like [`validate_model`]. Checked:
///
/// - **Multiplicity sanity** (errors): bounds that *provably* evaluate to a
///   negative number or to `lower > upper`. Bounds that reference unbound
///   features or fail to evaluate are left undecided (no diagnostic).
/// - **Explicit multiplicity containment** (warnings): supported header, body
///   and named domains are compared exactly in the specializing receiver.
///   Redefinition checks both ends; subsetting checks only the upper end.
///   Both features must have a unique explicit local domain. Incomplete,
///   cyclic, invalid or unevaluable domains cannot establish containment; a
///   bound referring to a member inside the constrained feature may be unsupported.
/// - **Contextual multiplicity validity** (errors): an explicit subsetting or
///   redefinition can make an authored valid range invalid in its receiver.
///   Each side is checked independently, even if the other has no local domain.
///   A finding requires a complete supported domain and a provably valid lexical
///   baseline; unknown baselines stay undecided. Shared named ranges are reported
///   once per specialization. Reporting is bounded to the first invalid range
///   on each side, so it is not an exhaustive validation of inherited ranges.
/// - **Self / circular subclassification** (errors): a definition that
///   (transitively) specializes itself. Feature subsetting/redefinition is
///   exempt — resolving a feature's own name to an inherited feature is the
///   idiomatic shorthand there.
/// - **Duplicate specializations** (warnings): the same target named twice
///   in one element's typing / subsetting / redefinition lists.
/// - **Metadata typing** (errors): a metadata feature (`@M`, `#M` prefix,
///   `metadata m : M`) whose typing resolves to anything other than a
///   `metadata def` / `metaclass`, or that declares more than one typing.
/// - **Feature-value scalar conformance** (warnings): a feature value that
///   *evaluates* to a scalar whose `ScalarValues` partition (Boolean /
///   String / the Number tower) can never conform to the feature's
///   declared type, or a non-integral rational bound to a feature whose
///   declared type specializes `Integer`. Anything subtler than
///   kind-level disjointness stays silent — see the check body for why
///   a stricter static rule would over-reject.
pub fn validate_semantics(model: &crate::model::Model) -> Vec<(usize, Diagnostic)> {
    let mut r = crate::json::ResolvedModel::build(model);
    validate_semantics_with(&mut r, model)
}

/// [`validate_semantics`] over an already-built [`crate::json::ResolvedModel`].
/// Preserves import provenance: speculative validation lookups are not source
/// references and must not hide unused imports from later analyses.
pub fn validate_semantics_with(
    r: &mut crate::json::ResolvedModel,
    model: &crate::model::Model,
) -> Vec<(usize, Diagnostic)> {
    let r = &mut *r;
    let used_imports = r.b.used_imports.clone();
    let mut out = Vec::new();

    out.extend(multiplicities::validate(r, model));
    out.extend(specialization::validate(r, model));
    out.extend(invocations::validate(r, model));
    out.extend(scalars::validate(r, model));
    out.extend(chains::validate(r, model));
    // The immutable facts already index ownership and binary relationship
    // targets for every later validator. Reuse them for connector checks too.
    let facts = facts::Facts::new(&mut r.b);
    out.extend(connectors::validate(r, model, &facts));
    out.extend(structural::validate(r, model, &facts));
    out.extend(structural::validate_directions(r, model, &facts));
    out.extend(endpoints::validate(r, model, &facts));
    out.extend(values::validate(r, model, &facts));
    out.extend(relationships::validate(r, model, &facts));
    out.extend(expressions::validate(r, model, &facts));
    out.extend(actions::validate(r, model, &facts));
    out.extend(typing::validate(r, model));
    out.extend(dimensions::validate(r, model));
    out.extend(distinguishability::validate(r, model));
    out.sort_by_key(|(unit, d)| (*unit, d.span.start));
    out.dedup_by(|a, b| a.0 == b.0 && a.1.span == b.1.span && a.1.message == b.1.message);
    r.b.used_imports = used_imports;
    out
}

/// Collect the feature references of an expression, in source order: the
/// `Ref` leaves and, with `chains`, every name chain (`a.b.c`) whole in
/// place of its root. Lambda bodies are not entered (their references
/// bind through runtime parameters), and a bracket's unit expression is
/// skipped (`[m]` names a measurement unit, not a model feature a
/// diagnostic should evaluate).
fn collect_feature_refs<'a>(
    e: &'a sysmlv2_syntax::ast::Expr,
    chains: bool,
    out: &mut Vec<&'a sysmlv2_syntax::ast::Expr>,
) {
    use sysmlv2_syntax::ast::{ArrowArgs, ExprKind};
    match &e.kind {
        ExprKind::Ref(_) => out.push(e),
        ExprKind::Literal(_)
        | ExprKind::Null
        | ExprKind::Extent { .. }
        | ExprKind::MetadataAccess { .. }
        | ExprKind::Body { .. } => {}
        ExprKind::Conditional {
            cond,
            then_branch,
            else_branch,
        } => {
            collect_feature_refs(cond, chains, out);
            collect_feature_refs(then_branch, chains, out);
            collect_feature_refs(else_branch, chains, out);
        }
        ExprKind::Binary { lhs, rhs, .. } => {
            collect_feature_refs(lhs, chains, out);
            collect_feature_refs(rhs, chains, out);
        }
        ExprKind::Unary { operand, .. } => collect_feature_refs(operand, chains, out),
        ExprKind::Classification { operand, .. } => {
            if let Some(o) = operand {
                collect_feature_refs(o, chains, out);
            }
        }
        ExprKind::ChainStep { target, .. } => {
            if chains && name_chain(e).is_some() {
                out.push(e);
            } else {
                collect_feature_refs(target, chains, out);
            }
        }
        ExprKind::Index { target, index } => {
            collect_feature_refs(target, chains, out);
            collect_feature_refs(index, chains, out);
        }
        ExprKind::Bracket { target, .. } => collect_feature_refs(target, chains, out),
        ExprKind::Arrow { target, args, .. } => {
            collect_feature_refs(target, chains, out);
            if let ArrowArgs::List(list) = args {
                for a in list {
                    collect_feature_refs(&a.value, chains, out);
                }
            }
        }
        ExprKind::Collect { target, .. } | ExprKind::Select { target, .. } => {
            collect_feature_refs(target, chains, out)
        }
        ExprKind::Invocation { args, .. } | ExprKind::Constructor { args, .. } => {
            for a in args {
                collect_feature_refs(&a.value, chains, out);
            }
        }
        ExprKind::Sequence(items) => {
            for i in items {
                collect_feature_refs(i, chains, out);
            }
        }
    }
}

/// The spelling of a reference or of a chain of names (`a.b.c`); `None`
/// for any other expression.
fn name_chain(e: &sysmlv2_syntax::ast::Expr) -> Option<String> {
    use sysmlv2_syntax::ast::{ExprKind, TargetRef};
    match &e.kind {
        ExprKind::Ref(qn) => Some(qn.to_display_string()),
        ExprKind::ChainStep {
            target,
            member: TargetRef::Name(member),
        } => Some(format!(
            "{}.{}",
            name_chain(target)?,
            member.to_display_string()
        )),
        _ => None,
    }
}

/// One feature reference of a constraint's result expression with its
/// own evaluation — the auxiliary "why" behind a verdict (`reserveKg =
/// 0.10` under a violated `reserveKg >= 0.15`; an unbound reference
/// under an undecided one).
#[derive(Clone, Debug)]
pub struct ConstraintBinding {
    /// The reference's source spelling (`reserveKg`, `Pkg::limit`).
    pub feature: String,
    /// Rendered evaluated value; `None` when the reference does not
    /// evaluate on its own (an unbound feature).
    pub value: Option<String>,
    /// Declaration site of the referenced feature's name: (unit index,
    /// span of the name token). `None` when the reference does not
    /// resolve or the element is synthesized.
    pub site: Option<(usize, sysmlv2_syntax::span::Span)>,
}

/// The feature references of `c`'s result expression, each evaluated on
/// its own in the constraint's scope — first occurrence per spelling.
/// Complements [`constraint_verdict`]: the pair is what a diagnostic
/// needs to say *why* (every binding of a decided verdict carries a
/// value; an undecided verdict's unbound references carry `None`).
pub fn constraint_bindings(
    r: &mut crate::json::ResolvedModel,
    c: &crate::json::ConstraintInfo,
) -> Vec<ConstraintBinding> {
    feature_bindings(r, c, None)
}

/// [`constraint_bindings`], or with a satisfaction claim's subject binding
/// seeded. A bound claim also reports each name chain whole
/// (`vehicle.mass = 950 [kg]`): its root is the satisfying feature itself,
/// which has no value worth showing.
fn feature_bindings(
    r: &mut crate::json::ResolvedModel,
    c: &crate::json::ConstraintInfo,
    overrides: Option<&std::collections::HashMap<usize, crate::eval::Value>>,
) -> Vec<ConstraintBinding> {
    let mut refs = Vec::new();
    collect_feature_refs(&c.expr, overrides.is_some(), &mut refs);
    let mut out: Vec<ConstraintBinding> = Vec::new();
    for probe in refs {
        let Some(feature) = name_chain(probe) else {
            continue;
        };
        if out.iter().any(|b| b.feature == feature) {
            continue;
        }
        let site = match &probe.kind {
            sysmlv2_syntax::ast::ExprKind::Ref(qn) => r
                .resolve_in(c.scope, qn)
                .and_then(|e| r.declaration_site(e)),
            _ => None,
        };
        let value = match overrides {
            Some(overrides) => r.evaluate_in_with(c.scope, probe, overrides),
            None => r.evaluate_in(c.scope, probe),
        };
        // An unvalued feature evaluates to itself as a bare element,
        // which renders opaquely (`<element>`) — that is the unbound
        // case for diagnostic purposes, not a value worth showing. A
        // reference *through* an unbound feature is undetermined for the
        // same reason and renders just as opaquely (`<indeterminate>`).
        let value = match value {
            Ok(
                crate::eval::Value::Element(_)
                | crate::eval::Value::Unbound(_)
                | crate::eval::Value::UnboundMember(_)
                | crate::eval::Value::Indeterminate,
            )
            | Err(_) => None,
            Ok(v) => Some(v.to_string()),
        };
        out.push(ConstraintBinding {
            feature,
            value,
            site,
        });
    }
    out
}

/// Verdict of one constraint-family element's trailing result expression
/// (checking only — no solving).
#[derive(Clone, Debug, PartialEq)]
pub enum ConstraintVerdict {
    /// The result expression evaluated to the asserted truth value.
    Satisfied,
    /// The result expression evaluated against the asserted truth value.
    Violated,
    /// Not decidable by evaluation — unbound features, unsupported
    /// constructs, or a non-boolean result. Carries the reason.
    Undecided(String),
}

/// One checked constraint.
#[derive(Clone, Debug)]
pub struct ConstraintCheck {
    /// Index into [`crate::model::Model::units`].
    pub unit: usize,
    /// Span of the result expression.
    pub span: sysmlv2_syntax::span::Span,
    /// Declared name of the owning element, if any.
    pub name: Option<String>,
    /// Metaclass of the owning element (e.g. `AssertConstraintUsage`).
    pub element_type: &'static str,
    /// Whether the constraint is asserted to hold (assert usages and KerML
    /// invariants; `assert not` / `inv false` invert the expected value).
    pub asserted: bool,
    pub verdict: ConstraintVerdict,
    /// Feature bindings of the result expression — the "why" behind a
    /// non-satisfied verdict. Empty for satisfied constraints (nothing
    /// to explain).
    pub bindings: Vec<ConstraintBinding>,
    /// For verdicts produced by a satisfaction claim: the qualified name
    /// of the satisfied requirement the constraint was evaluated under
    /// (subjects bound to the satisfaction target). `None` for ordinary
    /// constraint verdicts.
    pub context: Option<String>,
}

/// Evaluate every constraint/requirement/invariant body with its own
/// trailing result expression to a verdict (library units skipped).
/// Inherited bodies (`assert constraint c : Def;` where only `Def` carries
/// the expression) are not yet checked — a featuring-context increment.
pub fn check_constraints(model: &crate::model::Model) -> Vec<ConstraintCheck> {
    let mut r = crate::json::ResolvedModel::build(model);
    let mut out = constraint_checks(model, &mut r);
    out.extend(satisfaction_checks(model, &mut r));
    out
}

/// The ordinary verdicts of [`check_constraints`] — every user constraint,
/// requirement and invariant body, unbound — over an already resolved
/// model. Satisfaction claims are [`satisfaction_claims`].
pub fn constraint_checks(
    model: &crate::model::Model,
    r: &mut crate::json::ResolvedModel,
) -> Vec<ConstraintCheck> {
    let mut out = Vec::new();
    for c in r.constraints_where(|unit| !model.is_library_unit(unit)) {
        let verdict = constraint_verdict(r, &c);
        let bindings = match verdict {
            ConstraintVerdict::Satisfied => Vec::new(),
            _ => constraint_bindings(r, &c),
        };
        out.push(ConstraintCheck {
            unit: c.unit,
            span: c.span,
            name: c.name,
            element_type: c.element_type,
            asserted: c.asserted,
            verdict,
            bindings,
            context: None,
        });
    }
    out
}

/// Satisfaction claims (`satisfy R by x;`) expanded to bound constraint
/// verdicts: every constraint reachable through the satisfied
/// requirement's composition evaluates with the requirement's subjects
/// bound to the satisfaction target (see
/// [`crate::json::ResolvedModel::satisfactions`]). The same constraints
/// may also carry ordinary (unbound, usually undecided) verdicts from
/// [`check_constraints`]'s main pass — the `context` field tells the two
/// apart.
pub fn satisfaction_checks(
    model: &crate::model::Model,
    r: &mut crate::json::ResolvedModel,
) -> Vec<ConstraintCheck> {
    let mut out = Vec::new();
    for s in r.satisfactions() {
        for c in &s.constraints {
            if model.is_library_unit(c.unit) {
                continue;
            }
            out.push(ConstraintCheck {
                unit: c.unit,
                span: c.span,
                name: c.name.clone(),
                element_type: c.element_type,
                asserted: true,
                verdict: bound_verdict(r, c, &s.overrides),
                bindings: Vec::new(),
                context: s.context.clone(),
            });
        }
    }
    out
}

/// The verdict of `c` with a satisfaction claim's subject binding seeded.
fn bound_verdict(
    r: &mut crate::json::ResolvedModel,
    c: &crate::json::ConstraintInfo,
    overrides: &std::collections::HashMap<usize, crate::eval::Value>,
) -> ConstraintVerdict {
    match r.evaluate_in_with(c.scope, &c.expr, overrides) {
        Ok(crate::eval::Value::Boolean(b)) => {
            if b != c.negated {
                ConstraintVerdict::Satisfied
            } else {
                ConstraintVerdict::Violated
            }
        }
        Ok(crate::eval::Value::Indeterminate) => ConstraintVerdict::Undecided(
            "result is indeterminate over unbound features".to_string(),
        ),
        Ok(other) => ConstraintVerdict::Undecided(format!("result is not a boolean: {other}")),
        Err(e) => ConstraintVerdict::Undecided(e.to_string()),
    }
}

/// One satisfaction claim (`satisfy R by x;`) checked as a whole: `R`'s
/// constraints evaluate with its subjects bound to `x`, and their verdicts
/// combine the way a requirement check does. Each check's assumptions
/// imply its required constraints and the requirements it composes, in
/// three-valued logic: a claim is undecided only when what is known does
/// not settle it.
#[derive(Clone, Debug)]
pub struct SatisfactionClaim {
    /// Index into [`crate::model::Model::units`] of the `satisfy`
    /// statement.
    pub unit: usize,
    /// Source extent of the `satisfy` statement, keyword through its `;`
    /// or body.
    pub span: sysmlv2_syntax::span::Span,
    /// Qualified name of the satisfied requirement, as
    /// [`ConstraintCheck::context`] carries it.
    pub requirement: Option<String>,
    /// The satisfying feature as written after `by`.
    pub by: String,
    /// `not satisfy R by x;`: the verdict is on `x` *not* satisfying `R`.
    pub negated: bool,
    /// The claim's verdict.
    pub verdict: ConstraintVerdict,
    /// Satisfied only because an assumption does not hold.
    pub vacuous: bool,
    /// The verdicts the claim combines, in source order, each under the
    /// subject binding and, unless satisfied, with the feature values
    /// behind it.
    pub constraints: Vec<ClaimConstraint>,
}

/// One constraint verdict a [`SatisfactionClaim`] combines.
#[derive(Clone, Debug)]
pub struct ClaimConstraint {
    /// The constraint's own verdict under the subject binding, its
    /// `context` naming the satisfied requirement.
    pub check: ConstraintCheck,
    /// An `assume` constraint: when it fails, its check holds vacuously.
    pub assumed: bool,
}

/// Every satisfaction claim of the user units, checked as a whole (see
/// [`SatisfactionClaim`]), in model order.
pub fn satisfaction_claims(
    model: &crate::model::Model,
    r: &mut crate::json::ResolvedModel,
) -> Vec<SatisfactionClaim> {
    use crate::json::SatisfactionRole;
    let mut out = Vec::new();
    for s in r.satisfactions() {
        if model.is_library_unit(s.unit) {
            continue;
        }
        let mut constraints = Vec::with_capacity(s.constraints.len());
        for (i, c) in s.constraints.iter().enumerate() {
            let verdict = bound_verdict(r, c, &s.overrides);
            let bindings = match verdict {
                ConstraintVerdict::Satisfied => Vec::new(),
                _ => feature_bindings(r, c, Some(&s.overrides)),
            };
            let assumed = s
                .nodes
                .iter()
                .flat_map(|n| &n.constraints)
                .any(|&(j, role)| j == i && role == SatisfactionRole::Assumed);
            constraints.push(ClaimConstraint {
                check: ConstraintCheck {
                    unit: c.unit,
                    span: c.span,
                    name: c.name.clone(),
                    element_type: c.element_type,
                    asserted: true,
                    verdict,
                    bindings,
                    context: s.context.clone(),
                },
                assumed,
            });
        }
        let (verdict, vacuous) = claim_verdict(&s.nodes, &constraints, s.negated);
        out.push(SatisfactionClaim {
            unit: s.unit,
            span: s.span,
            requirement: s.context,
            by: s.by,
            negated: s.negated,
            verdict,
            vacuous,
            constraints,
        });
    }
    out
}

/// A claim's verdict from its constraints' (see [`SatisfactionClaim`]), and
/// whether it holds only because an assumption fails. A requirement with
/// nothing to evaluate leaves its claim undecided rather than vacuously
/// satisfied.
fn claim_verdict(
    nodes: &[crate::json::SatisfactionNode],
    constraints: &[ClaimConstraint],
    negated: bool,
) -> (ConstraintVerdict, bool) {
    if constraints.is_empty() || nodes.is_empty() {
        return (
            ConstraintVerdict::Undecided("the requirement has no constraint to evaluate".into()),
            false,
        );
    }
    let (truth, vacuous) = check_truth(nodes, 0, constraints, 0);
    match truth.map(|t| t != negated) {
        Some(true) => (ConstraintVerdict::Satisfied, vacuous && !negated),
        Some(false) => (ConstraintVerdict::Violated, false),
        None => {
            let why = constraints
                .iter()
                .find_map(|c| match &c.check.verdict {
                    ConstraintVerdict::Undecided(why) => Some(why.clone()),
                    _ => None,
                })
                .unwrap_or_else(|| "a constraint is undecided".into());
            (ConstraintVerdict::Undecided(why), false)
        }
    }
}

/// The three-valued truth of the check `at` — `None` when unknown — and
/// whether it holds only because an assumption fails.
fn check_truth(
    nodes: &[crate::json::SatisfactionNode],
    at: usize,
    constraints: &[ClaimConstraint],
    depth: usize,
) -> (Option<bool>, bool) {
    use crate::json::SatisfactionRole;
    // Kleene conjunction: one false part decides, otherwise any unknown
    // part leaves the whole unknown.
    fn and(a: Option<bool>, b: Option<bool>) -> Option<bool> {
        match (a, b) {
            (Some(false), _) | (_, Some(false)) => Some(false),
            (Some(true), Some(true)) => Some(true),
            _ => None,
        }
    }
    // The walk builds a tree; the bound only guards a malformed one.
    if depth > nodes.len() {
        return (None, false);
    }
    let (mut assumed, mut required) = (Some(true), Some(true));
    let mut fold = |role: SatisfactionRole, truth: Option<bool>| match role {
        SatisfactionRole::Assumed => assumed = and(assumed, truth),
        SatisfactionRole::Required => required = and(required, truth),
    };
    for &(i, role) in &nodes[at].constraints {
        let truth = match constraints[i].check.verdict {
            ConstraintVerdict::Satisfied => Some(true),
            ConstraintVerdict::Violated => Some(false),
            ConstraintVerdict::Undecided(_) => None,
        };
        fold(role, truth);
    }
    for &(child, role) in &nodes[at].children {
        fold(role, check_truth(nodes, child, constraints, depth + 1).0);
    }
    // The assumptions imply the required parts.
    match (assumed, required) {
        (Some(false), required) => (Some(true), required != Some(true)),
        (_, Some(true)) => (Some(true), false),
        (Some(true), Some(false)) => (Some(false), false),
        _ => (None, false),
    }
}

/// Evaluate one enumerated constraint to its verdict (shared by
/// [`check_constraints`] and the `sysmlv2-solve` crate, which solves the
/// undecided ones).
pub fn constraint_verdict(
    r: &mut crate::json::ResolvedModel,
    c: &crate::json::ConstraintInfo,
) -> ConstraintVerdict {
    match r.evaluate_in(c.scope, &c.expr) {
        Ok(crate::eval::Value::Boolean(b)) => {
            if b != c.negated {
                ConstraintVerdict::Satisfied
            } else {
                ConstraintVerdict::Violated
            }
        }
        Ok(crate::eval::Value::Indeterminate) => ConstraintVerdict::Undecided(
            "result is indeterminate over unbound features".to_string(),
        ),
        Ok(other) => ConstraintVerdict::Undecided(format!("result is not a boolean: {other}")),
        Err(e) => ConstraintVerdict::Undecided(e.to_string()),
    }
}

#[cfg(test)]
mod tests {
    use crate::{json::ResolvedModel, model::Model};

    const LIBRARY: &str = "package L {
        class A;
        class B :> A;
        feature n : A [1..2] = 1;
        feature m : B [0..1] :> n;
        function f { in x : A; return x; }
    }";
    const USER: &str = "package U {
        feature a : L::A [2..1];
        feature b :> L::n = 2;
    }";

    fn findings(model: &Model) -> Vec<(usize, String)> {
        let mut r = ResolvedModel::build(model);
        let before = crate::layered::copied_rows();
        let out = super::validate_semantics_with(&mut r, model);
        assert_eq!(
            crate::layered::copied_rows(),
            before,
            "a semantic pass must not copy any builder table"
        );
        out.into_iter().map(|(u, d)| (u, d.message)).collect()
    }

    #[test]
    fn semantic_checks_walk_tables_without_copying_them() {
        // Fresh build: library rows and user rows share one storage.
        let mut cold = Model::new();
        cold.add_library_source("lib.kerml", LIBRARY);
        cold.add_source("user.kerml", USER);
        let cold_findings = findings(&cold);
        assert!(
            cold_findings
                .iter()
                .any(|(_, m)| m.contains("lower bound 2 exceeds upper bound 1")),
            "{cold_findings:?}"
        );
        // Prepared build: the library rows are a shared prefix.
        let mut base = Model::new();
        base.add_library_source("lib.kerml", LIBRARY);
        let prepared = base.prepare_library().unwrap();
        let mut warm = Model::new();
        prepared.install(&mut warm).unwrap();
        warm.add_source("user.kerml", USER);
        assert!(ResolvedModel::build(&warm).b.library_facts.is_some());
        assert_eq!(findings(&warm), cold_findings);
    }

    /// The validators pass over the elements below the library boundary
    /// without locating their units: every explicit element below it
    /// belongs to a library unit and every later one to a user unit, in a
    /// build that lowers the library with the model — whatever order the
    /// units were added in — and in a build on a prepared library.
    #[test]
    fn library_units_own_exactly_the_elements_below_the_boundary() {
        const MORE: &str = "package W { feature c :> L::m; class D :> L::B; }";
        let mut cold = Model::new();
        cold.add_source("user.kerml", USER);
        cold.add_library_source("lib.kerml", LIBRARY);
        cold.add_source("more.kerml", MORE);
        let mut base = Model::new();
        base.add_library_source("lib.kerml", LIBRARY);
        let prepared = base.prepare_library().unwrap();
        let mut warm = Model::new();
        prepared.install(&mut warm).unwrap();
        warm.add_source("user.kerml", USER);
        warm.add_source("more.kerml", MORE);
        for (label, model) in [("cold", &cold), ("warm", &warm)] {
            let r = ResolvedModel::build(model);
            assert!(r.b.lib_boundary > 0, "{label}");
            assert!(r.b.explicit_len() > r.b.lib_boundary, "{label}");
            for e in 0..r.b.explicit_len() {
                assert_eq!(
                    e < r.b.lib_boundary,
                    model.is_library_unit(r.b.unit_of_elem(e)),
                    "{label}: element {e} of {}",
                    r.b.explicit_len()
                );
            }
        }
        // The two number their units differently; the findings agree.
        let messages = |model: &Model| -> Vec<String> {
            findings(model).into_iter().map(|(_, m)| m).collect()
        };
        assert_eq!(messages(&warm), messages(&cold));
        assert!(!messages(&cold).is_empty());
    }

    /// Reporting spans cost at most one ownership step per element,
    /// however deep the ownership nests. Measured in steps rather than in
    /// wall-clock time: the count is the work the walk does, and does not
    /// depend on the machine.
    ///
    /// An operator chain lowers four ownership levels per operator, so the
    /// longest chain the parser admits nests its first operand over four
    /// thousand levels deep. Walking up from each element separately took
    /// over seventy million steps over its seventeen thousand elements.
    #[test]
    fn span_resolution_is_linear_in_the_ownership_depth() {
        // Lowering the chain recurses once per operator, so the probe runs
        // on a thread with room for it; the count is kept per thread, so
        // the checks run there too.
        std::thread::Builder::new()
            .stack_size(64 << 20)
            .spawn(|| {
                let terms = sysmlv2_syntax::parser::MAX_EXPR_OPERATORS as usize;
                let chain = (0..terms)
                    .map(|i| format!("a{i} > 0"))
                    .collect::<Vec<_>>()
                    .join(" and ");
                let mut model = Model::new();
                model.add_source(
                    "chain.sysml",
                    &format!("package P {{ part x {{ attribute v = {chain}; }} }}"),
                );
                assert!(!model.has_errors());
                let mut r = ResolvedModel::build(&model);
                let elements = r.b.explicit_len();
                let before = super::facts::span_steps();
                super::validate_semantics_with(&mut r, &model);
                let steps = super::facts::span_steps() - before;
                assert!(
                    steps <= elements,
                    "{steps} ownership steps resolving spans over {elements} elements"
                );
            })
            .unwrap()
            .join()
            .unwrap();
    }
}
