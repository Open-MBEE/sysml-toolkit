//! Qualified public views of the one checked Feature.type projection.
use super::{Incomplete, adapter::RepositoryTyping};
use crate::{
    json::{ElementRef, ResolvedModel},
    metaclass::conforms,
};

/// Why a checked type-family property is unavailable. An error is not an empty
/// collection or proof of absence. This set may grow as coverage is expanded.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub enum FeatureTypeIssue {
    WorkLimit,
    DepthLimit,
    /// Missing element or a receiver that is not a Feature.
    InvalidElement,
    InvalidRelationship,
    ExternalEndpoint,
    MissingRequiredFamilies,
    UnsupportedProjection,
    AmbiguousSpecialization,
    InvalidFunctionMultiplicity,
    InvalidBehaviorKind,
    /// The receiver does not conform to the property's declaring metaclass.
    NotApplicable,
}
impl From<Incomplete> for FeatureTypeIssue {
    fn from(issue: Incomplete) -> Self {
        match issue {
            Incomplete::Budget => Self::WorkLimit,
            Incomplete::Depth => Self::DepthLimit,
            Incomplete::InvalidElement => Self::InvalidElement,
            Incomplete::InvalidRelationship => Self::InvalidRelationship,
            Incomplete::ExternalEndpoint => Self::ExternalEndpoint,
            Incomplete::MissingRequiredFamilies => Self::MissingRequiredFamilies,
            Incomplete::UnsupportedProjection => Self::UnsupportedProjection,
            Incomplete::AmbiguousSpecialization => Self::AmbiguousSpecialization,
            Incomplete::InvalidFunctionMultiplicity => Self::InvalidFunctionMultiplicity,
            Incomplete::InvalidBehaviorKind => Self::InvalidBehaviorKind,
        }
    }
}

/// Complete property values or explicit qualifications from one shared query.
/// Intermediate candidates are intentionally not exposed as a property value.
/// This report neither classifies model-level evaluability nor executes a call.
#[derive(Clone, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub struct FeatureTypeReport {
    /// Feature::type. Only Ok certifies the complete reduced collection.
    pub types: Result<Vec<ElementRef>, FeatureTypeIssue>,
    /// Step::behavior; NotApplicable on a Feature that is not a Step.
    pub behavior: Result<Vec<ElementRef>, FeatureTypeIssue>,
    /// Expression::function; NotApplicable outside Expression. Ok(None) proves
    /// no Function in the complete type collection; Err never means absence.
    pub function: Result<Option<ElementRef>, FeatureTypeIssue>,
    /// Bounded logical work, including cold projection construction when needed.
    pub steps: usize,
}
impl FeatureTypeReport {
    fn unavailable(issue: FeatureTypeIssue, step: bool, expression: bool, steps: usize) -> Self {
        Self {
            types: Err(issue),
            behavior: Err(if step {
                issue
            } else {
                FeatureTypeIssue::NotApplicable
            }),
            function: Err(if expression {
                issue
            } else {
                FeatureTypeIssue::NotApplicable
            }),
            steps,
        }
    }
}
impl ResolvedModel {
    /// Read qualified Feature::type, Step::behavior and Expression::function
    /// from one shared identity-based projection. Legacy derived reads retain
    /// their documented compatibility behavior.
    ///
    /// Supported domains include namespace-owned Feature, Step and Expression
    /// and ordinary structural Usage/Feature members, with witnessed canonical
    /// paths including required composition bases. Nested composite occurrence,
    /// item and part usages require a complete projection of their ordinary
    /// Feature or Usage owner. Other contextual families, Invocation, Constructor
    /// and unsupported required families remain Err;
    /// an instantiated-type membership alone never proves function. Source,
    /// library and materialized identities use the same checked providers.
    /// This query does not materialize semantic rows or execute expressions.
    pub fn feature_type_report(&mut self, feature: ElementRef) -> FeatureTypeReport {
        self.feature_type_report_with_budget(feature, 0)
    }

    /// The caller's row-local budget survives cache invalidation/recomputation.
    pub(in crate::json) fn feature_type_report_with_budget(
        &mut self,
        feature: ElementRef,
        initial_steps: usize,
    ) -> FeatureTypeReport {
        let Some(element) = self.b.elements.get(feature.0) else {
            return FeatureTypeReport::unavailable(
                FeatureTypeIssue::InvalidElement,
                false,
                false,
                initial_steps,
            );
        };
        if !conforms(element.ty, "Feature") {
            return FeatureTypeReport::unavailable(
                FeatureTypeIssue::InvalidElement,
                false,
                false,
                initial_steps,
            );
        }
        let step = conforms(element.ty, "Step");
        let expression = conforms(element.ty, "Expression");
        if initial_steps > crate::eval::MAX_STEPS {
            return FeatureTypeReport::unavailable(
                FeatureTypeIssue::WorkLimit,
                step,
                expression,
                initial_steps,
            );
        }
        let mut steps = initial_steps;
        let mut evidence = match RepositoryTyping::new(&mut self.b, &mut steps) {
            Ok(evidence) => evidence,
            Err(issue) => {
                return FeatureTypeReport::unavailable(
                    if steps > crate::eval::MAX_STEPS {
                        FeatureTypeIssue::WorkLimit
                    } else {
                        issue.into()
                    },
                    step,
                    expression,
                    steps,
                );
            }
        };
        let projection = evidence.project(feature.0, &mut steps);
        steps = projection.steps;
        if steps > crate::eval::MAX_STEPS {
            return FeatureTypeReport::unavailable(
                FeatureTypeIssue::WorkLimit,
                step,
                expression,
                steps,
            );
        }
        if !projection.complete() {
            let issue = projection
                .graph_issue
                .or(projection.required_issue)
                .expect("incomplete projection has a reason");
            return FeatureTypeReport::unavailable(issue.into(), step, expression, steps);
        }
        // Charge the four bounded result traversals before allocation. The
        // projection is complete; narrowing can still reject invalid function
        // multiplicity or a Behavior that cannot redefine Function.
        steps = steps.saturating_add(projection.candidates.len().saturating_mul(4));
        if steps > crate::eval::MAX_STEPS {
            return FeatureTypeReport::unavailable(
                FeatureTypeIssue::WorkLimit,
                step,
                expression,
                steps,
            );
        }
        let behavior = if step {
            projection
                .behaviors(&evidence)
                .map(|v| v.into_iter().map(ElementRef).collect())
                .map_err(Into::into)
        } else {
            Err(FeatureTypeIssue::NotApplicable)
        };
        let function = if expression {
            projection
                .function(&evidence)
                .map(|v| v.map(ElementRef))
                .map_err(Into::into)
        } else {
            Err(FeatureTypeIssue::NotApplicable)
        };
        FeatureTypeReport {
            types: Ok(projection.candidates.into_iter().map(ElementRef).collect()),
            behavior,
            function,
            steps,
        }
    }
}
