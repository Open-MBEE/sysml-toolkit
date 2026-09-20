//! Requirement, case and view structure over the resolved model: the
//! subject, actor, stakeholder and objective parameters, the required and
//! assumed constraints, framed concerns, verified and satisfied
//! requirements, view renderings, conditions and exposed elements. Each
//! function documents the specification rule it implements; the dispatch
//! is in `derived.rs`. Most of these read `featureMembership`, whose
//! specification unions the inherited memberships, and are answered at
//! the passthrough level (the owned side) until the closure policy is on;
//! `requiredConstraint`/`assumedConstraint` read `ownedFeatureMembership`
//! and are exact.

use super::derived::Reference;
use super::{ElementRef, ResolvedModel};

impl ResolvedModel {
    /// The owned members of the feature memberships of `kind`, in order
    /// (`featureMembership->selectByKind(Kind).ownedMemberX`) — the owned
    /// memberships at the passthrough level, the inherited ones too under
    /// the closure policy.
    pub(super) fn d_members_via(&mut self, e: ElementRef, kind: &str) -> Vec<ElementRef> {
        self.d_feature_memberships(e)
            .into_iter()
            .filter(|&m| self.is_kind(m, kind))
            .filter_map(|m| self.d_owned_member_element(m))
            .collect()
    }

    /// `requiredConstraint` / `assumedConstraint`:
    /// `ownedFeatureMembership->selectByKind(RequirementConstraintMembership)->select(kind = K).ownedConstraint`.
    pub(super) fn d_requirement_constraints(&self, e: ElementRef, kind: &str) -> Vec<ElementRef> {
        self.owned_relationships_of_kind(e, "RequirementConstraintMembership")
            .into_iter()
            .filter(|&m| self.prop_str(m.0, "kind") == Some(kind))
            .filter_map(|m| self.d_owned_member_element(m))
            .collect()
    }

    /// `RequirementConstraintMembership::referencedConstraint` (and its
    /// narrowings `referencedConcern`, `verifiedRequirement`,
    /// `ViewRenderingMembership::referencedRendering`): the owned member's
    /// `referencedFeatureTarget()`, else the owned member itself, cast to
    /// `kind`.
    pub(super) fn d_referenced_member(&mut self, m: ElementRef, kind: &str) -> Option<Reference> {
        let owned = self.d_owned_member_element(m)?;
        self.d_referenced_or_self(owned, kind)
    }

    /// `VerificationCaseUsage::verifiedRequirement` (and on the
    /// definition): the verified requirements of the objective
    /// requirement's RequirementVerificationMemberships.
    pub(super) fn d_verified_requirements(&mut self, e: ElementRef) -> Vec<Reference> {
        let Some(objective) = self
            .d_members_via(e, "ObjectiveMembership")
            .into_iter()
            .next()
        else {
            return Vec::new();
        };
        let memberships: Vec<ElementRef> = self
            .d_feature_memberships(objective)
            .into_iter()
            .filter(|&m| self.is_kind(m, "RequirementVerificationMembership"))
            .collect();
        // `->asOrderedSet()`: each requirement once, in first-mention order.
        let mut out: Vec<Reference> = Vec::new();
        for m in memberships {
            if let Some(r) = self.d_referenced_member(m, "RequirementUsage") {
                if !out.contains(&r) {
                    out.push(r);
                }
            }
        }
        out
    }

    /// `SatisfyRequirementUsage::satisfyingFeature`: the feature bound to
    /// the subject parameter — in the lowering the pilot and this toolkit
    /// share, the subject parameter's FeatureValue is a
    /// FeatureReferenceExpression whose referent is that feature.
    pub(super) fn d_satisfying_feature(&mut self, e: ElementRef) -> Option<Reference> {
        let subject = self
            .d_members_via(e, "SubjectMembership")
            .into_iter()
            .next()?;
        let value = self
            .owned_relationships_of_kind(subject, "FeatureValue")
            .into_iter()
            .next()
            .and_then(|fv| self.d_owned_member_element(fv))?;
        if !self.is_kind(value, "FeatureReferenceExpression") {
            return None;
        }
        let referent = self.d_referent(value)?;
        Some(match referent {
            Reference::Element(f) => self.d_feature_target(f),
            outside => outside,
        })
    }

    /// `ViewUsage::viewRendering` (and on the definition): the referenced
    /// rendering of the first ViewRenderingMembership.
    pub(super) fn d_view_rendering(&mut self, e: ElementRef) -> Option<Reference> {
        let m = self
            .d_feature_memberships(e)
            .into_iter()
            .find(|&m| self.is_kind(m, "ViewRenderingMembership"))?;
        self.d_referenced_member(m, "RenderingUsage")
    }

    /// `satisfiedViewpoint = ownedRequirement->selectByKind(ViewpointUsage)->select(isComposite)`.
    pub(super) fn d_satisfied_viewpoints(&self, e: ElementRef) -> Vec<ElementRef> {
        self.d_owned_features(e)
            .into_iter()
            .filter(|&f| self.is_kind(f, "ViewpointUsage") && self.prop_bool(f.0, "isComposite"))
            .collect()
    }

    /// `viewpointStakeholder = framedConcern.featureMembership->selectByKind(StakeholderMembership).ownedStakeholderParameter`.
    pub(super) fn d_viewpoint_stakeholders(&mut self, e: ElementRef) -> Vec<ElementRef> {
        let concerns = self.d_members_via(e, "FramedConcernMembership");
        concerns
            .into_iter()
            .flat_map(|c| self.d_members_via(c, "StakeholderMembership"))
            .collect()
    }

    /// `ViewUsage::exposedElement`: the members visible through the
    /// view's expose imports that its conditions admit
    /// ([`Self::view_exposed_elements`], in discovery order).
    pub(super) fn d_exposed_elements(&mut self, e: ElementRef) -> Vec<ElementRef> {
        self.view_exposed_elements(e)
    }
}
