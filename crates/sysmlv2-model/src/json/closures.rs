//! The closures and the inheritance-aware switch (plan §33h): the four
//! closure names — `inheritedMembership`, `inheritedFeature`,
//! `importedMembership`, `featuringType` — over the resolver's own
//! inheritance and import walks, and the *closure policy* under which the
//! inheritance-aware families (`feature`, `featureMembership`,
//! `membership`, `member` and everything defined over them) switch from
//! the passthrough level — the owned side — to their specification
//! definition, which unions the inherited and imported memberships.
//!
//! The read API answers the closure names whatever the policy: a consumer
//! asking for `inheritedMembership` wants the walk. The policy governs the
//! *families* (so that `feature` on a part lists what it inherits) and,
//! in the full-form emitter, whether the closure names are written at all
//! — the payload grows with the closures materialized per element, which
//! is why the passthrough level exists (INTEROP.md).
//!
//! The walk stops at a fixed heritage depth ([`super::MAX_RESOLUTION_DEPTH`])
//! and reports it ([`ResolvedModel::closure_truncated`]) rather than
//! presenting a cut enumeration as the closure; the emitter refuses to
//! write one.

use super::{ElementRef, InheritedBindings, LookupAccess, ResolvedModel};
use crate::metaclass::conforms;
use std::collections::HashSet;

/// How the inheritance-aware families are answered.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Default)]
pub enum ClosurePolicy {
    /// The owned side only — the passthrough level, the default.
    #[default]
    Passthrough,
    /// The specification's definition over the inheritance and import
    /// closures; `include_implied` extends the heritage over the implied
    /// library bases (every part inherits `Parts::Part`'s members).
    Closure { include_implied: bool },
}

impl ClosurePolicy {
    /// Whether the closures are in force, and with the implied heritage.
    pub fn include_implied(self) -> Option<bool> {
        match self {
            Self::Passthrough => None,
            Self::Closure { include_implied } => Some(include_implied),
        }
    }
}

/// The four closure names: answered by the walks, written by the emitter
/// only under the closure policy.
pub const CLOSURE_NAMES: &[&str] = &[
    "featuringType",
    "importedMembership",
    "inheritedFeature",
    "inheritedMembership",
];

impl ResolvedModel {
    /// The closure policy in force for [`Self::derived`].
    pub fn closure_policy(&self) -> ClosurePolicy {
        self.closure_policy
    }

    /// Set the closure policy for [`Self::derived`]: under
    /// [`ClosurePolicy::Closure`] the inheritance-aware families answer
    /// their specification definition over the inherited and imported
    /// memberships (with or without the implied library heritage); under
    /// [`ClosurePolicy::Passthrough`] the owned side only. The four closure
    /// names are answered either way (with the policy's implied flag, or
    /// without the implied heritage under passthrough).
    pub fn set_closure_policy(&mut self, policy: ClosurePolicy) {
        self.closure_policy = policy;
    }

    fn include_implied(&self) -> bool {
        self.closure_policy.include_implied().unwrap_or(false)
    }

    /// Whether the inheritance or import walk behind the closures of `e`
    /// hit the resolver's depth budget, so a closure of `e` would be
    /// incomplete. A closure the emitter is asked to write for such an
    /// element is refused, not truncated.
    pub fn closure_truncated(&mut self, e: ElementRef) -> bool {
        let include_implied = self.include_implied();
        if self.inheritance_walk_truncated(e, include_implied) {
            return true;
        }
        let Some(&s) = self.b.elem_scope.get(&e.0) else {
            return false;
        };
        if let Some(&t) = self.import_truncated.get(&(s, include_implied)) {
            return t;
        }
        let mut out = InheritedBindings::default();
        self.b
            .imported_bindings(s, include_implied, LookupAccess::All, &mut out);
        self.import_truncated
            .insert((s, include_implied), out.truncated);
        out.truncated
    }

    // ---- the closure names ----

    /// `Type::inheritedMembership`: the Membership relationships `e`
    /// inherits, per the resolver's walk ([`Self::inherited_memberships`]).
    pub(super) fn d_inherited_memberships(&mut self, e: ElementRef) -> Vec<ElementRef> {
        let include_implied = self.include_implied();
        self.inherited_memberships(e, include_implied)
    }

    /// `Type::inheritedFeature = inheritedMembership->selectByKind(FeatureMembership).memberFeature`
    /// — selected by the *membership* kind (a package-owned feature
    /// arriving through an imported membership is not one), unlike the
    /// navigation accessor [`Self::inherited_features`].
    pub(super) fn d_inherited_features(&mut self, e: ElementRef) -> Vec<ElementRef> {
        self.d_inherited_memberships(e)
            .into_iter()
            .filter(|&m| conforms(self.b.elements[m.0].ty, "FeatureMembership"))
            .filter_map(|m| self.d_owned_member_element(m))
            .collect()
    }

    /// `Namespace::importedMembership = ownedImport.importedMemberships(…)`:
    /// the Memberships the namespace's imports bring in — every owned
    /// import, whatever its visibility (a private import imports for its
    /// owner; it is the *re-export* through heritage that private
    /// excludes) — each imported member's owning membership, and the
    /// imported alias memberships, admitted by the imports' filter
    /// conditions, in discovery order (per import, declaration order).
    /// Two deviations from the normative operation: a `import Q::alias;`
    /// contributes the aliased element's owning membership rather than
    /// the alias Membership itself, and a mutual public-import cycle
    /// lists a namespace's own memberships under its imports (the
    /// operation's `excluded->including(self)` seed), which `membership`
    /// deduplicates.
    pub fn imported_memberships(&mut self, e: ElementRef) -> Vec<ElementRef> {
        let Some(&s) = self.b.elem_scope.get(&e.0) else {
            return Vec::new();
        };
        let include_implied = self.include_implied();
        let mut bindings = InheritedBindings::default();
        self.b
            .imported_bindings(s, include_implied, LookupAccess::All, &mut bindings);
        let mut out: Vec<ElementRef> = Vec::new();
        let mut seen: HashSet<usize> = HashSet::new();
        for &(elem, _) in &bindings.members {
            if let Some(r) = self.b.elements[elem].owning_relationship {
                if seen.insert(r) {
                    out.push(ElementRef(r));
                }
            }
        }
        for &r in &bindings.alias_rels {
            if seen.insert(r) {
                out.push(ElementRef(r));
            }
        }
        out
    }

    // ---- the inheritance-aware bases ----

    /// `Type::feature = featureMembership.ownedMemberFeature` under the
    /// policy: the owned features, then the inherited feature
    /// memberships' features (shadowing applied on the membership side);
    /// the owned features alone at the passthrough level.
    pub(super) fn d_features(&mut self, e: ElementRef) -> Vec<ElementRef> {
        if self.closure_policy == ClosurePolicy::Passthrough {
            return self.d_owned_features(e);
        }
        let mut out: Vec<ElementRef> = Vec::new();
        for m in self.d_feature_memberships(e) {
            if let Some(f) = self.d_owned_member_element(m) {
                if !out.contains(&f) {
                    out.push(f);
                }
            }
        }
        out
    }

    /// `Type::featureMembership` under the policy: the owned feature
    /// memberships, then the inherited memberships that are
    /// FeatureMemberships.
    pub(super) fn d_feature_memberships(&mut self, e: ElementRef) -> Vec<ElementRef> {
        let mut out = self.d_owned_feature_memberships(e);
        if self.closure_policy != ClosurePolicy::Passthrough {
            let inherited = self.d_inherited_memberships(e);
            for m in inherited {
                if conforms(self.b.elements[m.0].ty, "FeatureMembership") && !out.contains(&m) {
                    out.push(m);
                }
            }
        }
        out
    }

    /// `Namespace::membership = ownedMembership ∪ importedMembership`, and
    /// `Type::membership` adds `inheritedMembership`, under the policy;
    /// the owned memberships alone at the passthrough level.
    pub(super) fn d_memberships(&mut self, e: ElementRef) -> Vec<ElementRef> {
        let mut out = self.d_owned_memberships(e);
        if self.closure_policy != ClosurePolicy::Passthrough {
            let mut extra = self.imported_memberships(e);
            if self.is_kind(e, "Type") {
                extra.extend(self.d_inherited_memberships(e));
            }
            for m in extra {
                if !out.contains(&m) {
                    out.push(m);
                }
            }
        }
        out
    }
}
