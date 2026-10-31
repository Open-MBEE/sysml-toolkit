//! The specification's naming rule over the resolved model — KerML 8.2.3.5
//! `Element::effectiveName()` / `effectiveShortName()` and the
//! `qualifiedName` derivation — as the derivation layer answers `name`,
//! `shortName` and `qualifiedName` and as the public name accessors
//! ([`ResolvedModel::element_effective_name`],
//! [`ResolvedModel::element_short_name`],
//! [`ResolvedModel::element_qualified_name`]) read them.
//!
//! A Feature with neither a declared name nor a declared short name takes
//! both names from its *naming feature* (KerML `Feature::effectiveName()`
//! / `effectiveShortName()`: `if declaredShortName <> null or declaredName
//! <> null then declaredName else namingFeature().effectiveName()` — a
//! feature that declares either name declares both): the feature
//! it explicitly redefines, else a positional redefinition target read from
//! its owner's heritage, else — for memberships whose owned
//! feature implicitly redefines a library feature (a binary connector's
//! two ends, a flow's payload, a return parameter, a subject, an objective,
//! a view rendering, a transition's accepter, an invocation's positional
//! arguments) — the positional name the pilot implementation computes
//! from that implied redefinition, else the feature selected by a SysML
//! reference naming rule. Specialized SysML reference rules take precedence
//! over redefinition. Anonymous feature chains do not confer names. The
//! naming feature's name is
//! itself effective, so a chain of unnamed redefinitions resolves to the
//! first named ancestor. A naming feature outside the model (a library
//! feature when no library is loaded) is named through
//! [`ResolvedModel::set_library_names`] when the caller supplied a
//! library name table; otherwise the element stays unnamed, as it does
//! on the wire.
//!
//! The full form projects this layer's values and keeps its own
//! `effective_name_of` / `implied_member_name` / `qname_of` (in `full.rs`)
//! as the fallback for an element the projection cannot find. Both read
//! the positional names from one place: [`membership_implied_name`] for
//! the role memberships and [`crate::json::binary_end_names`] for the two
//! ends of a binary connector.

use super::{ElementRef, ResolvedModel};
use crate::metaclass::conforms;
use crate::metaclass::is_a;
use crate::properties::Atom;

/// SysML reference forms whose naming rule uses the referenced feature's
/// `featureTarget`. This does not give the anonymous chain itself a name.
pub(crate) fn reference_names_feature_target(ty: &str, membership: Option<&str>) -> bool {
    conforms(ty, "PerformActionUsage")
        || (conforms(ty, "ConstraintUsage")
            && membership == Some("RequirementConstraintMembership"))
}

/// Reference-based SysML naming takes precedence over the generic
/// redefinition rule. Variants name through the reference itself.
pub(crate) fn reference_names_feature(ty: &str, membership: Option<&str>) -> bool {
    reference_names_feature_target(ty, membership) || membership == Some("VariantMembership")
}

/// The positional name a membership kind gives the feature it owns: the
/// library feature that feature implicitly redefines — a subject `subj`,
/// an objective `obj`, a return parameter `result`, a view rendering
/// `viewRendering`.
pub(crate) fn membership_implied_name(membership: &str) -> Option<&'static str> {
    match membership {
        "SubjectMembership" => Some("subj"),
        "ObjectiveMembership" => Some("obj"),
        "ReturnParameterMembership" => Some("result"),
        "ViewRenderingMembership" => Some("viewRendering"),
        _ => None,
    }
}

/// [`membership_implied_name`] with the membership's `kind`: a state's
/// entry, do and exit actions (`StateSubactionMembership`) redefine the
/// state action's `entryAction`, `doAction` and `exitAction`, which name
/// an unnamed one (`entry;` is findable as `entryAction`).
pub(crate) fn membership_implied_name_of(
    membership: &str,
    kind: Option<&str>,
) -> Option<&'static str> {
    if membership == "StateSubactionMembership" {
        return match kind {
            Some("entry") => Some("entryAction"),
            Some("do") => Some("doAction"),
            Some("exit") => Some("exitAction"),
            _ => None,
        };
    }
    membership_implied_name(membership)
}

impl super::Builder {
    /// The positional name an unnamed role member is findable by in its
    /// owner (`subject : V;` is `subj`), when lowering registered `e` under
    /// one: a feature that declares no name, redefines nothing explicitly
    /// (a written `:>>` names it instead) and is owned through a membership
    /// with an implied name ([`membership_implied_name`]). Read back from
    /// the owner's scope, so it answers exactly what lookup finds.
    pub(super) fn implied_role_name(&self, e: usize) -> Option<&'static str> {
        let element = &self.elements[e];
        let membership = &self.elements[element.owning_relationship?];
        let name = membership_implied_name_of(
            membership.ty,
            membership.props.get("kind").and_then(|v| v.as_str()),
        )?;
        if self.effective_name(e).is_some()
            || element
                .owned_relationships
                .iter()
                .any(|&r| self.elements[r].ty == "Redefinition")
        {
            return None;
        }
        let scope = self.owner_scope_of(e)?;
        self.scopes[scope]
            .effective_names
            .get(name)?
            .iter()
            .any(|b| b.elem == e)
            .then_some(name)
    }

    /// A generic reference spelling is retained as a replay locator, but it
    /// contributes no semantic name to a recursive namespace import. Keep
    /// specialized reference naming, explicit redefinitions and positional
    /// members out of this bounded absence proof.
    pub(super) fn reference_locator_has_no_semantic_name(&self, e: usize) -> bool {
        let element = &self.elements[e];
        let membership = element.owning_relationship.map(|r| self.elements[r].ty);
        self.effective_name(e).is_none()
            && self.effective_hint.contains_key(&e)
            && !reference_names_feature(element.ty, membership)
            && !matches!(
                membership,
                Some(
                    "ParameterMembership"
                        | "EndFeatureMembership"
                        | "ReturnParameterMembership"
                        | "SubjectMembership"
                        | "ObjectiveMembership"
                        | "ViewRenderingMembership"
                        | "TransitionFeatureMembership"
                )
            )
            && !element
                .owned_relationships
                .iter()
                .any(|&r| self.elements[r].ty == "Redefinition")
    }
}

/// The feature that names an unnamed one, once found.
enum Naming {
    /// A feature of the model.
    Feature(usize),
    /// A feature outside the model, by id, already named through the
    /// library name table.
    Named(uuid::Uuid, String),
    /// A positional name the pilot computes from an implied redefinition.
    Positional(String),
}

/// What looking for an unnamed feature's naming feature found.
enum NamingStep {
    /// No naming feature: the feature's names are null.
    Absent,
    /// A naming feature there is no way to identify or to name — an
    /// unresolved redefinition target, or an element outside the model
    /// that no library name table names.
    Unknown,
    Found(Naming),
}

/// A memoized effective name or short name, and whether its derivation
/// was certain. The plain accessors answer `None` either way, as the
/// `name` and `shortName` derivations always have; the checked operation
/// bodies answer only a certain derivation.
#[derive(Clone, Debug)]
pub(super) struct NameMemo {
    pub(super) value: Option<String>,
    pub(super) certain: bool,
}

impl NameMemo {
    fn certain(value: Option<String>) -> Self {
        Self {
            value,
            certain: true,
        }
    }
    fn unknown() -> Self {
        Self {
            value: None,
            certain: false,
        }
    }
}

impl ResolvedModel {
    /// `Element::effectiveName()` for the element at `e`, memoized.
    pub(super) fn effective_name_of(&mut self, e: usize) -> Option<String> {
        self.effective_name_memo(e).value
    }

    /// `Element::effectiveName()` for the element at `e` as a checked
    /// answer: `None` when the derivation met a naming feature it could
    /// not identify or name ([`NamingStep::Unknown`]), else the name,
    /// null included.
    pub(super) fn checked_effective_name_of(&mut self, e: usize) -> Option<Option<String>> {
        let memo = self.effective_name_memo(e);
        memo.certain.then_some(memo.value)
    }

    /// `Element::effectiveShortName()` for the element at `e`: the
    /// declared short name when the element declares either name, else
    /// the naming feature's effective short name (an implied positional
    /// name carries none). Memoized.
    pub(super) fn effective_short_name_of(&mut self, e: usize) -> Option<String> {
        self.effective_short_name_memo(e).value
    }

    /// `Element::effectiveShortName()` as a checked answer, as
    /// [`Self::checked_effective_name_of`] is for the name.
    pub(super) fn checked_effective_short_name_of(&mut self, e: usize) -> Option<Option<String>> {
        let memo = self.effective_short_name_memo(e);
        memo.certain.then_some(memo.value)
    }

    fn effective_name_memo(&mut self, e: usize) -> NameMemo {
        self.ensure_name_memo();
        if let Some(memo) = &self.name_memo[e] {
            return memo.clone();
        }
        let memo = self.effective_name_walk(e, 0);
        self.name_memo[e] = Some(memo.clone());
        memo
    }

    fn effective_short_name_memo(&mut self, e: usize) -> NameMemo {
        self.ensure_name_memo();
        if let Some(memo) = &self.short_name_memo[e] {
            return memo.clone();
        }
        let memo = self.effective_short_name_walk(e, 0);
        self.short_name_memo[e] = Some(memo.clone());
        memo
    }

    fn effective_short_name_walk(&mut self, e: usize, depth: usize) -> NameMemo {
        if depth > 32 {
            return NameMemo::unknown();
        }
        if self.declares_a_name(e) {
            return NameMemo::certain(self.declared(e, "declaredShortName"));
        }
        match self.naming_feature(e) {
            NamingStep::Absent => NameMemo::certain(None),
            NamingStep::Unknown => NameMemo::unknown(),
            NamingStep::Found(Naming::Feature(t)) => self.effective_short_name_walk(t, depth + 1),
            // The name table carries names only: an external naming
            // feature's short name is unknown.
            NamingStep::Found(Naming::Named(..)) => NameMemo::unknown(),
            // The library's role features (`subj`, `obj`, `result`,
            // `viewRendering`, `payload`, `accepter`, the binary ends)
            // declare no short names; a test on the library pins that.
            NamingStep::Found(Naming::Positional(_)) => NameMemo::certain(None),
        }
    }

    /// Whether the element declares a name or a short name — either one
    /// makes both of its names the declared ones.
    fn declares_a_name(&self, e: usize) -> bool {
        let props = &self.b.elements[e].props;
        props
            .get("declaredName")
            .is_some_and(|v| v.as_str().is_some())
            || props
                .get("declaredShortName")
                .is_some_and(|v| v.as_str().is_some())
    }

    fn ensure_name_memo(&mut self) {
        self.sync_semantic_publication();
        let n = self.b.elements.len();
        if self.name_memo.len() != n {
            self.name_memo = vec![None; n];
        }
        if self.short_name_memo.len() != n {
            self.short_name_memo = vec![None; n];
        }
    }

    fn declared(&self, e: usize, key: &str) -> Option<String> {
        self.b.elements[e]
            .props
            .get(key)
            .and_then(|v| v.as_str())
            .map(str::to_string)
    }

    fn effective_name_walk(&mut self, e: usize, depth: usize) -> NameMemo {
        if depth > 32 {
            return NameMemo::unknown();
        }
        if self.declares_a_name(e) {
            return NameMemo::certain(self.declared(e, "declaredName"));
        }
        match self.naming_feature(e) {
            NamingStep::Absent => NameMemo::certain(None),
            NamingStep::Unknown => NameMemo::unknown(),
            NamingStep::Found(Naming::Feature(t)) => self.effective_name_walk(t, depth + 1),
            NamingStep::Found(Naming::Named(_, n) | Naming::Positional(n)) => {
                NameMemo::certain(Some(n))
            }
        }
    }

    /// The naming feature of an unnamed element: a specialized SysML
    /// reference rule takes precedence (a performed action names the
    /// `do refuel;` that performs it ahead of the `doAction` it redefines);
    /// otherwise the first explicitly redefined feature, the positional
    /// target from its owner's heritage, the library-role fallback, then
    /// — unless the
    /// element is an actor or stakeholder parameter, whose reference
    /// subsets the library collection and carries no name — the referenced
    /// feature selected by the applicable SysML naming rule. Redefinitions
    /// confer names; other implied library specializations do not.
    fn naming_feature(&mut self, e: usize) -> NamingStep {
        self.ensure_by_id();
        let rels: Vec<usize> = self.b.elements[e].owned_relationships.to_vec();
        let owning_ty = self.b.elements[e]
            .owning_relationship
            .map(|r| self.b.elements[r].ty);
        // Specialized SysML naming overrides Feature::namingFeature, even
        // when a written redefinition is unresolved or has another name.
        let named_reference = reference_names_feature(self.b.elements[e].ty, owning_ty)
            .then(|| {
                rels.iter()
                    .copied()
                    .find(|&r| self.b.elements[r].ty == "ReferenceSubsetting")
            })
            .flatten();
        let mut reference: Option<Atom> = None;
        for r in rels {
            if named_reference.is_some() && Some(r) != named_reference {
                continue;
            }
            match self.b.elements[r].ty {
                "Redefinition" => {
                    let Some(target) = self.b.elements[r].props.get("redefinedFeature").cloned()
                    else {
                        return NamingStep::Unknown;
                    };
                    return self.naming_step(&target);
                }
                "ReferenceSubsetting" if named_reference == Some(r) && reference.is_none() => {
                    reference = self.b.elements[r].props.get("referencedFeature").cloned();
                }
                _ => {}
            }
        }
        // Use the actual positional target before the library-role fallback.
        // A specializing requirement's subject may redefine a user subject
        // whose name (and short name) differs from the library's `subj`.
        if named_reference.is_none() {
            if let Some(target) = self.positional_redefinition_targets(ElementRef(e)).first() {
                return NamingStep::Found(Naming::Feature(target.0));
            }
        }
        if named_reference.is_none() {
            if let Some(n) = self.implied_member_name(e) {
                return NamingStep::Found(Naming::Positional(n));
            }
        }
        if matches!(owning_ty, Some("ActorMembership" | "StakeholderMembership")) {
            return NamingStep::Absent;
        }
        let Some(target) = reference else {
            return NamingStep::Absent;
        };
        let NamingStep::Found(naming) = self.naming_step(&target) else {
            return NamingStep::Unknown;
        };
        if reference_names_feature_target(self.b.elements[e].ty, owning_ty) {
            if let Naming::Feature(t) = naming {
                if let Some(last) = self.b.elements[t]
                    .owned_relationships
                    .iter()
                    .rev()
                    .find_map(|&r| {
                        (self.b.elements[r].ty == "FeatureChaining")
                            .then(|| self.b.elements[r].props.get("chainingFeature").cloned())
                            .flatten()
                    })
                {
                    return self.naming_step(&last);
                }
            }
        }
        NamingStep::Found(naming)
    }

    /// `Feature::namingFeature()` as a checked answer for the operation
    /// bodies: `None` when the naming feature cannot be identified
    /// ([`NamingStep::Unknown`]) or is a library feature known only by the
    /// positional name it confers ([`Naming::Positional`], the implied
    /// redefinition's target when the library that holds it is not loaded);
    /// else the feature, as an element of the model or an external
    /// reference, or the absence of one.
    pub(super) fn checked_naming_feature(&mut self, e: usize) -> Option<Option<super::Reference>> {
        match self.naming_feature(e) {
            NamingStep::Absent => Some(None),
            NamingStep::Unknown | NamingStep::Found(Naming::Positional(_)) => None,
            NamingStep::Found(Naming::Feature(t)) => {
                Some(Some(super::Reference::Element(ElementRef(t))))
            }
            NamingStep::Found(Naming::Named(id, _)) => Some(Some(super::Reference::External(id))),
        }
    }

    /// [`Self::naming_target`] as a step: a target that cannot be
    /// identified is an unknown naming feature, not an absent one.
    fn naming_step(&self, target: &Atom) -> NamingStep {
        match self.naming_target(target) {
            Some(naming) => NamingStep::Found(naming),
            None => NamingStep::Unknown,
        }
    }

    /// A resolved naming target: a model element (whatever its own names
    /// — a naming feature with only a short name leaves `name` null and
    /// gives `shortName`, so `qualifiedName` still forms), or an element
    /// outside the model the library name table names. An unresolved
    /// reference is no naming feature.
    fn naming_target(&self, target: &Atom) -> Option<Naming> {
        let id = target.as_reference()?;
        match self.by_id.get(&id).copied() {
            Some(t) => Some(Naming::Feature(t)),
            None => self
                .external_names
                .get(&id)
                .cloned()
                .map(|name| Naming::Named(id, name)),
        }
    }

    /// The positional name of a member that implicitly redefines a library
    /// feature (the pilot's computed redefinitions are its naming
    /// features): a flow's payload feature redefines `payload`, a
    /// transition's accept action `accepter`, a return parameter `result`,
    /// a subject `subj`, an objective `obj`, a view rendering
    /// `viewRendering` ([`membership_implied_name`]); an invocation's
    /// positional argument redefines the callee's `in` parameter at its
    /// position; the two ends of a binary connector-family element
    /// redefine the library binary ends
    /// ([`crate::json::binary_end_names`]: `source` / `target`,
    /// successions `earlierOccurrence` / `laterOccurrence`, bindings
    /// `thisThing` / `sameThing`). An element owning exactly two end
    /// memberships is binary here however its text spelled them, as the
    /// specification reads it; the emitter's lookup registration
    /// (`implied_ends`) is narrower and covers only the two ends a usage
    /// declares in its connector part. The implied Redefinition elements
    /// themselves are not materialized — only the names they would confer.
    fn implied_member_name(&mut self, e: usize) -> Option<String> {
        let t = self.b.elements[e].ty;
        let rel = self.b.elements[e].owning_relationship?;
        let rel_ty = self.b.elements[rel].ty;
        if t == "PayloadFeature" {
            return Some("payload".to_string());
        }
        if t == "AcceptActionUsage" && rel_ty == "TransitionFeatureMembership" {
            return Some("accepter".to_string());
        }
        if let Some(n) = membership_implied_name_of(
            rel_ty,
            self.b.elements[rel]
                .props
                .get("kind")
                .and_then(|v| v.as_str()),
        ) {
            return Some(n.to_string());
        }
        if rel_ty == "ParameterMembership" {
            return self.invocation_arg_name(e, rel);
        }
        if rel_ty != "EndFeatureMembership" {
            return None;
        }
        self.ensure_rel_owner();
        let owner = self.rel_owner[rel]?;
        let names = crate::json::binary_end_names_of(self.b.elements[owner].ty)?;
        let ends: Vec<usize> = self.b.elements[owner]
            .owned_relationships
            .iter()
            .copied()
            .filter(|&r| self.b.elements[r].ty == "EndFeatureMembership")
            .collect();
        if ends.len() != 2 {
            return None;
        }
        let pos = ends.iter().position(|&r| r == rel)?;
        Some(names[pos].to_string())
    }

    /// The positional name of an invocation or constructor argument: the
    /// pilot implicitly redefines the callee's input parameters (`in` and
    /// `inout`) in declaration order, so the argument at position *k* is
    /// named after the *k*-th input parameter — an unnamed one names
    /// nothing but still holds its position. An argument owning any
    /// Redefinition is a named argument and keeps that name (even
    /// unresolved). An accept action's reference parameters are its
    /// payload and receiver.
    fn invocation_arg_name(&mut self, e: usize, rel: usize) -> Option<String> {
        let has_redefinition = self.b.elements[e]
            .owned_relationships
            .iter()
            .any(|&r| self.b.elements[r].ty == "Redefinition");
        if has_redefinition {
            return None;
        }
        self.ensure_rel_owner();
        let owner = self.rel_owner[rel]?;
        let owner_rels: Vec<usize> = self.b.elements[owner].owned_relationships.to_vec();
        let owner_ty = self.b.elements[owner].ty;
        if owner_ty == "AcceptActionUsage" {
            let ref_params: Vec<usize> = owner_rels
                .iter()
                .copied()
                .filter(|&r| {
                    self.b.elements[r].ty == "ParameterMembership"
                        && self.b.elements[r].children.first().is_some_and(|&k| {
                            matches!(self.b.elements[k].ty, "ReferenceUsage" | "Feature")
                        })
                })
                .collect();
            let pos = ref_params.iter().position(|&r| r == rel)?;
            return ["payload", "receiver"].get(pos).map(|n| n.to_string());
        }
        if !matches!(owner_ty, "InvocationExpression" | "ConstructorExpression") {
            return None;
        }
        // The callee: the invocation's fn/type Membership target (an
        // OwningMembership when the callee is a feature chain, which
        // spells no memberElement).
        let callee_rel = owner_rels
            .iter()
            .copied()
            .find(|&r| matches!(self.b.elements[r].ty, "Membership" | "OwningMembership"))?;
        let callee = self.prop_target(callee_rel, "memberElement")?;
        let params: Vec<Option<String>> = self.b.elements[callee]
            .owned_relationships
            .iter()
            .filter_map(|&r| self.b.elements[r].children.first().copied())
            .filter(|&k| {
                matches!(
                    self.b.elements[k]
                        .props
                        .get("direction")
                        .and_then(|v| v.as_str()),
                    Some("in" | "inout")
                )
            })
            .map(|k| self.declared(k, "declaredName"))
            .collect();
        let pos = owner_rels
            .iter()
            .filter(|&&r| self.b.elements[r].ty == "ParameterMembership")
            .position(|&r| r == rel)?;
        params.get(pos).cloned().flatten()
    }

    /// The segments of the specification's `qualifiedName`: the
    /// `escapedName()` of every element from the document root down —
    /// the effective name, else the effective short name — reached
    /// through memberships only (`qualifiedName` is null for an element
    /// without an `owningNamespace`, or with an unnamed one). Raw
    /// (unescaped), root first.
    pub(super) fn qualified_name_segments(&mut self, e: ElementRef) -> Option<Vec<String>> {
        self.qualified_name_walk(e, false).flatten()
    }

    /// The segments of `qualifiedName` as a checked answer: `None` when a
    /// segment's name cannot be derived, `Some(None)` when the qualified
    /// name is certainly null (an unowned element, an unnamed owner, or
    /// ownership through something other than a membership).
    pub(super) fn checked_qualified_name_segments(
        &mut self,
        e: ElementRef,
    ) -> Option<Option<Vec<String>>> {
        self.qualified_name_walk(e, true)
    }

    fn qualified_name_walk(&mut self, e: ElementRef, checked: bool) -> Option<Option<Vec<String>>> {
        self.ensure_rel_owner();
        let mut segs: Vec<String> = Vec::new();
        let mut cur = e.0;
        // The document root namespace is unnamed; reaching it (or any
        // unowned element) ends the walk.
        while let Some(rel) = self.b.elements[cur].owning_relationship {
            if !is_a!(self.b.elements[rel], "Membership") {
                return Some(None);
            }
            let seg = if checked {
                match self.checked_effective_name_of(cur)? {
                    Some(name) => name,
                    None => match self.checked_effective_short_name_of(cur)? {
                        Some(short) => short,
                        None => return Some(None),
                    },
                }
            } else {
                match self
                    .effective_name_of(cur)
                    .or_else(|| self.effective_short_name_of(cur))
                {
                    Some(seg) => seg,
                    None => return Some(None),
                }
            };
            segs.push(seg);
            let Some(owner) = self.rel_owner[rel] else {
                return Some(None);
            };
            cur = owner;
        }
        if segs.is_empty() {
            return Some(None);
        }
        segs.reverse();
        Some(Some(segs))
    }
}
