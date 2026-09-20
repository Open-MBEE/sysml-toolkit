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
//! it explicitly redefines, else — for the memberships whose owned
//! feature implicitly redefines a library feature (a binary connector's
//! two ends, a flow's payload, a return parameter, a subject, an objective,
//! a view rendering, a transition's accepter, an invocation's positional
//! arguments) — the positional name the pilot implementation computes
//! from that implied redefinition, else the feature it references, else
//! the last link of its feature chain. The naming feature's name is
//! itself effective, so a chain of unnamed redefinitions resolves to the
//! first named ancestor. A naming feature outside the model (a library
//! feature when no library is loaded) is named through
//! [`ResolvedModel::set_library_names`] when the caller supplied a
//! library name table; otherwise the element stays unnamed, as it does
//! on the wire.
//!
//! These rules are the ones `full.rs` carried as `effective_name_of` /
//! `implied_member_name` / `qname_of`; the emitter now projects the
//! layer's values and keeps those only as the fallback for an element the
//! projection cannot find.

use super::{ElementRef, ResolvedModel};
use crate::metaclass::conforms;
use crate::properties::Atom;

/// The feature that names an unnamed one, once found.
enum Naming {
    /// A feature of the model.
    Feature(usize),
    /// A feature outside the model, already named through the library
    /// name table.
    Named(String),
    /// A positional name the pilot computes from an implied redefinition.
    Positional(String),
}

impl ResolvedModel {
    /// `Element::effectiveName()` for the element at `e`, memoized.
    pub(super) fn effective_name_of(&mut self, e: usize) -> Option<String> {
        self.ensure_name_memo();
        if let Some(memo) = &self.name_memo[e] {
            return memo.clone();
        }
        let name = self.effective_name_walk(e, 0);
        self.name_memo[e] = Some(name.clone());
        name
    }

    /// `Element::effectiveShortName()` for the element at `e`: the
    /// declared short name when the element declares either name, else
    /// the naming feature's effective short name (an implied positional
    /// name carries none).
    pub(super) fn effective_short_name_of(&mut self, e: usize) -> Option<String> {
        self.effective_short_name_walk(e, 0)
    }

    fn effective_short_name_walk(&mut self, e: usize, depth: usize) -> Option<String> {
        if depth > 32 {
            return None;
        }
        if self.declares_a_name(e) {
            return self.declared(e, "declaredShortName");
        }
        match self.naming_feature(e)? {
            Naming::Feature(t) => self.effective_short_name_walk(t, depth + 1),
            Naming::Named(_) | Naming::Positional(_) => None,
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
        let n = self.b.elements.len();
        if self.name_memo.len() != n {
            self.name_memo = vec![None; n];
        }
    }

    fn declared(&self, e: usize, key: &str) -> Option<String> {
        self.b.elements[e]
            .props
            .get(key)
            .and_then(|v| v.as_str())
            .map(str::to_string)
    }

    fn effective_name_walk(&mut self, e: usize, depth: usize) -> Option<String> {
        if depth > 32 {
            return None;
        }
        if self.declares_a_name(e) {
            return self.declared(e, "declaredName");
        }
        match self.naming_feature(e)? {
            Naming::Feature(t) => self.effective_name_walk(t, depth + 1),
            Naming::Named(n) | Naming::Positional(n) => Some(n),
        }
    }

    /// The naming feature of an unnamed element, in the pilot's
    /// precedence: the first explicitly redefined feature that resolved,
    /// the implied positional redefinition, then — unless the
    /// element is an actor or stakeholder parameter, whose reference
    /// subsets the library collection and carries no name — the referenced
    /// feature, then the chain's last link. Only explicit relationships
    /// count; the implied library specializations name nothing.
    fn naming_feature(&mut self, e: usize) -> Option<Naming> {
        self.ensure_by_id();
        let rels: Vec<usize> = self.b.elements[e].owned_relationships.to_vec();
        let mut reference: Option<Atom> = None;
        let mut last_chain: Option<Atom> = None;
        for r in rels {
            match self.b.elements[r].ty {
                "Redefinition" => {
                    if let Some(target) = self.b.elements[r].props.get("redefinedFeature").cloned()
                    {
                        if let Some(naming) = self.naming_target(&target) {
                            return Some(naming);
                        }
                    }
                }
                "ReferenceSubsetting" => {
                    if reference.is_none() {
                        reference = self.b.elements[r].props.get("referencedFeature").cloned();
                    }
                }
                "FeatureChaining" => {
                    last_chain = self.b.elements[r].props.get("chainingFeature").cloned();
                }
                _ => {}
            }
        }
        if let Some(n) = self.implied_member_name(e) {
            return Some(Naming::Positional(n));
        }
        let owning_ty = self.b.elements[e]
            .owning_relationship
            .map(|r| self.b.elements[r].ty);
        if matches!(owning_ty, Some("ActorMembership" | "StakeholderMembership")) {
            return None;
        }
        if let Some(naming) = reference.and_then(|t| self.naming_target(&t)) {
            return Some(naming);
        }
        last_chain.and_then(|t| self.naming_target(&t))
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
            None => self.external_names.get(&id).cloned().map(Naming::Named),
        }
    }

    /// The positional name of a member that implicitly redefines a library
    /// feature (the pilot's computed redefinitions are its naming
    /// features): a flow's payload feature redefines `payload`, a
    /// transition's accept action `accepter`, a return parameter `result`,
    /// a subject `subj`, an objective `obj`, a view rendering
    /// `viewRendering`; an invocation's positional argument redefines the
    /// callee's `in` parameter at its position; the two ends of a binary
    /// connector-family usage redefine the library binary ends (`source` /
    /// `target`; successions `earlierOccurrence` / `laterOccurrence`;
    /// bindings `thisThing` / `sameThing`). The implied Redefinition
    /// elements themselves are not materialized — only the names they
    /// would confer.
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
        let fixed = match rel_ty {
            "ReturnParameterMembership" => Some("result"),
            "SubjectMembership" => Some("subj"),
            "ObjectiveMembership" => Some("obj"),
            "ViewRenderingMembership" => Some("viewRendering"),
            _ => None,
        };
        if let Some(n) = fixed {
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
        let names: [&str; 2] = match self.b.elements[owner].ty {
            "SuccessionAsUsage" | "Succession" | "TransitionUsage" => {
                ["earlierOccurrence", "laterOccurrence"]
            }
            "BindingConnectorAsUsage" | "BindingConnector" => ["thisThing", "sameThing"],
            "ConnectionUsage"
            | "AllocationUsage"
            | "InterfaceUsage"
            | "Connector"
            | "FlowUsage"
            | "SuccessionFlowUsage"
            | "Flow"
            | "SuccessionFlow" => ["source", "target"],
            _ => return None,
        };
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
        self.ensure_rel_owner();
        let mut segs: Vec<String> = Vec::new();
        let mut cur = e.0;
        // The document root namespace is unnamed; reaching it (or any
        // unowned element) ends the walk.
        while let Some(rel) = self.b.elements[cur].owning_relationship {
            if !conforms(self.b.elements[rel].ty, "Membership") {
                return None;
            }
            let seg = self
                .effective_name_of(cur)
                .or_else(|| self.effective_short_name_of(cur))?;
            segs.push(seg);
            cur = self.rel_owner[rel]?;
        }
        if segs.is_empty() {
            return None;
        }
        segs.reverse();
        Some(segs)
    }
}
