//! Complete ordered input evidence over the shared Membership reduction.
//! Compatibility projections and dynamic relationship publication are independent.
use super::{
    Builder, ElementRef, ResolvedModel, membership_evidence,
    membership_projection::{Membership, MembershipFacts, Node, Reachability, Reduction},
    semantic::certified_types::Stamp,
    semantic_ownership,
    structural_index::StoredStructure,
    type_relations::{self, TypeRelations},
};
use crate::metaclass::conforms;
use std::collections::{HashMap, HashSet};

/// Why a complete ordered Type projection could not be certified. Errors never mean
/// an empty input list. Additional supported domains may be added over time.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub enum TypeInputIssue {
    InvalidElement,
    InvalidRelationship,
    IncompleteProvider,
    UnsupportedConfiguration,
    CyclicDependency,
    StaleEvidence,
    WorkLimit,
}
/// Complete ordered inputs or an explicit qualification, with bounded query work.
#[derive(Clone, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub struct TypeInputReport {
    pub inputs: Result<Vec<ElementRef>, TypeInputIssue>,
    pub steps: usize,
}
/// Complete ordinary Function result selection, or an explicit qualification.
#[derive(Clone, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub struct FunctionResultReport {
    pub result: Result<Option<ElementRef>, TypeInputIssue>,
    pub steps: usize,
}
fn charge(steps: &mut usize, n: usize) -> Result<(), TypeInputIssue> {
    *steps = steps.saturating_add(n);
    if *steps > crate::eval::MAX_STEPS {
        Err(TypeInputIssue::WorkLimit)
    } else {
        Ok(())
    }
}
fn relationships(
    b: &Builder,
    owner: usize,
    steps: &mut usize,
) -> Result<Vec<usize>, TypeInputIssue> {
    let rows = semantic_ownership::owned_relationships(b, owner)
        .ok_or(TypeInputIssue::InvalidRelationship)?;
    charge(steps, rows.len())?;
    let rows: Vec<_> = rows.iter().collect();
    let mut seen = HashSet::new();
    if rows.iter().any(|r| !seen.insert(*r)) {
        return Err(TypeInputIssue::InvalidRelationship);
    }
    Ok(rows)
}

/// A structural owner's ordinary member has no end, parameter, subject, result
/// or state-subaction positional role. Its subclass's internal features need
/// their own certificates, but do not change this member's redefinition list.
fn ordinary_usage_member(
    b: &Builder,
    raw: &StoredStructure,
    feature: usize,
    steps: &mut usize,
) -> bool {
    let row = &b.elements[feature];
    if !matches!(
        row.ty,
        "PortUsage"
            | "ActionUsage"
            | "StateUsage"
            | "ConstraintUsage"
            | "ConnectionUsage"
            | "InterfaceUsage"
            | "AllocationUsage"
            | "FlowUsage"
            | "SuccessionAsUsage"
    ) || row.props.get("direction").is_some_and(|v| !v.is_null())
        || row
            .props
            .get("isEnd")
            .is_some_and(|v| v.as_bool() != Some(false))
    {
        return false;
    }
    let Some(membership) = row.owning_relationship else {
        return false;
    };
    if b.elements[membership].ty != "FeatureMembership" {
        return false;
    }
    // The main proof checks reciprocal ownership and complete ancestry below.
    // No assumption is made about features in an action/state/usage body.
    let Some(Some(owner)) =
        semantic_ownership::checked_relationship_carrier(b, raw, membership, steps)
    else {
        return false;
    };
    matches!(
        b.elements[owner].ty,
        "Type"
            | "Classifier"
            | "Class"
            | "Structure"
            | "DataType"
            | "Definition"
            | "AttributeDefinition"
            | "OccurrenceDefinition"
            | "ItemDefinition"
            | "PartDefinition"
    )
}
struct Facts<'a>(&'a Builder);
impl MembershipFacts for Facts<'_> {
    fn is_feature(&self, e: usize) -> bool {
        conforms(self.0.elements[e].ty, "Feature")
    }
    fn is_feature_membership(&self, r: usize) -> bool {
        conforms(self.0.elements[r].ty, "FeatureMembership")
    }
    fn is_protected(&self, r: usize) -> bool {
        self.0.elements[r]
            .props
            .get("visibility")
            .and_then(|v| v.as_str())
            == Some("protected")
    }
}
/// Every dependency is visited once; active marks distinguish cycles from diamonds.
fn order(
    graph: &HashMap<usize, Vec<usize>>,
    steps: &mut usize,
) -> Result<Vec<usize>, TypeInputIssue> {
    let mut state = HashMap::new();
    let mut ordered = Vec::new();
    for &root in graph.keys() {
        let mut todo = vec![(root, false)];
        while let Some((e, exit)) = todo.pop() {
            charge(steps, 1)?;
            if exit {
                state.insert(e, 2);
                ordered.push(e);
                continue;
            }
            match state.get(&e) {
                Some(1) => return Err(TypeInputIssue::CyclicDependency),
                Some(2) => continue,
                _ => {}
            }
            state.insert(e, 1);
            todo.push((e, true));
            let next = graph.get(&e).ok_or(TypeInputIssue::IncompleteProvider)?;
            charge(steps, next.len())?;
            todo.extend(next.iter().rev().map(|&n| (n, false)));
        }
    }
    Ok(ordered)
}
impl ResolvedModel {
    /// Certify Type.input for supported ordinary Types with complete ancestry,
    /// reciprocal memberships and nonconjugated directions. Public/protected
    /// package imports require exact central positional selector agreement;
    /// Contextual types and unsupported required families remain qualified.
    /// This does not validate the whole Function or change compatibility reads,
    /// evaluate it, or publish Invocation edges.
    pub fn type_input_report(&mut self, receiver: ElementRef) -> TypeInputReport {
        self.type_input_report_with_budget(receiver, 0)
    }
    pub(in crate::json) fn type_input_report_with_budget(
        &mut self,
        receiver: ElementRef,
        initial: usize,
    ) -> TypeInputReport {
        let mut steps = initial;
        let mut inputs = self.checked_inputs(receiver.0, &mut steps);
        if steps > crate::eval::MAX_STEPS {
            inputs = Err(TypeInputIssue::WorkLimit);
        }
        TypeInputReport { inputs, steps }
    }
    fn checked_inputs(
        &mut self,
        receiver: usize,
        steps: &mut usize,
    ) -> Result<Vec<ElementRef>, TypeInputIssue> {
        Ok(self.checked_type_features(receiver, steps)?.inputs)
    }

    /// Select the first effective ReturnParameterMembership of an ordinary
    /// Function. Absence is reported only for a complete supported provider.
    /// This does not certify uniqueness or validity of the Function as a whole.
    pub fn function_result_report(&mut self, receiver: ElementRef) -> FunctionResultReport {
        self.function_result_report_with_budget(receiver, 0)
    }
    pub(in crate::json) fn function_result_report_with_budget(
        &mut self,
        receiver: ElementRef,
        initial: usize,
    ) -> FunctionResultReport {
        let mut steps = initial;
        let result = if self.b.elements.get(receiver.0).is_none() {
            Err(TypeInputIssue::InvalidElement)
        } else if self.b.elements[receiver.0].ty != "Function" {
            Err(TypeInputIssue::UnsupportedConfiguration)
        } else {
            self.checked_type_features(receiver.0, &mut steps)
                .and_then(|sequence| {
                    let features = sequence.features;
                    charge(&mut steps, features.len())?;
                    Ok(features.into_iter().find(|f| {
                        self.b.elements[f.0].owning_relationship.is_some_and(|m| {
                            conforms(self.b.elements[m].ty, "ReturnParameterMembership")
                        })
                    }))
                })
        };
        FunctionResultReport {
            result: if steps > crate::eval::MAX_STEPS {
                Err(TypeInputIssue::WorkLimit)
            } else {
                result
            },
            steps,
        }
    }
}

impl super::Builder {
    pub(super) fn checked_type_memberships(
        &mut self,
        receiver: usize,
        steps: &mut usize,
    ) -> Result<super::type_features::MembershipSequence, TypeInputIssue> {
        self.checked_type_memberships_with_relations(receiver, steps, &mut TypeRelations::default())
    }
    /// Reuse only the shared relation evidence within one caller-guarded query.
    /// Membership reduction and positional verification remain per receiver.
    pub(super) fn checked_type_memberships_with_relations(
        &mut self,
        receiver: usize,
        steps: &mut usize,
        relations: &mut TypeRelations,
    ) -> Result<super::type_features::MembershipSequence, TypeInputIssue> {
        self.checked_type_memberships_filtered(receiver, false, &[], None, steps, relations)
    }
    /// Select imports and ancestry only after certifying the complete provider.
    pub(super) fn checked_type_membership_operation(
        &mut self,
        receiver: usize,
        excluded_namespaces: &[usize],
        excluded_types: &[usize],
        exclude_implied: bool,
        steps: &mut usize,
    ) -> Result<super::type_features::MembershipSequence, TypeInputIssue> {
        self.checked_type_memberships_filtered(
            receiver,
            exclude_implied,
            excluded_namespaces,
            Some(excluded_types),
            steps,
            &mut TypeRelations::default(),
        )
    }
    pub(super) fn checked_type_memberships_for_visibility(
        &mut self,
        receiver: usize,
        excluded_namespaces: &[usize],
        exclude_implied: bool,
        steps: &mut usize,
    ) -> Result<super::type_features::MembershipSequence, TypeInputIssue> {
        self.checked_type_memberships_filtered(
            receiver,
            exclude_implied,
            excluded_namespaces,
            None,
            steps,
            &mut TypeRelations::default(),
        )
    }
    fn checked_type_memberships_filtered(
        &mut self,
        receiver: usize,
        exclude_implied: bool,
        excluded_namespaces: &[usize],
        excluded_types: Option<&[usize]>,
        steps: &mut usize,
        relations: &mut TypeRelations,
    ) -> Result<super::type_features::MembershipSequence, TypeInputIssue> {
        charge(steps, 1)?;
        let row = self
            .elements
            .get(receiver)
            .ok_or(TypeInputIssue::InvalidElement)?;
        if !super::type_features::supported_root(row.ty) || self.positional_planning {
            return Err(TypeInputIssue::UnsupportedConfiguration);
        }
        if !self.ensure_positional_redefinitions_with_budget(steps) {
            return Err(TypeInputIssue::IncompleteProvider);
        }
        let retained = self
            .retained_typing_edges(steps)
            .ok_or(TypeInputIssue::IncompleteProvider)?;
        let raw =
            StoredStructure::for_query(self, steps).ok_or(TypeInputIssue::IncompleteProvider)?;
        if !raw.ids_unique || raw.annotations_incomplete || self.metadata_associations_incomplete {
            return Err(TypeInputIssue::IncompleteProvider);
        }
        let domains = raw
            .membership_domains(self, steps)
            .ok_or(TypeInputIssue::IncompleteProvider)?;
        let imports = raw
            .import_domains(self, steps)
            .ok_or(TypeInputIssue::IncompleteProvider)?;
        let inverse = raw
            .typing(self, steps)
            .ok_or(TypeInputIssue::IncompleteProvider)?;
        if inverse.sources_incomplete {
            return Err(TypeInputIssue::IncompleteProvider);
        }
        let stamp = Stamp::capture_builder(self);
        let b = &mut *self;
        let mut nodes = HashMap::new();
        let mut bases = HashMap::new();
        let mut features = Vec::new();
        let mut owned_memberships = Vec::new();
        let mut root_import = false;
        let mut visible_import_owners = HashSet::new();
        let mut imported_features = HashSet::new();
        let mut todo = vec![receiver];
        while let Some(owner) = todo.pop() {
            charge(steps, 1)?;
            if nodes.contains_key(&owner) {
                continue;
            }
            let element = b
                .elements
                .get(owner)
                .ok_or(TypeInputIssue::InvalidElement)?;
            if !super::type_features::supported_root(element.ty) || owner >= b.explicit_len() {
                return Err(TypeInputIssue::UnsupportedConfiguration);
            }
            if element.ty == "Feature"
                && (element
                    .props
                    .get("isEnd")
                    .is_some_and(|v| v.as_bool() != Some(false))
                    || element.props.get("direction").is_some_and(|v| !v.is_null()))
            {
                return Err(TypeInputIssue::UnsupportedConfiguration);
            }
            if !domains.owner_complete(owner)
                || !imports.owner_complete(owner)
                || raw.metadata_annotation_targets.contains(&owner)
                || b.metadata_of.get(&owner).is_some_and(|m| !m.is_empty())
            {
                return Err(TypeInputIssue::IncompleteProvider);
            }
            if relations
                .owned_conjugation(b, owner, steps)
                .ok_or(TypeInputIssue::IncompleteProvider)?
                .is_some()
            {
                return Err(TypeInputIssue::UnsupportedConfiguration);
            }
            let direct = relations
                .complete_direct_bases(b, owner, steps)
                .ok_or(TypeInputIssue::IncompleteProvider)?;
            charge(steps, direct.len().saturating_mul(2))?;
            todo.extend(direct.iter().copied());
            bases.insert(owner, direct.clone());
            let mut node = Node {
                owned: Vec::new(),
                owned_memberships: Vec::new(),
                bases: direct,
                public_imports: Vec::new(),
                protected_imports: Vec::new(),
                memberships_complete: true,
            };
            for rel in relationships(b, owner, steps)? {
                charge(steps, 1)?;
                if semantic_ownership::checked_relationship_carrier(b, &raw, rel, steps)
                    != Some(Some(owner))
                {
                    return Err(TypeInputIssue::InvalidRelationship);
                }
                if conforms(b.elements[rel].ty, "Import") {
                    super::import_memberships::checked_import_target(b, &raw, owner, rel, steps)
                        .ok_or(TypeInputIssue::InvalidRelationship)?;
                    if b.elements[rel]
                        .props
                        .get("visibility")
                        .is_some_and(|v| v.as_str() != Some("private"))
                    {
                        visible_import_owners.insert(owner);
                    }
                    root_import |= owner == receiver;
                }
                let row = &b.elements[rel];
                if !conforms(row.ty, "Membership") {
                    continue;
                }
                let member = membership_evidence::member(b, &raw, owner, rel, steps)
                    .ok_or(TypeInputIssue::InvalidRelationship)?;
                let visibility = match row.props.get("visibility") {
                    None => "public",
                    Some(v) => v
                        .as_str()
                        .filter(|s| matches!(*s, "public" | "protected" | "private"))
                        .ok_or(TypeInputIssue::InvalidRelationship)?,
                };
                let membership = Membership {
                    relationship: rel,
                    member,
                };
                if owner == receiver {
                    owned_memberships.push(membership);
                }
                if conforms(row.ty, "FeatureMembership") {
                    if !conforms(b.elements[member].ty, "Feature") {
                        return Err(TypeInputIssue::InvalidRelationship);
                    }
                    node.owned.push(member);
                }
                if conforms(b.elements[member].ty, "Feature") {
                    features.push(member);
                }
                if visibility != "private" {
                    node.owned_memberships.push(membership);
                }
            }
            if visible_import_owners.contains(&owner) {
                let (public, protected) = super::operations::namespaces::imports::type_imports(
                    b,
                    &raw,
                    owner,
                    &[],
                    steps,
                )
                .map_err(|_| TypeInputIssue::IncompleteProvider)?;
                charge(steps, public.len().saturating_add(protected.len()))?;
                for membership in public.iter().chain(&protected) {
                    if conforms(b.elements[membership.member].ty, "Feature") {
                        features.push(membership.member);
                        imported_features.insert(membership.member);
                        // External owning Types are proof dependencies, never extra
                        // bases or inheritance contributions of the receiver.
                        if let Some(declaring) = relations
                            .owning_type(b, membership.member, steps)
                            .ok_or(TypeInputIssue::IncompleteProvider)?
                        {
                            todo.push(declaring);
                        }
                    }
                }
                node.public_imports = public;
                node.protected_imports = protected;
            }
            nodes.insert(owner, node);
        }
        let ordered = order(&bases, steps)?;
        let mut redefinitions = HashMap::new();
        let mut authored = HashMap::new();
        let mut feature_owners = HashMap::new();
        while let Some(feature) = features.pop() {
            charge(steps, 1)?;
            if redefinitions.contains_key(&feature) {
                continue;
            }
            let row = b
                .elements
                .get(feature)
                .ok_or(TypeInputIssue::InvalidElement)?;
            if !conforms(row.ty, "Feature")
                || (conforms(row.ty, "Usage")
                    && !ordinary_usage_member(b, &raw, feature, steps)
                    && !matches!(
                        row.ty,
                        "ReferenceUsage"
                            | "AttributeUsage"
                            | "OccurrenceUsage"
                            | "ItemUsage"
                            | "PartUsage"
                    ))
                || conforms(row.ty, "InvocationExpression")
                || raw.bad_bases.contains(&feature)
                || raw.metadata_annotation_targets.contains(&feature)
                || b.metadata_of.get(&feature).is_some_and(|m| !m.is_empty())
                || !b.dynamic_evidence_current(feature)
                || !b.result_redefinition_evidence_current(feature)
            {
                return Err(TypeInputIssue::IncompleteProvider);
            }
            if relations
                .owned_conjugation(b, feature, steps)
                .ok_or(TypeInputIssue::IncompleteProvider)?
                .is_some()
            {
                return Err(TypeInputIssue::UnsupportedConfiguration);
            }
            let owning_type = relations
                .owning_type(b, feature, steps)
                .ok_or(TypeInputIssue::IncompleteProvider)?;
            let owner = match owning_type {
                Some(owner) => {
                    if membership_evidence::parameter_direction(b, &raw, feature, steps).is_none() {
                        return Err(TypeInputIssue::InvalidRelationship);
                    }
                    owner
                }
                None if imported_features.contains(&feature)
                    && b.elements[feature].ty == "Feature" =>
                {
                    let membership = b.elements[feature]
                        .owning_relationship
                        .filter(|&m| b.elements[m].ty == "OwningMembership")
                        .ok_or(TypeInputIssue::IncompleteProvider)?;
                    let owner = semantic_ownership::checked_relationship_carrier(
                        b, &raw, membership, steps,
                    )
                    .flatten()
                    .ok_or(TypeInputIssue::InvalidRelationship)?;
                    if !matches!(
                        b.elements[owner].ty,
                        "Namespace" | "Package" | "LibraryPackage"
                    ) || membership_evidence::member(b, &raw, owner, membership, steps)
                        != Some(feature)
                        || b.elements[feature]
                            .props
                            .get("direction")
                            .is_some_and(|v| !v.is_null())
                        || ["isEnd", "isPortion", "isComposite", "isVariable"]
                            .iter()
                            .any(|key| {
                                b.elements[feature]
                                    .props
                                    .get(key)
                                    .is_some_and(|v| v.as_bool() != Some(false))
                            })
                        || raw.metadata_annotation_targets.contains(&owner)
                        || b.metadata_of.get(&owner).is_some_and(|m| !m.is_empty())
                    {
                        return Err(TypeInputIssue::UnsupportedConfiguration);
                    }
                    owner
                }
                None if matches!(b.elements[feature].ty, "Multiplicity" | "MultiplicityRange") => {
                    // A named multiplicity can be an ordinary owned member of a
                    // Type without being one of its features. It still participates
                    // in Membership redefinition reduction, using the same complete
                    // inverse ownership evidence. Directed or end multiplicities
                    // require a separate FeatureMembership/positional certificate.
                    let membership = b.elements[feature]
                        .owning_relationship
                        .filter(|&m| b.elements[m].ty == "OwningMembership")
                        .ok_or(TypeInputIssue::IncompleteProvider)?;
                    let owner = semantic_ownership::checked_relationship_carrier(
                        b, &raw, membership, steps,
                    )
                    .flatten()
                    .ok_or(TypeInputIssue::InvalidRelationship)?;
                    if membership_evidence::member(b, &raw, owner, membership, steps)
                        != Some(feature)
                        || b.elements[feature]
                            .props
                            .get("direction")
                            .is_some_and(|v| !v.is_null())
                        || b.elements[feature]
                            .props
                            .get("isEnd")
                            .is_some_and(|v| v.as_bool() != Some(false))
                    {
                        return Err(TypeInputIssue::InvalidRelationship);
                    }
                    owner
                }
                None => return Err(TypeInputIssue::IncompleteProvider),
            };
            if !visible_import_owners.is_empty() {
                charge(steps, 1)?;
                feature_owners.insert(feature, owner);
            }
            if !nodes.contains_key(&owner) && !imported_features.contains(&feature) {
                return Err(TypeInputIssue::IncompleteProvider);
            }
            if !domains.owner_complete(owner)
                || b.elements[feature]
                    .props
                    .get("isEnd")
                    .is_some_and(|v| v.as_bool().is_none())
            {
                return Err(TypeInputIssue::InvalidRelationship);
            }
            let owned = relationships(b, feature, steps)?;
            let mut actual = HashSet::new();
            let mut targets = Vec::new();
            let mut authored_targets = Vec::new();
            for rel in owned.into_iter().chain(
                inverse
                    .relationships
                    .get(&feature)
                    .into_iter()
                    .flatten()
                    .copied(),
            ) {
                charge(steps, 1)?;
                if !conforms(b.elements[rel].ty, "Redefinition") || !actual.insert(rel) {
                    continue;
                }
                if !b.static_chain_row_current(rel) || !b.result_redefinition_row_current(rel) {
                    return Err(TypeInputIssue::StaleEvidence);
                }
                let carrier = semantic_ownership::checked_relationship_carrier(b, &raw, rel, steps)
                    .ok_or(TypeInputIssue::InvalidRelationship)?;
                // The shared reducer uses one redefinition closure. Until its
                // inverse-only and owned roles are distinct, qualify standalone
                // Redefinitions rather than treating them as owned closure edges.
                if carrier != Some(feature) {
                    return Err(TypeInputIssue::UnsupportedConfiguration);
                }
                let target = type_relations::endpoint_with_carrier(
                    b,
                    feature,
                    carrier,
                    rel,
                    &["specific", "subsettingFeature", "redefiningFeature"],
                    &["general", "subsettedFeature", "redefinedFeature"],
                    "Feature",
                    steps,
                )
                .ok_or(TypeInputIssue::InvalidRelationship)?;
                targets.push(target);
                if rel < b.explicit_len() {
                    authored_targets.push(target);
                }
            }
            let implied = retained.get(&feature).map_or(&[][..], Vec::as_slice);
            charge(steps, implied.len())?;
            for &(kind, id) in implied {
                if conforms(kind, "Redefinition") {
                    targets.push(
                        raw.element_for_uuid(b, id)
                            .ok_or(TypeInputIssue::IncompleteProvider)?,
                    );
                }
            }
            authored.insert(feature, authored_targets);
            charge(steps, targets.len().saturating_mul(2))?;
            let mut seen = HashSet::new();
            targets.retain(|t| seen.insert(*t));
            features.extend(targets.iter().copied());
            redefinitions.insert(feature, targets);
        }
        if b.positional_redefinition_sources_match(&authored, steps) != Some(true) {
            return Err(TypeInputIssue::StaleEvidence);
        }
        // A proof-only foreign owner is not ordered before the importing Type
        // by the positional planner's ancestry traversal. Its generated edges
        // can change inherited suppression even through an alias Membership.
        // Legacy retains that planner, so require actual ancestry. Canonical
        // planning certifies and schedules the supported foreign prerequisites
        // below using these same complete source/owner proof nodes.
        if b.graph_format == crate::model::GraphFormat::LegacyV2
            && !visible_import_owners.is_empty()
        {
            let mut closure = Reachability::sparse();
            let mut ancestry = Reachability::sparse();
            for &owner in &visible_import_owners {
                let node = &nodes[&owner];
                charge(
                    steps,
                    node.public_imports
                        .len()
                        .saturating_add(node.protected_imports.len()),
                )?;
                for membership in node.public_imports.iter().chain(&node.protected_imports) {
                    if !conforms(b.elements[membership.member].ty, "Feature") {
                        continue;
                    }
                    let reached = closure
                        .reachable_budget(membership.member, &redefinitions, &mut Some(steps))
                        .ok_or(TypeInputIssue::WorkLimit)?;
                    charge(steps, reached.len())?;
                    for &feature in reached {
                        if b.elements[feature]
                            .props
                            .get("isEnd")
                            .and_then(|v| v.as_bool())
                            != Some(true)
                            && !b.is_parameter(feature)
                        {
                            continue;
                        }
                        let declaring = *feature_owners
                            .get(&feature)
                            .ok_or(TypeInputIssue::IncompleteProvider)?;
                        if !ancestry
                            .reaches_budget(owner, declaring, &bases, &mut Some(steps))
                            .ok_or(TypeInputIssue::WorkLimit)?
                        {
                            return Err(TypeInputIssue::IncompleteProvider);
                        }
                    }
                }
            }
        }
        let positional = b
            .plan_checked_positional(&nodes, &bases, &visible_import_owners, steps)
            .ok_or(TypeInputIssue::IncompleteProvider)?;
        charge(steps, nodes.len())?;
        if nodes
            .keys()
            .any(|owner| positional.incomplete.contains(owner))
        {
            return Err(TypeInputIssue::IncompleteProvider);
        }
        let required_positional = positional.targets;
        for (&feature, targets) in &required_positional {
            charge(steps, targets.len().saturating_add(1))?;
            if targets
                .iter()
                .any(|target| !redefinitions.contains_key(target))
            {
                return Err(TypeInputIssue::IncompleteProvider);
            }
            redefinitions
                .get_mut(&feature)
                .ok_or(TypeInputIssue::IncompleteProvider)?
                .extend(targets.iter().copied());
        }
        order(&redefinitions, steps)?;
        // Excluding implied supertypes changes only inheritance selection.
        // Redefinition suppression still uses the complete semantic certificate.
        let ordered = if exclude_implied {
            let mut explicit_bases = HashMap::new();
            for (&owner, node) in &mut nodes {
                charge(steps, 1)?;
                let direct = relations
                    .checked_supertypes(b, owner, true, steps)
                    .map_err(|_| TypeInputIssue::IncompleteProvider)?;
                charge(steps, direct.len())?;
                if direct.iter().any(|target| !bases.contains_key(target)) {
                    return Err(TypeInputIssue::IncompleteProvider);
                }
                node.bases = direct.clone();
                explicit_bases.insert(owner, direct);
            }
            order(&explicit_bases, steps)?
        } else {
            ordered
        };
        // Selection exclusions must not hide incomplete ancestry, malformed
        // redefinitions, or positional evidence. The full certificate above is
        // established before changing any contributing edge. Cycles remain
        // qualified, so path-specific excludingSelf adds no additional cuts.
        if let Some(excluded) = excluded_types {
            charge(steps, excluded.len())?;
            let excluded: HashSet<_> = excluded.iter().copied().collect();
            for node in nodes.values_mut() {
                charge(steps, node.bases.len())?;
                node.bases.retain(|base| !excluded.contains(base));
            }
        }
        if !excluded_namespaces.is_empty() {
            for &owner in &visible_import_owners {
                charge(steps, 1)?;
                let (public, protected) = super::operations::namespaces::imports::type_imports(
                    b,
                    &raw,
                    owner,
                    excluded_namespaces,
                    steps,
                )
                .map_err(|_| TypeInputIssue::IncompleteProvider)?;
                let node = nodes
                    .get_mut(&owner)
                    .ok_or(TypeInputIssue::IncompleteProvider)?;
                node.public_imports = public;
                node.protected_imports = protected;
            }
        }
        let mut reduction = Reduction::default();
        let mut reachability = Reachability::sparse();
        let mut exported = HashMap::new();
        let mut inherited = Vec::new();
        let mut inheritable = Vec::new();
        for owner in ordered {
            let node = &nodes[&owner];
            if owner == receiver && excluded_types.is_some() {
                inheritable = reduction
                    .inheritable(node, &exported, &mut Some(steps))
                    .ok_or(TypeInputIssue::WorkLimit)?;
            }
            let (_, surviving) = reduction
                .reduce(
                    node,
                    &exported,
                    &redefinitions,
                    &mut reachability,
                    &Facts(b),
                    &mut Some(steps),
                )
                .ok_or(TypeInputIssue::WorkLimit)?;
            if owner == receiver {
                charge(steps, surviving.len())?;
                inherited = surviving.clone();
            }
            let visible = reduction
                .export(node, surviving, &Facts(b), &mut Some(steps))
                .ok_or(TypeInputIssue::WorkLimit)?;
            exported.insert(owner, visible);
        }
        if !stamp.current_builder(self) {
            return Err(TypeInputIssue::StaleEvidence);
        }
        Ok(super::type_features::MembershipSequence {
            owned: owned_memberships,
            inherited,
            inheritable,
            non_private: if excluded_types.is_some() {
                exported
                    .remove(&receiver)
                    .ok_or(TypeInputIssue::IncompleteProvider)?
            } else {
                Vec::new()
            },
            root_import,
            required_positional,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        json::{ClosurePolicy, PropertyError},
        model::{GraphFormat, Model},
    };
    const LIB: &str = "standard library package Base { classifier Anything; feature things:Anything; } standard library package Occurrences { class Occurrence specializes Base::Anything; feature occurrences:Occurrence subsets Base::things; } standard library package Performances { behavior Performance specializes Occurrences::Occurrence; function Evaluation specializes Performance { return result; } step performances:Performance subsets Occurrences::occurrences; expr evaluations:Evaluation subsets performances; }";
    fn fixture(source: &str) -> ResolvedModel {
        fixture_format(source, GraphFormat::LegacyV2)
    }
    fn fixture_format(source: &str, format: GraphFormat) -> ResolvedModel {
        let mut m = Model::with_graph_format(format);
        assert!(
            m.add_library_source("inputs-library.kerml", LIB)
                .diagnostics
                .is_empty()
        );
        let unit = m.add_source("inputs.kerml", source);
        assert!(unit.diagnostics.is_empty(), "{:?}", unit.diagnostics);
        ResolvedModel::build(&m)
    }
    #[test]
    fn visible_package_imports_preserve_aliases_order_and_redefinition() {
        for format in [GraphFormat::LegacyV2, GraphFormat::CanonicalV3] {
            let mut r = fixture_format(
                "class External {feature original; feature kept;} package P {class Scalar; alias Named for Scalar; feature slot; alias original for External::original; alias kept for External::kept;} class A {public import P::Named; public import P::slot; public import P::original; protected import P::kept; protected feature own;} class B specializes A {feature replacement redefines External::original;}",
                format,
            );
            let p = r.resolve_qualified("P").unwrap().0;
            let b = r.resolve_qualified("B").unwrap().0;
            let alias = |r: &ResolvedModel, name: &str| {
                *r.b.elements[p]
                    .owned_relationships
                    .iter()
                    .find(|&&m| {
                        r.b.elements[m].ty == "Membership"
                            && r.b.elements[m]
                                .props
                                .get("memberName")
                                .and_then(|v| v.as_str())
                                == Some(name)
                    })
                    .unwrap()
            };
            let named = alias(&r, "Named");
            let original = alias(&r, "original");
            let kept = alias(&r, "kept");
            let slot = r.resolve_qualified("P::slot").unwrap().0;
            let slot = r.b.elements[slot].owning_relationship.unwrap();
            let own = r.resolve_qualified("A::own").unwrap().0;
            let own = r.b.elements[own].owning_relationship.unwrap();
            let proof =
                r.b.checked_type_membership_operation(b, &[], &[], true, &mut 0)
                    .unwrap();
            assert_eq!(
                proof
                    .inheritable
                    .iter()
                    .map(|m| m.relationship)
                    .collect::<Vec<_>>(),
                [named, slot, original, own, kept]
            );
            assert_eq!(
                proof
                    .inherited
                    .iter()
                    .map(|m| m.relationship)
                    .collect::<Vec<_>>(),
                [named, slot, own, kept]
            );
            let features = r.type_feature_report(ElementRef(b)).projections.unwrap();
            assert_eq!(features.features.len(), 2);
            // Alias memberships inherit without turning the imported Features
            // into FeatureMembership slots or adding their owner's own members.
            assert!(features.inherited_memberships.contains(&ElementRef(kept)));
        }
    }
    #[test]
    fn namespace_exclusions_select_imports_after_full_proof_and_budget_is_retryable() {
        for format in [GraphFormat::LegacyV2, GraphFormat::CanonicalV3] {
            let mut r = fixture_format(
                "package P {class Imported;} class A {public import P::*; class Local;} class B specializes A;",
                format,
            );
            let b = r.resolve_qualified("B").unwrap().0;
            let p = r.resolve_qualified("P").unwrap().0;
            let a = r.resolve_qualified("A").unwrap().0;
            let baseline =
                r.b.checked_type_membership_operation(b, &[], &[], true, &mut 0)
                    .unwrap();
            assert_eq!(baseline.inherited.len(), 2);
            let selected =
                r.b.checked_type_membership_operation(b, &[p], &[], true, &mut 0)
                    .unwrap();
            assert_eq!(selected.inherited.len(), 1);
            assert_eq!(
                selected.inherited[0].member,
                r.resolve_qualified("A::Local").unwrap().0
            );
            let mut exhausted_steps = crate::eval::MAX_STEPS;
            assert!(
                r.b.checked_type_membership_operation(b, &[], &[], true, &mut exhausted_steps)
                    .is_err()
            );
            assert_eq!(
                r.b.checked_type_membership_operation(b, &[], &[], true, &mut 0)
                    .unwrap()
                    .inherited
                    .len(),
                2
            );
            let import = *r.b.elements[a]
                .owned_relationships
                .iter()
                .find(|&&rel| conforms(r.b.elements[rel].ty, "Import"))
                .unwrap();
            let wrong = r.b.elements[a].id.to_string();
            r.b.set(import, "importedElement", serde_json::json!({"@id":wrong}));
            assert!(
                r.b.checked_type_membership_operation(b, &[p], &[a], true, &mut 0)
                    .is_err()
            );
        }
    }
    #[test]
    fn broader_import_providers_do_not_bypass_central_positional_completeness() {
        for source in [
            "package P {class Imported;} package Q {public import P::*;} class A {public import Q::*;} class B specializes A;",
            "package P {package Q;} class A {public import P::**;} class B specializes A;",
            "class External {feature original;} class A {public import External::original;} class B specializes A;",
        ] {
            let mut r = fixture(source);
            let b = r.resolve_qualified("B").unwrap().0;
            let a = r.resolve_qualified("A").unwrap().0;
            assert!(
                r.b.checked_type_membership_operation(b, &[], &[a], true, &mut 0)
                    .is_err()
            );
        }
    }
    #[test]
    fn canonical_imports_compose_transitive_packages_and_foreign_ordinary_features() {
        for (source, names) in [
            (
                "package P {class Imported;} package Q {public import P::*;} class A {public import Q::*;} class B specializes A;",
                vec!["P::Imported"],
            ),
            (
                "class Ancestor {feature original;} class External specializes Ancestor {feature selected redefines Ancestor::original;} class A {public import External::selected;} class B specializes A; class C specializes B {feature replacement redefines External::selected;}",
                vec!["External::selected"],
            ),
        ] {
            for format in [GraphFormat::LegacyV2, GraphFormat::CanonicalV3] {
                let mut r = fixture_format(source, format);
                let b = r.resolve_qualified("B").unwrap().0;
                let selected =
                    r.b.checked_type_membership_operation(b, &[], &[], true, &mut 0);
                if format == GraphFormat::LegacyV2 {
                    assert!(selected.is_err(), "{source}");
                    continue;
                }
                let expected: Vec<_> = names
                    .iter()
                    .map(|name| r.resolve_qualified(name).unwrap().0)
                    .collect();
                assert_eq!(
                    selected
                        .unwrap_or_else(|error| panic!("{format:?}: {source}: {error:?}"))
                        .inherited
                        .iter()
                        .map(|m| m.member)
                        .collect::<Vec<_>>(),
                    expected,
                    "{source}"
                );
                if let Some(c) = r.resolve_qualified("C") {
                    assert!(
                        r.b.checked_type_membership_operation(c.0, &[], &[], true, &mut 0)
                            .unwrap()
                            .inherited
                            .is_empty()
                    );
                }
            }
        }
    }

    #[test]
    fn many_cold_importing_types_share_recorded_edge_proof_within_the_work_limit() {
        let mut source = String::from(
            "class Source {feature shared;} package P {alias sharedAlias for Source::shared;} class Parent {end feature original;} class NoiseBase;",
        );
        for i in 0..1000 {
            source.push_str(&format!("class Noise{i} specializes NoiseBase;"));
        }
        for i in 0..3000 {
            source.push_str(&format!("class Child{i} specializes Parent {{public import P::sharedAlias; end feature replacement;}}"));
        }
        let mut r = fixture_format(&source, GraphFormat::CanonicalV3);
        let child = r.resolve_qualified("Child2999").unwrap();
        let replacement = r.resolve_qualified("Child2999::replacement").unwrap();
        let original = r.resolve_qualified("Parent::original").unwrap();
        // The first checked query prepares the complete positional table. Its
        // imported-source equality proof must not rescan all unrelated recorded
        // specializations for each importing Type and exhaust the fixed budget.
        let report = r.type_feature_report(child);
        let features = report
            .projections
            .unwrap_or_else(|error| panic!("{} steps: {error:?}", report.steps));
        assert!(report.steps < crate::eval::MAX_STEPS);
        assert!(features.features.contains(&replacement));
        assert!(!features.features.contains(&original));
        assert_eq!(
            r.b.positional_redefinitions
                .as_ref()
                .unwrap()
                .targets
                .get(&replacement.0),
            Some(&vec![original.0])
        );
    }

    #[test]
    fn canonical_transitive_import_exclusions_follow_full_proof_and_retries_are_bounded() {
        let source = "package P {class Imported;} package Q {public import P::*;} class A {public import Q::*;} class B specializes A;";
        let mut r = fixture_format(source, GraphFormat::CanonicalV3);
        let b = r.resolve_qualified("B").unwrap().0;
        let p = r.resolve_qualified("P").unwrap().0;
        let q = r.resolve_qualified("Q").unwrap().0;
        let a = r.resolve_qualified("A").unwrap().0;
        let mut used = 0;
        assert_eq!(
            r.b.checked_type_membership_operation(b, &[], &[], true, &mut used)
                .unwrap()
                .inherited
                .len(),
            1
        );
        assert!(used > 1 && used < crate::eval::MAX_STEPS);
        for excluded in [p, q] {
            assert!(
                r.b.checked_type_membership_operation(b, &[excluded], &[], true, &mut 0)
                    .unwrap()
                    .inherited
                    .is_empty()
            );
        }
        let mut steps = crate::eval::MAX_STEPS;
        assert!(
            r.b.checked_type_membership_operation(b, &[], &[], true, &mut steps)
                .is_err()
        );
        assert_eq!(
            r.b.checked_type_membership_operation(b, &[], &[], true, &mut 0)
                .unwrap()
                .inherited
                .len(),
            1
        );
        let import = *r.b.elements[q]
            .owned_relationships
            .iter()
            .find(|&&rel| conforms(r.b.elements[rel].ty, "Import"))
            .unwrap();
        let wrong = r.b.elements[a].id.to_string();
        r.b.set(import, "importedElement", serde_json::json!({"@id":wrong}));
        assert!(
            r.b.checked_type_membership_operation(b, &[p, q], &[a], true, &mut 0)
                .is_err()
        );
    }

    #[test]
    fn canonical_imported_positional_dependencies_remain_qualified() {
        for source in [
            "class Marker; package P {package Q {alias Alias for Marker;}} class A {public import P::**;} class B specializes A;",
            "package P {class Marker; public import Q::*;} package Q {public import P::*;} class A {public import P::*;} class B specializes A;",
            "function Foreign {in original;} class Parent; class External specializes Parent {feature selected redefines Foreign::original;} class A {public import External::selected;} class B specializes A;",
            "package P {class Nested {feature original;}} class A {public import P::**;} class B specializes A;",
        ] {
            let mut r = fixture_format(source, GraphFormat::CanonicalV3);
            let b = r.resolve_qualified("B").unwrap().0;
            let a = r.resolve_qualified("A").unwrap().0;
            assert!(
                r.b.checked_type_membership_operation(b, &[], &[], true, &mut 0)
                    .is_err(),
                "{source}"
            );
            assert!(
                r.b.checked_type_membership_operation(b, &[], &[a], true, &mut 0)
                    .is_err(),
                "{source}"
            );
        }
    }

    #[test]
    fn exclude_implied_filters_inheritance_without_disabling_redefinition_suppression() {
        for redefinition in ["redefines A::a", ""] {
            let mut r = fixture(&format!(
                "function A {{ in a; feature kept; }} function B specializes A {{ in x {redefinition}; }}"
            ));
            let receiver = r.resolve_qualified("B").unwrap();
            let kept = r.resolve_qualified("A::kept").unwrap();
            let replaced = r.resolve_qualified("A::a").unwrap();
            let implicit = r
                .resolve_qualified("Performances::Evaluation::result")
                .unwrap();
            let ordinary = r.b.checked_type_memberships(receiver.0, &mut 0).unwrap();
            let explicit =
                r.b.checked_type_memberships_for_visibility(receiver.0, &[], true, &mut 0)
                    .unwrap();
            let ordinary: Vec<_> = ordinary
                .inherited
                .iter()
                .map(|m| ElementRef(m.member))
                .collect();
            let explicit: Vec<_> = explicit
                .inherited
                .iter()
                .map(|m| ElementRef(m.member))
                .collect();
            assert!(ordinary.contains(&kept));
            assert!(ordinary.contains(&implicit));
            assert!(!ordinary.contains(&replaced));
            assert_eq!(explicit, [kept]);
        }
    }

    fn read(r: &mut ResolvedModel, name: &str) -> Result<Vec<String>, TypeInputIssue> {
        let e = r.resolve_qualified(name).unwrap();
        r.type_input_report(e)
            .inputs
            .map(|v| v.into_iter().map(|e| r.element_id(e).to_string()).collect())
    }
    fn ids(r: &mut ResolvedModel, names: &[&str]) -> Vec<String> {
        names
            .iter()
            .map(|n| {
                let e = r.resolve_qualified(n).unwrap();
                r.element_id(e).to_string()
            })
            .collect()
    }
    #[test]
    fn function_result_reuses_complete_order_and_checked_multiplicity() {
        let mut r = fixture(
            "function A {return resultA;} function B {return resultB;} function C specializes A, B;",
        );
        let c = r.resolve_qualified("C").unwrap();
        let first = r.resolve_qualified("A::resultA").unwrap();
        assert_eq!(r.function_result_report(c).result, Ok(Some(first)));
        r.set_closure_policy(ClosurePolicy::Closure {
            include_implied: true,
        });
        assert_eq!(
            r.property(c, "result").unwrap(),
            serde_json::json!({"@id":r.element_id(first)})
        );
        let membership = r.b.elements[first.0].owning_relationship.unwrap();
        r.b.elements[membership]
            .props
            .insert("ownedMemberParameter", serde_json::Value::Null);
        assert!(r.function_result_report(c).result.is_err());
    }
    #[test]
    fn function_result_does_not_treat_missing_evidence_as_absence() {
        let mut r = fixture("function F {return r;} function G specializes F {return s;}");
        let g = r.resolve_qualified("G").unwrap();
        let s = r.resolve_qualified("G::s").unwrap();
        assert_eq!(r.function_result_report(g).result, Ok(Some(s)));
        assert_eq!(
            r.function_result_report_with_budget(g, crate::eval::MAX_STEPS)
                .result,
            Err(TypeInputIssue::WorkLimit)
        );
        assert_eq!(r.function_result_report(g).result, Ok(Some(s)));
        let mut missing = Model::new();
        missing.add_source("missing.kerml", "function F;");
        let mut r = ResolvedModel::build(&missing);
        let f = r.resolve_qualified("F").unwrap();
        assert!(r.function_result_report(f).result.is_err());
    }
    #[test]
    fn ordered_inputs_and_checked_read_preserve_compatibility() {
        let mut r = fixture(
            "function F { out feature diagnostic; in a; inout b; feature plain; return answer; } function Empty;",
        );
        let f = r.resolve_qualified("F").unwrap();
        let expected = ids(&mut r, &["F::a", "F::b"]);
        let before = r.derived(f, "input");
        assert_eq!(read(&mut r, "F"), Ok(expected.clone()));
        assert_eq!(read(&mut r, "Empty"), Ok(vec![]));
        assert_eq!(r.property(f, "input"), Err(PropertyError::Approximate));
        r.set_closure_policy(ClosurePolicy::Closure {
            include_implied: true,
        });
        assert_eq!(
            r.property(f, "input"),
            Ok(serde_json::json!(
                expected
                    .iter()
                    .map(|id| serde_json::json!({"@id":id}))
                    .collect::<Vec<_>>()
            ))
        );
        assert_eq!(r.derived(f, "input"), before);
    }
    #[test]
    fn inherited_order_redefinition_and_private_visibility() {
        let mut r = fixture(
            "function A { in a; private in secret; protected in b; } function B specializes A { in x redefines a; } function C specializes B;",
        );
        let expected = ids(&mut r, &["B::x", "A::b"]);
        assert_eq!(read(&mut r, "C"), Ok(expected));
        let expected = ids(&mut r, &["A::a", "A::secret", "A::b"]);
        assert_eq!(read(&mut r, "A"), Ok(expected));
    }
    #[test]
    fn malformed_direction_membership_and_inverse_claims_are_not_empty_inputs() {
        for damage in 0..5 {
            let mut r = fixture("function F { in a; out feature b; }");
            let f = r.resolve_qualified("F").unwrap();
            let a = r.resolve_qualified("F::a").unwrap();
            let b = r.resolve_qualified("F::b").unwrap();
            assert!(r.type_input_report(f).inputs.is_ok());
            let membership = r.b.elements[a.0].owning_relationship.unwrap();
            match damage {
                0 => {
                    r.b.elements[b.0]
                        .props
                        .insert("direction", serde_json::json!("invalid"));
                }
                1 => {
                    r.b.elements[membership]
                        .props
                        .insert("visibility", serde_json::json!("unknown"));
                }
                2 => {
                    let wrong = r.element_id(b).to_string();
                    r.b.elements[membership]
                        .props
                        .insert("memberElement", serde_json::json!({"@id":wrong}));
                }
                3 => {
                    r.b.elements[f.0]
                        .owned_relationships
                        .make_mut()
                        .retain(|&rel| rel != membership);
                }
                _ => {
                    r.b.elements[b.0].owning_relationship = Some(membership);
                }
            }
            assert!(r.type_input_report(f).inputs.is_err(), "damage {damage}");
        }
    }
    #[test]
    fn missing_library_unsupported_imports_and_budget_retry() {
        let mut model = Model::new();
        model.add_source("no-library.kerml", "function F;");
        let mut r = ResolvedModel::build(&model);
        assert!(read(&mut r, "F").is_err());
        let mut r = fixture("package P { in feature a; } function F { public import P::*; }");
        assert!(read(&mut r, "F").is_err());
        let mut r = fixture("function F { in a; }");
        let f = r.resolve_qualified("F").unwrap();
        assert_eq!(
            r.type_input_report_with_budget(f, crate::eval::MAX_STEPS)
                .inputs,
            Err(TypeInputIssue::WorkLimit)
        );
        assert!(r.type_input_report(f).inputs.is_ok());
    }
    #[test]
    fn private_imports_and_unrelated_local_import_damage_preserve_inputs() {
        let mut r = fixture(
            "package P {feature x;} function A {private import P::*; in a;} function B specializes A; package Q {private import P::*;}",
        );
        let expected = ids(&mut r, &["A::a"]);
        assert_eq!(read(&mut r, "B"), Ok(expected.clone()));
        let q = r.resolve_qualified("Q").unwrap().0;
        let import = r.b.elements[q]
            .owned_relationships
            .iter()
            .copied()
            .find(|&rel| conforms(r.b.elements[rel].ty, "Import"))
            .unwrap();
        r.b.elements[q]
            .owned_relationships
            .make_mut()
            .retain(|&rel| rel != import);
        assert_eq!(read(&mut r, "B"), Ok(expected));
    }
    #[test]
    fn orphan_import_on_ancestor_refuses_inputs_even_when_marked_implied() {
        for visibility in ["private", "public", "protected"] {
            let mut r = fixture(&format!(
                "package P {{in feature x;}} function A {{{visibility} import P::*; in a;}} function B specializes A;"
            ));
            let initial = read(&mut r, "B");
            assert_eq!(initial.is_ok(), visibility == "private");
            let a = r.resolve_qualified("A").unwrap().0;
            let import = r.b.elements[a]
                .owned_relationships
                .iter()
                .copied()
                .find(|&rel| conforms(r.b.elements[rel].ty, "Import"))
                .unwrap();
            let position = r.b.elements[a]
                .owned_relationships
                .iter()
                .position(|&rel| rel == import)
                .unwrap();
            r.b.elements[a]
                .owned_relationships
                .make_mut()
                .remove(position);
            r.b.set(import, "isImplied", serde_json::json!(true));
            assert!(read(&mut r, "B").is_err(), "{visibility}");
            r.b.elements[a]
                .owned_relationships
                .make_mut()
                .insert(position, import);
            r.b.set(import, "isImplied", serde_json::json!(false));
            assert_eq!(read(&mut r, "B").is_ok(), visibility == "private");
        }
    }
    #[test]
    fn real_library_functions_in_both_formats() {
        let dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../../spec-refs/SysML-v2-Release/sysml.library");
        if !dir.exists() {
            return;
        }
        for format in [GraphFormat::LegacyV2, GraphFormat::CanonicalV3] {
            let mut m = Model::with_graph_format(format);
            m.load_library_dir(&dir).unwrap();
            assert!(m.add_source("real-inputs.kerml", "function F { in a; out feature diagnostic; inout b; return result; } function G specializes F;").diagnostics.is_empty());
            let mut r = ResolvedModel::build(&m);
            let expected = ids(&mut r, &["F::a", "F::b"]);
            assert_eq!(read(&mut r, "F"), Ok(expected.clone()), "{format:?}");
            assert_eq!(read(&mut r, "G"), Ok(expected), "{format:?}");
            assert_eq!(read(&mut r, "Performances::Evaluation"), Ok(vec![]));
        }
    }
    #[test]
    fn cold_large_library_input_slice_stays_within_shared_budget() {
        let dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../../spec-refs/SysML-v2-Release/sysml.library");
        if !dir.exists() {
            return;
        }
        for format in [GraphFormat::LegacyV2, GraphFormat::CanonicalV3] {
            let mut m = Model::with_graph_format(format);
            m.load_library_dir(&dir).unwrap();
            let mut source = String::from(
                "function A {in a; inout b; return r;} function B specializes A {in x redefines a;} function C specializes B;",
            );
            for i in 0..10_000 {
                source.push_str(&format!("class Unused{i};"));
            }
            assert!(
                m.add_source("large-inputs.kerml", &source)
                    .diagnostics
                    .is_empty()
            );
            let mut r = ResolvedModel::build(&m);
            let c = r.resolve_qualified("C").unwrap();
            let x = r.resolve_qualified("B::x").unwrap();
            let b = r.resolve_qualified("A::b").unwrap();
            let report = r.type_input_report(c);
            eprintln!("{format:?} cold large-library input work: {}", report.steps);
            assert_eq!(
                report.inputs,
                Ok(vec![x, b]),
                "{format:?}, {}",
                report.steps
            );
            assert!(report.steps <= crate::eval::MAX_STEPS);
            assert!(r.b.implied.is_none());
        }
    }
    #[test]
    fn nullable_ordinary_direction_and_parameter_defaults_are_distinct() {
        let mut r = fixture("function F { in a; feature plain; return r; }");
        let f = r.resolve_qualified("F").unwrap();
        let a = r.resolve_qualified("F::a").unwrap();
        let membership = r.b.elements[a.0].owning_relationship.unwrap();
        // Ordinary directed declarations use FeatureMembership; parameter
        // membership is a distinct abstract-syntax defaulting case.
        assert_eq!(r.b.elements[membership].ty, "FeatureMembership");
        r.b.elements[a.0]
            .props
            .entries
            .make_mut()
            .retain(|(key, _)| key.name() != "direction");
        assert_eq!(r.type_input_report(f).inputs, Ok(vec![]));
        r.b.elements[membership].ty = "ParameterMembership";
        assert_eq!(r.type_input_report(f).inputs, Ok(vec![a]));
        r.b.elements[a.0]
            .props
            .insert("direction", serde_json::Value::Null);
        assert!(r.type_input_report(f).inputs.is_err());
    }
    #[test]
    fn same_length_direction_redefinition_and_identity_edits_are_observed() {
        let mut r =
            fixture("function A { in a; in b; } function F specializes A { in x redefines a; }");
        let f = r.resolve_qualified("F").unwrap();
        let x = r.resolve_qualified("F::x").unwrap();
        let expected = ids(&mut r, &["F::x", "A::b"]);
        assert_eq!(read(&mut r, "F"), Ok(expected.clone()));
        r.b.elements[x.0]
            .props
            .insert("direction", serde_json::json!("out"));
        let output_only = ids(&mut r, &["A::b"]);
        assert_eq!(read(&mut r, "F"), Ok(output_only));
        r.b.elements[x.0]
            .props
            .insert("direction", serde_json::json!("in"));
        assert_eq!(read(&mut r, "F"), Ok(expected));
        let target = r.resolve_qualified("A::b").unwrap();
        let rel = r.b.elements[x.0]
            .owned_relationships
            .iter()
            .copied()
            .find(|&i| r.b.elements[i].ty == "Redefinition")
            .unwrap();
        let id = r.element_id(target);
        r.b.elements[rel]
            .props
            .insert("redefinedFeature", serde_json::json!({"@id":id}));
        // A stale positional/provider cache must not certify the old answer.
        let expected = ids(&mut r, &["F::x"]);
        let report = read(&mut r, "F");
        assert!(
            report.as_ref().is_err() || report.as_ref().is_ok_and(|v| v == &expected),
            "{report:?}"
        );
        r.b.elements[x.0].id = r.b.elements[target.0].id;
        assert!(r.type_input_report(f).inputs.is_err());
    }
    #[test]
    fn ordinary_authored_redefinition_does_not_exempt_parameter_ordinal() {
        let mut r =
            fixture("function A { in a; in b; } function F specializes A { in x redefines A::b; }");
        let expected = ids(&mut r, &["F::x"]);
        assert_eq!(read(&mut r, "F"), Ok(expected));
    }
    #[test]
    fn malformed_end_roles_and_external_redefinition_owners_are_qualified() {
        for value in [serde_json::Value::Null, serde_json::json!("true")] {
            let mut r = fixture("function A { in a; } function F specializes A { feature x; }");
            let a = r.resolve_qualified("A::a").unwrap();
            let x = r.resolve_qualified("F::x").unwrap();
            r.b.elements[a.0]
                .props
                .insert("isEnd", serde_json::json!(true));
            r.b.elements[x.0]
                .props
                .insert("isEnd", serde_json::json!(false));
            let expected = ids(&mut r, &["A::a"]);
            assert_eq!(read(&mut r, "F"), Ok(expected));
            r.b.elements[x.0]
                .props
                .insert("isEnd", serde_json::json!(true));
            assert_eq!(read(&mut r, "F"), Ok(vec![]));
            r.b.elements[x.0].props.insert("isEnd", value);
            assert!(read(&mut r, "F").is_err());
        }
        let mut r = fixture("function A { in a; } function F { in x redefines A::a; }");
        assert!(read(&mut r, "F").is_err());
    }
    #[test]
    fn cold_input_read_does_not_publish_rows_and_checks_supported_receivers() {
        let mut r = fixture("function F { in a; } class A;");
        let f = r.resolve_qualified("F").unwrap();
        let a = r.resolve_qualified("A").unwrap();
        let before = r.b.elements.len();
        assert!(r.b.implied.is_none());
        assert!(r.type_input_report(f).inputs.is_ok());
        assert_eq!(r.b.elements.len(), before);
        assert!(r.b.implied.is_none());
        r.set_closure_policy(ClosurePolicy::Closure {
            include_implied: true,
        });
        assert!(r.derived_exact(f, "input").is_ok());
        assert_eq!(r.property(a, "input"), Ok(serde_json::json!([])));
        assert_eq!(r.type_input_report(a).inputs, Ok(vec![]));
        assert_eq!(
            r.function_result_report(a).result,
            Err(TypeInputIssue::UnsupportedConfiguration)
        );
    }
    #[test]
    fn diamonds_multiple_base_order_and_transitive_redefinitions() {
        let mut r = fixture(
            "function A { in a; } function B specializes A; function C specializes A; function D specializes B,C; function E { in e; } function F specializes D,E; function G specializes F { in g redefines A::a; } function H specializes G { in h redefines G::g; }",
        );
        let expected = ids(&mut r, &["A::a", "E::e"]);
        assert_eq!(read(&mut r, "F"), Ok(expected));
        let expected = ids(&mut r, &["H::h", "E::e"]);
        assert_eq!(read(&mut r, "H"), Ok(expected));
    }
    #[test]
    fn inverse_redefinition_claims_and_conjugation_do_not_certify_absence() {
        for damage in 0..4 {
            let mut r =
                fixture("function A { in a; } function F specializes A { in x redefines a; }");
            assert!(read(&mut r, "F").is_ok());
            let f = r.resolve_qualified("F").unwrap();
            let x = r.resolve_qualified("F::x").unwrap();
            let rel = r.b.elements[x.0]
                .owned_relationships
                .iter()
                .copied()
                .find(|&i| r.b.elements[i].ty == "Redefinition")
                .unwrap();
            match damage {
                0 => r.b.elements[x.0]
                    .owned_relationships
                    .make_mut()
                    .retain(|&i| i != rel),
                1 => {
                    r.b.elements[rel].props.insert(
                        "redefiningFeature",
                        serde_json::json!({"@id":uuid::Uuid::nil()}),
                    );
                }
                2 => {
                    r.b.elements[rel].props.insert(
                        "redefinedFeature",
                        serde_json::json!({"@id":uuid::Uuid::nil()}),
                    );
                }
                _ => {
                    r.b.elements[f.0]
                        .props
                        .insert("isConjugated", serde_json::json!(true));
                }
            }
            assert!(r.type_input_report(f).inputs.is_err(), "damage {damage}");
        }
        let mut r = fixture("function A specializes B; function B specializes A;");
        assert!(read(&mut r, "A").is_err());
    }
    #[test]
    fn real_library_recorded_prepared_and_full_emission_preserve_inputs_and_graphs() {
        let dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../../spec-refs/SysML-v2-Release/sysml.library");
        if !dir.exists() {
            return;
        }
        for format in [GraphFormat::LegacyV2, GraphFormat::CanonicalV3] {
            let mut cold = Model::with_graph_format(format);
            cold.load_library_dir(&dir).unwrap();
            cold.record_library_cache();
            ResolvedModel::build(&cold);
            let cache = cold.take_recorded_library_cache().unwrap();
            let prepared = cold.prepare_library().unwrap();
            let bytes = prepared.to_bytes(119).unwrap();
            let decoded = std::sync::Arc::new(
                crate::prepared::PreparedLibrary::from_bytes(&bytes, 119).unwrap(),
            );
            let mut warm = Model::with_graph_format(format);
            decoded.install(&mut warm).unwrap();
            let mut prepared_model = Model::with_graph_format(format);
            prepared.install(&mut prepared_model).unwrap();
            let mut recorded = Model::with_graph_format(format);
            recorded.load_library_dir(&dir).unwrap();
            recorded.set_library_cache(cache);
            let source = "function F { in a; inout b; return answer; } function G specializes F; feature call=G(b=2); class A {out feature x; in feature y;} class B specializes A;";
            let mut expected = None;
            let mut expected_features = None;
            for m in [&mut cold, &mut recorded, &mut prepared_model, &mut warm] {
                m.add_source("input-replay.kerml", source);
                let mut r = ResolvedModel::build(m);
                let g = r.resolve_qualified("G").unwrap();
                let call = ElementRef(
                    (r.b.lib_boundary..r.b.elements.len())
                        .find(|&e| r.b.elements[e].ty == "InvocationExpression")
                        .unwrap(),
                );
                let mapping = r.invocation_binding_report(call).arguments.unwrap();
                assert_eq!(mapping.bindings.len(), 1);
                assert_eq!(
                    mapping.bindings[0].input,
                    r.resolve_qualified("F::b").unwrap()
                );
                let before =
                    crate::full::resolved_to_full_json(&mut r, m, Default::default()).unwrap();
                assert_eq!(r.invocation_binding_report(call).arguments, Ok(mapping));
                let b = r.resolve_qualified("B").unwrap();
                let p = r.type_feature_report(b).projections.unwrap();
                let projection_ids: Vec<Vec<_>> = [
                    &p.features,
                    &p.feature_memberships,
                    &p.inherited_memberships,
                    &p.inputs,
                    &p.outputs,
                    &p.directed_features,
                    &p.end_features,
                    p.memberships.as_ref().unwrap(),
                    p.members.as_ref().unwrap(),
                ]
                .into_iter()
                .map(|refs| refs.iter().map(|&e| r.element_id(e)).collect())
                .collect();
                if let Some(ref expected) = expected_features {
                    assert_eq!(&projection_ids, expected);
                } else {
                    expected_features = Some(projection_ids);
                }
                let value = read(&mut r, "G").unwrap();
                if let Some(ref expected) = expected {
                    assert_eq!(&value, expected);
                } else {
                    expected = Some(value);
                }
                assert_eq!(
                    crate::full::resolved_to_full_json(&mut r, m, Default::default()).unwrap(),
                    before
                );
                assert!(
                    r.type_input_report_with_budget(g, crate::eval::MAX_STEPS)
                        .inputs
                        .is_err()
                );
                assert!(r.type_input_report(g).inputs.is_ok());
            }
        }
    }
}

#[cfg(test)]
mod import_dependencies;

#[cfg(test)]
mod parameter_dependencies;

#[cfg(test)]
mod authored_dependencies;

#[cfg(test)]
mod visible_dependencies;
