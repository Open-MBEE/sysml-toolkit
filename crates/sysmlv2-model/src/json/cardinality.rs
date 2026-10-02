//! Checked multiplicity constraints and collection questions over shared evidence.
use super::{
    Builder, ElementRef, ResolvedModel, membership_evidence,
    semantic::certified_types::Stamp,
    semantic_ownership,
    structural_index::StoredStructure,
    type_relations::{self, TypeRelations},
};
use crate::metaclass::conforms;
use std::{
    collections::{HashMap, HashSet},
    sync::Arc,
};

/// An exact integer interval. An absent upper limit denotes infinity.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CardinalityBounds {
    pub lower: i128,
    pub upper: Option<i128>,
}
impl CardinalityBounds {
    /// Exact collection size, when the complete interval is a singleton.
    pub fn size(self) -> Option<i128> {
        (self.upper == Some(self.lower)).then_some(self.lower)
    }
    /// A proved emptiness answer; an interval containing zero and positive
    /// counts does not establish either answer.
    pub fn is_empty(self) -> Option<bool> {
        if self.upper == Some(0) {
            Some(true)
        } else if self.lower > 0 {
            Some(false)
        } else {
            None
        }
    }
    /// Proved validity of a one-based index. A possibly present position is unknown.
    pub fn contains_index(self, index: i128) -> Option<bool> {
        if index <= 0 || self.upper.is_some_and(|upper| index > upper) {
            Some(false)
        } else if index <= self.lower {
            Some(true)
        } else {
            None
        }
    }
}
/// Why a complete supported multiplicity domain could not be established.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub enum CardinalityIssue {
    InvalidElement,
    InvalidRelationship,
    IncompleteProvider,
    UnsupportedBound,
    CyclicDependency,
    ConflictingConstraints,
    StaleEvidence,
    WorkLimit,
}
/// Checked cardinality constraints. This proves bounds, not concrete members,
/// whole-model conformance, or the value of an arbitrary collection expression.
#[derive(Clone, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub struct CardinalityReport {
    pub bounds: Result<CardinalityBounds, CardinalityIssue>,
    /// Range or named Multiplicity identities contributing to the answer.
    pub multiplicities: Vec<ElementRef>,
    /// Structural Usage identities supplying the normative implicit singleton.
    pub implicit_singletons: Vec<ElementRef>,
    pub steps: usize,
}
fn charge(steps: &mut usize, amount: usize) -> Result<(), CardinalityIssue> {
    *steps = steps.saturating_add(amount);
    if *steps > crate::eval::MAX_STEPS {
        Err(CardinalityIssue::WorkLimit)
    } else {
        Ok(())
    }
}
impl ResolvedModel {
    /// Prove supported Type multiplicities using reciprocal owned membership,
    /// complete shared specialization evidence and exact receiver-aware bounds.
    /// Owned multiplicities stop inheritance, as in Type::multiplicities. When
    /// several inherited constraints apply their numeric domains intersect;
    /// incompatible constraints are errors, never an empty collection. Unlike
    /// the compatibility evaluator, missing semantic providers cannot establish
    /// an unconstrained default. Unsupported expressions remain qualified.
    pub fn cardinality_report(&mut self, receiver: ElementRef) -> CardinalityReport {
        self.cardinality_report_with_budget(receiver, 0)
    }
    /// Add cardinalities of a flat or nested sequence without pretending that
    /// one symbolic collection placeholder denotes one member. Closed reflection
    /// elements remain single declarations. Unknown receiver members stay qualified
    /// because their placeholder does not retain the outer receiver cardinality.
    pub fn collection_cardinality_report(
        &mut self,
        value: &crate::eval::Value,
    ) -> CardinalityReport {
        fn visit(
            r: &mut ResolvedModel,
            value: &crate::eval::Value,
            depth: usize,
            steps: &mut usize,
            domains: &mut Vec<ElementRef>,
            defaults: &mut Vec<ElementRef>,
            stamp: &mut Option<Stamp>,
        ) -> Result<CardinalityBounds, CardinalityIssue> {
            use crate::eval::Value;
            charge(steps, 1)?;
            if depth >= 64 {
                return Err(CardinalityIssue::WorkLimit);
            }
            match value {
                Value::Indeterminate | Value::UnboundMember(_) => {
                    Err(CardinalityIssue::IncompleteProvider)
                }
                Value::Unbound(element) => {
                    let report = r.cardinality_report_with_budget(*element, *steps);
                    *steps = report.steps;
                    let bounds = report.bounds?;
                    if stamp.as_ref().is_some_and(|previous| !previous.current(r)) {
                        return Err(CardinalityIssue::StaleEvidence);
                    }
                    if stamp.is_none() {
                        *stamp = Some(Stamp::capture(r));
                    }
                    domains.extend(report.multiplicities);
                    defaults.extend(report.implicit_singletons);
                    Ok(bounds)
                }
                Value::Sequence(items) => {
                    charge(steps, items.len())?;
                    let mut bounds = CardinalityBounds {
                        lower: 0,
                        upper: Some(0),
                    };
                    for item in items {
                        let next = visit(r, item, depth + 1, steps, domains, defaults, stamp)?;
                        bounds.lower = bounds
                            .lower
                            .checked_add(next.lower)
                            .ok_or(CardinalityIssue::UnsupportedBound)?;
                        bounds.upper = match (bounds.upper, next.upper) {
                            (Some(a), Some(b)) => {
                                Some(a.checked_add(b).ok_or(CardinalityIssue::UnsupportedBound)?)
                            }
                            _ => None,
                        };
                    }
                    Ok(bounds)
                }
                _ => Ok(CardinalityBounds {
                    lower: 1,
                    upper: Some(1),
                }),
            }
        }
        let mut steps = 0;
        let mut multiplicities = Vec::new();
        let mut implicit_singletons = Vec::new();
        let bounds = visit(
            self,
            value,
            0,
            &mut steps,
            &mut multiplicities,
            &mut implicit_singletons,
            &mut None,
        );
        if bounds.is_err() {
            multiplicities.clear();
            implicit_singletons.clear();
        }
        CardinalityReport {
            bounds,
            multiplicities,
            implicit_singletons,
            steps,
        }
    }
    fn cardinality_report_with_budget(
        &mut self,
        receiver: ElementRef,
        initial: usize,
    ) -> CardinalityReport {
        let mut steps = initial;
        let mut multiplicities = Vec::new();
        let mut implicit_singletons = Vec::new();
        let mut bounds = (|| {
            if !self
                .b
                .elements
                .get(receiver.0)
                .is_some_and(|e| conforms(e.ty, "Type"))
            {
                return Err(CardinalityIssue::InvalidElement);
            }
            // Shared preparation precedes the stamp; readers never publish a
            // competing graph or retain a partial proof across a mutation.
            if !self
                .b
                .ensure_positional_redefinitions_with_budget(&mut steps)
            {
                return Err(CardinalityIssue::IncompleteProvider);
            }
            let raw = StoredStructure::for_query(&mut self.b, &mut steps)
                .ok_or(CardinalityIssue::IncompleteProvider)?;
            if !raw.ids_unique
                || raw.annotations_incomplete
                || self.b.metadata_associations_incomplete
            {
                return Err(CardinalityIssue::IncompleteProvider);
            }
            let context = self.b.owner_scope_of(receiver.0);
            let mut reader = Reader {
                raw,
                relations: TypeRelations::default(),
                active: HashSet::new(),
                known: HashMap::new(),
                domains: HashSet::new(),
                expressions: HashSet::new(),
                universal_relationships: HashSet::new(),
                steps: &mut steps,
            };
            let result = reader.constraints(&mut self.b, receiver.0, 0)?;
            let stamp = Stamp::capture(self);
            charge(reader.steps, result.len())?;
            for &domain in &result {
                if let Constraint::Range(domain) = domain {
                    reader.validate_domain(&mut self.b, domain, 0)?;
                }
            }
            let expressions = std::mem::take(&mut reader.expressions);
            let universal_relationships = std::mem::take(&mut reader.universal_relationships);
            drop(reader);
            let mut operators = certified_operators(self, &expressions, context, &mut steps)?;
            operators.universal_relationships = universal_relationships;
            let mut bounds = CardinalityBounds {
                lower: 0,
                upper: None,
            };
            for domain in result {
                let (lower, upper) = match domain {
                    Constraint::Range(domain) => {
                        multiplicities.push(ElementRef(domain));
                        crate::eval::checked_multiplicity_domain(
                            &mut self.b,
                            domain,
                            context,
                            &operators,
                            &mut steps,
                        )
                        .ok_or(CardinalityIssue::UnsupportedBound)?
                    }
                    Constraint::Singleton(feature) => {
                        implicit_singletons.push(ElementRef(feature));
                        (1, Some(1))
                    }
                };
                bounds.lower = bounds.lower.max(lower);
                bounds.upper = match (bounds.upper, upper) {
                    (Some(a), Some(b)) => Some(a.min(b)),
                    (a, b) => a.or(b),
                };
                if bounds.upper.is_some_and(|upper| bounds.lower > upper) {
                    return Err(CardinalityIssue::ConflictingConstraints);
                }
            }
            if !stamp.current(self) {
                return Err(CardinalityIssue::StaleEvidence);
            }
            Ok(bounds)
        })();
        if steps > crate::eval::MAX_STEPS {
            bounds = Err(CardinalityIssue::WorkLimit);
        }
        if bounds.is_err() {
            multiplicities.clear();
            implicit_singletons.clear();
        }
        CardinalityReport {
            bounds,
            multiplicities,
            implicit_singletons,
            steps,
        }
    }
}
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
enum Constraint {
    Range(usize),
    Singleton(usize),
}
struct Reader<'a> {
    raw: Arc<StoredStructure>,
    relations: TypeRelations,
    active: HashSet<usize>,
    known: HashMap<usize, Vec<Constraint>>,
    domains: HashSet<usize>,
    expressions: HashSet<usize>,
    universal_relationships: HashSet<usize>,
    steps: &'a mut usize,
}
impl Reader<'_> {
    fn members(&mut self, b: &Builder, owner: usize) -> Result<Vec<usize>, CardinalityIssue> {
        charge(self.steps, 1)?;
        if !self.raw.is_current(b) || self.raw.metadata_annotation_targets.contains(&owner) {
            return Err(CardinalityIssue::IncompleteProvider);
        }
        let domains = self
            .raw
            .membership_domains(b, self.steps)
            .ok_or(CardinalityIssue::InvalidRelationship)?;
        if !domains.owner_complete(owner) {
            return Err(CardinalityIssue::InvalidRelationship);
        }
        let relationships = semantic_ownership::owned_relationships(b, owner)
            .ok_or(CardinalityIssue::InvalidRelationship)?;
        charge(self.steps, relationships.len())?;
        let mut result = Vec::new();
        let mut seen = HashSet::new();
        for relationship in relationships.iter() {
            if !seen.insert(relationship) {
                return Err(CardinalityIssue::InvalidRelationship);
            }
            let relation = b
                .elements
                .get(relationship)
                .ok_or(CardinalityIssue::InvalidRelationship)?;
            if conforms(relation.ty, "Membership") {
                let member =
                    membership_evidence::member(b, &self.raw, owner, relationship, self.steps)
                        .ok_or(CardinalityIssue::InvalidRelationship)?;
                if conforms(relation.ty, "OwningMembership") {
                    result.push(member);
                }
            }
        }
        Ok(result)
    }
    fn constraints(
        &mut self,
        b: &mut Builder,
        owner: usize,
        depth: usize,
    ) -> Result<Vec<Constraint>, CardinalityIssue> {
        charge(self.steps, 1)?;
        if depth >= 64 || !self.active.insert(owner) {
            return Err(CardinalityIssue::CyclicDependency);
        }
        if let Some(known) = self.known.get(&owner) {
            charge(self.steps, known.len())?;
            self.active.remove(&owner);
            return Ok(known.clone());
        }
        let owned: Vec<_> = self
            .members(b, owner)?
            .into_iter()
            .filter(|&e| conforms(b.elements[e].ty, "Multiplicity"))
            .collect();
        if owned.len() > 1 {
            return Err(CardinalityIssue::InvalidRelationship);
        }
        let mut result: Vec<_> = owned.into_iter().map(Constraint::Range).collect();
        if result.is_empty() && self.implicit_singleton(b, owner)? {
            result.push(Constraint::Singleton(owner));
        }
        if result.is_empty() {
            let bases = self
                .relations
                .complete_direct_bases(b, owner, self.steps)
                .ok_or(CardinalityIssue::IncompleteProvider)?;
            let mut seen = HashSet::new();
            for base in bases {
                for domain in self.constraints(b, base, depth + 1)? {
                    charge(self.steps, 1)?;
                    if seen.insert(domain) {
                        result.push(domain);
                    }
                }
            }
        }
        self.active.remove(&owner);
        charge(self.steps, result.len())?;
        self.known.insert(owner, result.clone());
        Ok(result)
    }
    fn implicit_singleton(
        &mut self,
        b: &mut Builder,
        feature: usize,
    ) -> Result<bool, CardinalityIssue> {
        if b.default_cardinality(feature) != (1, Some(1)) {
            return Ok(false);
        }
        let membership = b.elements[feature]
            .owning_relationship
            .ok_or(CardinalityIssue::InvalidRelationship)?;
        let owner =
            semantic_ownership::checked_relationship_carrier(b, &self.raw, membership, self.steps)
                .flatten()
                .ok_or(CardinalityIssue::InvalidRelationship)?;
        if !conforms(b.elements[membership].ty, "FeatureMembership")
            || membership_evidence::member(b, &self.raw, owner, membership, self.steps)
                != Some(feature)
            || self.raw.metadata_annotation_targets.contains(&owner)
        {
            return Err(CardinalityIssue::InvalidRelationship);
        }
        let domains = self
            .raw
            .membership_domains(b, self.steps)
            .ok_or(CardinalityIssue::InvalidRelationship)?;
        if !domains.owner_complete(owner) {
            return Err(CardinalityIssue::InvalidRelationship);
        }
        let typing = self
            .raw
            .typing(b, self.steps)
            .ok_or(CardinalityIssue::InvalidRelationship)?;
        if typing.sources_incomplete {
            return Err(CardinalityIssue::InvalidRelationship);
        }
        let relationships = typing
            .relationships
            .get(&feature)
            .map_or(&[][..], Vec::as_slice);
        charge(self.steps, relationships.len())?;
        // Owned authored subsettings suppress the textual/default singleton.
        // The generated static suffix is not an authored declaration, and an
        // authored isImplied flag cannot impersonate that provenance.
        for &relationship in relationships {
            if relationship < b.explicit_len()
                && conforms(b.elements[relationship].ty, "Subsetting")
            {
                return Ok(false);
            }
        }
        Ok(true)
    }
    fn validate_domain(
        &mut self,
        b: &mut Builder,
        owner: usize,
        depth: usize,
    ) -> Result<(), CardinalityIssue> {
        charge(self.steps, 1)?;
        if depth >= 64 || !self.domains.insert(owner) {
            return Err(CardinalityIssue::CyclicDependency);
        }
        if !conforms(b.elements[owner].ty, "Multiplicity") {
            return Err(CardinalityIssue::InvalidRelationship);
        }
        let members = self.members(b, owner)?;
        if b.elements[owner].ty == "MultiplicityRange" {
            let bounds: Vec<_> = members
                .iter()
                .copied()
                .take_while(|&member| conforms(b.elements[member].ty, "Expression"))
                .collect();
            if !(1..=2).contains(&bounds.len())
                || members[bounds.len()..]
                    .iter()
                    .any(|&member| conforms(b.elements[member].ty, "Expression"))
            {
                return Err(CardinalityIssue::InvalidRelationship);
            }
            for (key, expected) in [
                ("lowerBound", (bounds.len() == 2).then_some(bounds[0])),
                ("upperBound", bounds.last().copied()),
            ] {
                if let Some(value) = b.elements[owner].props.get(key) {
                    if match expected {
                        Some(expected) => value.as_reference() != Some(b.elements[expected].id),
                        None => !value.is_null(),
                    } {
                        return Err(CardinalityIssue::InvalidRelationship);
                    }
                }
            }
            if let Some(value) = b.elements[owner].props.get("bound") {
                let values = value
                    .as_array()
                    .ok_or(CardinalityIssue::InvalidRelationship)?;
                charge(self.steps, values.len())?;
                if values.len() != bounds.len()
                    || values.iter().zip(&bounds).any(|(value, &expected)| {
                        value.as_reference() != Some(b.elements[expected].id)
                    })
                {
                    return Err(CardinalityIssue::InvalidRelationship);
                }
            }
        }
        for member in members {
            if conforms(b.elements[member].ty, "Expression") {
                match b.elements[member].ty {
                    "LiteralInteger" | "LiteralInfinity" => {
                        // Literal syntax has no payload relationships; imported
                        // relationship-bearing forms need their own proof.
                        if !b.elements[member].owned_relationships.is_empty() {
                            return Err(CardinalityIssue::UnsupportedBound);
                        }
                    }
                    _ => {
                        self.expressions.insert(member);
                    }
                }
            }
        }
        let typing = self
            .raw
            .typing(b, self.steps)
            .ok_or(CardinalityIssue::InvalidRelationship)?;
        if typing.sources_incomplete {
            return Err(CardinalityIssue::InvalidRelationship);
        }
        let relationships = semantic_ownership::owned_relationships(b, owner)
            .ok_or(CardinalityIssue::InvalidRelationship)?;
        charge(self.steps, relationships.len())?;
        let relationships: Vec<_> = relationships.iter().collect();
        let mut seen = HashSet::new();
        for relationship in relationships {
            if !seen.insert(relationship) {
                return Err(CardinalityIssue::InvalidRelationship);
            }
            let kind = b
                .elements
                .get(relationship)
                .ok_or(CardinalityIssue::InvalidRelationship)?
                .ty;
            if !conforms(kind, "Specialization") {
                continue;
            }
            if !matches!(kind, "Subsetting" | "Redefinition") {
                return Err(CardinalityIssue::IncompleteProvider);
            }
            if semantic_ownership::checked_relationship_carrier(
                b,
                &self.raw,
                relationship,
                self.steps,
            ) != Some(Some(owner))
            {
                return Err(CardinalityIssue::InvalidRelationship);
            }
            if !b.static_chain_row_current(relationship)
                || !b.result_redefinition_row_current(relationship)
                || !b.dynamic_evidence_current(owner)
            {
                return Err(CardinalityIssue::StaleEvidence);
            }
            let target = type_relations::endpoint(
                b,
                owner,
                relationship,
                &["specific", "subsettingFeature", "redefiningFeature"],
                &["general", "subsettedFeature", "redefinedFeature"],
                "Feature",
                self.steps,
            )
            .ok_or(CardinalityIssue::InvalidRelationship)?;
            if conforms(b.elements[target].ty, "Multiplicity") {
                self.validate_domain(b, target, depth + 1)?;
            } else if kind == "Subsetting"
                && self.relations.library_role(b, "Base::things", self.steps) == Some(target)
            {
                // Every Feature subsets the universal library feature. This
                // checked identity adds no integer-domain constraint; unrelated
                // non-Multiplicity targets are not silently discarded.
                self.universal_relationships.insert(relationship);
            } else {
                return Err(CardinalityIssue::InvalidRelationship);
            }
        }
        if typing
            .relationships
            .get(&owner)
            .is_some_and(|incoming| incoming.iter().any(|r| !seen.contains(r)))
        {
            return Err(CardinalityIssue::InvalidRelationship);
        }
        self.domains.remove(&owner);
        Ok(())
    }
}

impl Builder {
    /// Preserve the compatibility candidate order, but certify every membership
    /// and its inverse domain before it can establish absence of a redefinition.
    pub(crate) fn cardinality_feature_candidates(
        &mut self,
        e: usize,
        steps: &mut usize,
    ) -> Option<Vec<usize>> {
        let scope = *self.elem_scope.get(&e)?;
        let inherited = self.inherited_bindings(scope, true);
        if inherited.incomplete || inherited.truncated || self.recorded_lookup_incomplete {
            return None;
        }
        let raw = StoredStructure::for_query(self, steps)?;
        let domains = raw.membership_domains(self, steps)?;
        if !raw.ids_unique || !domains.owner_complete(e) {
            return None;
        }
        let own = semantic_ownership::owned_relationships(self, e)?;
        charge(
            steps,
            own.len().saturating_add(inherited.membership_order.len()),
        )
        .ok()?;
        let relationships: Vec<_> = own
            .iter()
            .chain(inherited.membership_order.iter().copied())
            .collect();
        let mut out = Vec::new();
        let mut seen = HashSet::new();
        for relationship in relationships {
            if !super::is_feature_membership(self.elements.get(relationship)?.ty) {
                continue;
            }
            let owner =
                semantic_ownership::checked_relationship_carrier(self, &raw, relationship, steps)??;
            if !domains.owner_complete(owner) {
                return None;
            }
            let member = membership_evidence::member(self, &raw, owner, relationship, steps)?;
            if !conforms(self.elements[member].ty, "Feature") {
                return None;
            }
            if seen.insert(member) {
                out.push(member);
            }
        }
        Some(out)
    }
    /// Complete raw inverse domain plus reciprocal, typed endpoint evidence.
    /// Stored isImplied flags never exempt authored rows from certification.
    fn cardinality_edges(
        &mut self,
        e: usize,
        redefinitions_only: bool,
        steps: &mut usize,
    ) -> Option<Vec<usize>> {
        if !self.dynamic_evidence_current(e) || !self.result_redefinition_evidence_current(e) {
            return None;
        }
        let raw = StoredStructure::for_query(self, steps)?;
        if !raw.ids_unique || !raw.is_current(self) {
            return None;
        }
        let typing = raw.typing(self, steps)?;
        if typing.sources_incomplete {
            return None;
        }
        let own = semantic_ownership::owned_relationships(self, e)?;
        let incoming = typing.relationships.get(&e).map_or(&[][..], Vec::as_slice);
        charge(
            steps,
            own.len().saturating_mul(2).saturating_add(incoming.len()),
        )
        .ok()?;
        let authored_owned_subsets = own
            .iter()
            .filter(|&relationship| {
                relationship < self.explicit_len()
                    && conforms(self.elements[relationship].ty, "Subsetting")
            })
            .count();
        let relationships: Vec<_> = own.iter().chain(incoming.iter().copied()).collect();
        let mut seen = HashSet::new();
        let mut targets = Vec::new();
        for relationship in relationships {
            if !seen.insert(relationship) {
                continue;
            }
            let kind = self.elements.get(relationship)?.ty;
            if !conforms(kind, "Subsetting") || (redefinitions_only && kind != "Redefinition") {
                continue;
            }
            if !matches!(kind, "Subsetting" | "Redefinition") {
                return None;
            }
            if !self.static_chain_row_current(relationship)
                || !self.result_redefinition_row_current(relationship)
            {
                return None;
            }
            let carrier =
                semantic_ownership::checked_relationship_carrier(self, &raw, relationship, steps)?;
            let target = type_relations::endpoint_with_carrier(
                self,
                e,
                carrier,
                relationship,
                &["specific", "subsettingFeature", "redefiningFeature"],
                &["general", "subsettedFeature", "redefinedFeature"],
                "Feature",
                steps,
            )?;
            if !targets.contains(&target) {
                targets.push(target);
            }
        }
        self.ensure_spec_index();
        let mut recorded_subsets = 0;
        let mut recorded_targets = Vec::new();
        if let Some(indices) = self.spec_index.as_ref()?.get(&e) {
            charge(steps, indices.len()).ok()?;
            for &index in indices {
                let kind = self.spec_targets[index].1;
                if matches!(kind, "Subsetting" | "Redefinition")
                    && (!redefinitions_only || kind == "Redefinition")
                {
                    recorded_subsets += 1;
                    let recorded = self.spec_resolved.get(index).copied().flatten()?;
                    if !targets.contains(&recorded) {
                        return None;
                    }
                    if !redefinitions_only {
                        charge(steps, recorded_targets.len()).ok()?;
                        if !recorded_targets.contains(&recorded) {
                            recorded_targets.push(recorded);
                        }
                    }
                }
            }
        }
        // Compatibility Feature-cardinality reads admit the recorded authored
        // specialization domain. In particular, a named Multiplicity's numeric
        // subsettings are not evidence for its own Feature cardinality. Keep
        // those unrecorded authored forms unknown even after raw certification;
        // centrally published relationships have their separate freshness proof.
        // Positional targets are applied separately, after structural singleton
        // defaults. Publishing them must not move them before that precedence.
        if !redefinitions_only && authored_owned_subsets != recorded_subsets {
            return None;
        }
        Some(if redefinitions_only {
            targets
        } else {
            recorded_targets
        })
    }
    pub(crate) fn cardinality_subset_targets(
        &mut self,
        e: usize,
        steps: &mut usize,
    ) -> Option<Vec<usize>> {
        self.cardinality_edges(e, false, steps)
    }
    pub(crate) fn cardinality_redefinition_targets(
        &mut self,
        e: usize,
        steps: &mut usize,
    ) -> Option<Vec<usize>> {
        let mut targets = self.cardinality_edges(e, true, steps)?;
        if (self.is_parameter(e)
            || self.elements[e]
                .props
                .get("isEnd")
                .and_then(|v| v.as_bool())
                == Some(true))
            && self.effective_positional_redefinitions().is_none()
            && !self.ensure_positional_redefinitions_with_budget(steps)
        {
            return None;
        }
        let positional = self.completed_positional_targets(e)?;
        charge(steps, positional.len()).ok()?;
        for &target in positional {
            if !targets.contains(&target) {
                targets.push(target);
            }
        }
        Some(targets)
    }
}

/// Collect only current graph operands from the shared checked invocation
/// provider. Recorded source syntax is not evidence after an imported row edit.
fn certified_operators(
    r: &mut ResolvedModel,
    roots: &HashSet<usize>,
    context: Option<usize>,
    steps: &mut usize,
) -> Result<crate::eval::CheckedMultiplicityExpressions, CardinalityIssue> {
    use sysmlv2_syntax::ast::BinaryOp;
    charge(steps, roots.len())?;
    let mut pending: Vec<_> = roots.iter().copied().collect();
    let mut seen = HashSet::new();
    let mut contextual_features: Option<(HashSet<usize>, HashSet<usize>)> = None;
    let mut operators = crate::eval::CheckedMultiplicityExpressions::default();
    let raw =
        StoredStructure::for_query(&mut r.b, steps).ok_or(CardinalityIssue::IncompleteProvider)?;
    while let Some(expression) = pending.pop() {
        charge(steps, 1)?;
        if !seen.insert(expression) {
            continue;
        }
        if raw.metadata_annotation_targets.contains(&expression)
            || r.b
                .metadata_of
                .get(&expression)
                .is_some_and(|m| !m.is_empty())
        {
            return Err(CardinalityIssue::IncompleteProvider);
        }
        // Contextual references follow FeatureReferenceExpression::evaluate(target),
        // not its separate model-level classification. Other expression kinds
        // retain the existing model-level admission requirement.
        if r.b.elements[expression].ty != "FeatureReferenceExpression" {
            require_model_level_value(r, expression, steps)?;
        }
        match r.b.elements[expression].ty {
            "LiteralInteger" | "LiteralInfinity" => continue,
            "FeatureReferenceExpression" => {
                certify_reference_domain(&r.b, &raw, expression, steps)?;
                // The referenced Feature is the first non-parameter member,
                // matching the shared model-level rule. A published result is
                // a ParameterMembership, not another reference target.
                let target = membership_evidence::first_unowned_member(
                    &mut r.b,
                    &raw,
                    expression,
                    "ParameterMembership",
                    "Feature",
                    None,
                    steps,
                )
                .ok_or(CardinalityIssue::InvalidRelationship)?;
                let selected = crate::eval::checked_multiplicity_reference_target(
                    &mut r.b, target, context, steps,
                )
                .ok_or(CardinalityIssue::IncompleteProvider)?;
                // Lexical references keep their model-level proof. A selected
                // Type member instead has a complete receiver/redefinition proof.
                if r.b
                    .owner_elem(target)
                    .is_none_or(|owner| !conforms(r.b.elements[owner].ty, "Type"))
                {
                    require_model_level_value(r, expression, steps)?;
                } else {
                    let receiver = context
                        .and_then(|scope| r.b.scope_owner(scope))
                        .ok_or(CardinalityIssue::IncompleteProvider)?;
                    // Active behavior inputs need an invocation/frame environment;
                    // a declaration default cannot stand in for supplied arguments.
                    if conforms(r.b.elements[receiver].ty, "Behavior") {
                        return Err(CardinalityIssue::UnsupportedBound);
                    }
                    if contextual_features.is_none() {
                        let projection =
                            r.b.checked_type_features(receiver, steps)
                                .map_err(|_| CardinalityIssue::IncompleteProvider)?;
                        charge(
                            steps,
                            projection
                                .features
                                .len()
                                .saturating_add(projection.directed_features.len()),
                        )?;
                        contextual_features = Some((
                            projection.features.into_iter().map(|e| e.0).collect(),
                            projection
                                .directed_features
                                .into_iter()
                                .map(|e| e.0)
                                .collect(),
                        ));
                    }
                    let (features, directed) = contextual_features.as_ref().unwrap();
                    if !features.contains(&selected) || directed.contains(&selected) {
                        return Err(CardinalityIssue::UnsupportedBound);
                    }
                }
                let (_, value) = membership_evidence::valuation(&r.b, &raw, selected, steps)
                    .flatten()
                    .ok_or(CardinalityIssue::UnsupportedBound)?;
                operators
                    .references
                    .insert(expression, (target, selected, value));
                pending.push(value);
                continue;
            }
            "OperatorExpression" => {}
            _ => return Err(CardinalityIssue::UnsupportedBound),
        }
        let report = r.invocation_binding_report_with_budget(ElementRef(expression), *steps);
        *steps = report.steps;
        let arguments = report
            .arguments
            .map_err(|_| CardinalityIssue::UnsupportedBound)?;
        let operator = match r.b.elements[expression]
            .props
            .get("operator")
            .and_then(|v| v.as_str())
        {
            Some("+") => BinaryOp::Add,
            Some("-") => BinaryOp::Sub,
            Some("*") => BinaryOp::Mul,
            Some("/") => BinaryOp::Div,
            Some("%") => BinaryOp::Rem,
            Some("^" | "**") => BinaryOp::Pow,
            _ => return Err(CardinalityIssue::UnsupportedBound),
        };
        charge(steps, arguments.bindings.len())?;
        let operands: Vec<_> = arguments
            .bindings
            .iter()
            .map(|binding| binding.value.0)
            .collect();
        if operands.len() != 2
            && !(operands.len() == 1 && matches!(operator, BinaryOp::Add | BinaryOp::Sub))
        {
            return Err(CardinalityIssue::UnsupportedBound);
        }
        pending.extend(operands.iter().copied());
        operators.operators.insert(expression, (operator, operands));
    }
    Ok(operators)
}

/// A contextual reference replaces only the model-level eligibility predicate,
/// never the complete inverse membership and current ownership evidence.
fn certify_reference_domain(
    b: &Builder,
    raw: &StoredStructure,
    expression: usize,
    steps: &mut usize,
) -> Result<(), CardinalityIssue> {
    if !raw.is_current(b)
        || !b.dynamic_evidence_current(expression)
        || !b.local_featuring_evidence_current(expression)
        || !b.result_redefinition_evidence_current(expression)
    {
        return Err(CardinalityIssue::StaleEvidence);
    }
    if raw.carrier(b, expression) != Some(None)
        || !raw
            .membership_domains(b, steps)
            .ok_or(CardinalityIssue::InvalidRelationship)?
            .owner_complete(expression)
    {
        return Err(CardinalityIssue::InvalidRelationship);
    }
    let relationships = semantic_ownership::owned_relationships(b, expression)
        .ok_or(CardinalityIssue::InvalidRelationship)?;
    charge(steps, relationships.len())?;
    let mut seen = HashSet::new();
    for relationship in relationships.iter() {
        if !seen.insert(relationship)
            || semantic_ownership::checked_relationship_carrier(b, raw, relationship, steps)
                != Some(Some(expression))
        {
            return Err(CardinalityIssue::InvalidRelationship);
        }
        if !b.static_chain_row_current(relationship)
            || !b.result_redefinition_row_current(relationship)
        {
            return Err(CardinalityIssue::StaleEvidence);
        }
        if conforms(b.elements[relationship].ty, "Membership") {
            membership_evidence::member(b, raw, expression, relationship, steps)
                .ok_or(CardinalityIssue::InvalidRelationship)?;
        }
    }
    Ok(())
}

fn require_model_level_value(
    r: &mut ResolvedModel,
    expression: usize,
    steps: &mut usize,
) -> Result<(), CardinalityIssue> {
    let proof = r.model_level_evaluability_with_budget(ElementRef(expression), *steps);
    *steps = proof.steps;
    if proof.classification == super::ModelLevelEvaluability::Evaluable {
        Ok(())
    } else {
        Err(CardinalityIssue::UnsupportedBound)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::model::{GraphFormat, Model};
    use serde_json::json;
    const LIB: &str = "standard library package Base { classifier Anything; feature things:Anything; } standard library package Occurrences { class Occurrence specializes Base::Anything; }";
    fn fixture(source: &str, format: GraphFormat) -> ResolvedModel {
        let mut m = Model::with_graph_format(format);
        assert!(
            m.add_library_source("bounds-library.kerml", LIB)
                .diagnostics
                .is_empty()
        );
        let unit = m.add_source("bounds.kerml", source);
        assert!(unit.diagnostics.is_empty(), "{:?}", unit.diagnostics);
        ResolvedModel::build(&m)
    }
    fn bounds(r: &mut ResolvedModel, name: &str) -> Result<CardinalityBounds, CardinalityIssue> {
        let e = r.resolve_qualified(name).unwrap();
        r.cardinality_report(e).bounds
    }
    #[test]
    fn checked_constraints_preserve_local_precedence_and_intersect_inheritance() {
        for format in [GraphFormat::LegacyV2, GraphFormat::CanonicalV3] {
            let mut r = fixture(
                "feature a[2..5]; feature b[3..7]; feature c subsets a,b; feature d[4] subsets c; feature bad[1] subsets c; feature zero[0]; feature conflict subsets a,zero;",
                format,
            );
            assert_eq!(
                bounds(&mut r, "a"),
                Ok(CardinalityBounds {
                    lower: 2,
                    upper: Some(5)
                })
            );
            assert_eq!(
                bounds(&mut r, "c"),
                Ok(CardinalityBounds {
                    lower: 3,
                    upper: Some(5)
                })
            );
            assert_eq!(
                bounds(&mut r, "d"),
                Ok(CardinalityBounds {
                    lower: 4,
                    upper: Some(4)
                })
            );
            // Cardinality selection is not specialization conformance validation.
            assert_eq!(
                bounds(&mut r, "bad"),
                Ok(CardinalityBounds {
                    lower: 1,
                    upper: Some(1)
                })
            );
            assert_eq!(
                bounds(&mut r, "conflict"),
                Err(CardinalityIssue::ConflictingConstraints)
            );
            let c = bounds(&mut r, "c").unwrap();
            assert_eq!(c.size(), None);
            assert_eq!(c.is_empty(), Some(false));
            assert_eq!(c.contains_index(3), Some(true));
            assert_eq!(c.contains_index(4), None);
            assert_eq!(c.contains_index(6), Some(false));
            assert_eq!(c.contains_index(0), Some(false));
        }
    }
    #[test]
    fn checked_named_domains_are_exact_and_cycles_remain_unknown() {
        let mut r = fixture(
            "multiplicity huge[9223372036854775809]; feature exact { multiplicity subsets huge; } multiplicity a subsets b; multiplicity b subsets a; feature cyclic {multiplicity subsets a;} feature infinity[*]; feature empty[0];",
            GraphFormat::CanonicalV3,
        );
        assert_eq!(
            bounds(&mut r, "exact").unwrap().size(),
            Some(9223372036854775809)
        );
        assert_eq!(
            bounds(&mut r, "infinity"),
            Ok(CardinalityBounds {
                lower: 0,
                upper: None
            })
        );
        assert_eq!(bounds(&mut r, "empty").unwrap().is_empty(), Some(true));
        assert_eq!(
            bounds(&mut r, "cyclic"),
            Err(CardinalityIssue::CyclicDependency)
        );
    }
    #[test]
    fn checked_range_inverse_membership_and_endpoint_aliases_cannot_be_hidden() {
        for mutation in 0..3 {
            let mut r = fixture(
                "multiplicity base[3]; feature a {multiplicity m subsets base;} feature other;",
                GraphFormat::CanonicalV3,
            );
            assert_eq!(bounds(&mut r, "a").unwrap().size(), Some(3));
            let a = r.resolve_qualified("a").unwrap().0;
            let m = r.resolve_qualified("a::m").unwrap().0;
            let other = r.resolve_qualified("other").unwrap().0;
            let member = r.b.elements[m].owning_relationship.unwrap();
            match mutation {
                0 => {
                    r.b.elements[a].owned_relationships = r.b.elements[a]
                        .owned_relationships
                        .iter()
                        .copied()
                        .filter(|&x| x != member)
                        .collect::<Vec<_>>()
                        .into()
                }
                1 => {
                    let id = r.b.elements[other].id;
                    r.b.elements[member]
                        .props
                        .insert("memberElement", json!({"@id": id.to_string()}));
                }
                _ => {
                    let edge = r.b.elements[m].owned_relationships[0];
                    let id = r.b.elements[other].id;
                    r.b.elements[edge]
                        .props
                        .insert("general", json!({"@id": id.to_string()}));
                }
            }
            assert_eq!(
                bounds(&mut r, "a"),
                Err(CardinalityIssue::InvalidRelationship),
                "mutation {mutation}"
            );
        }
    }
    #[test]
    fn checked_reference_bounds_and_budget_retry_do_not_publish_partial_success() {
        let mut r = fixture(
            "feature n=3; feature a[n]; feature b[2];",
            GraphFormat::LegacyV2,
        );
        assert_eq!(bounds(&mut r, "a").unwrap().size(), Some(3));
        let b = r.resolve_qualified("b").unwrap();
        let failed = r.cardinality_report_with_budget(b, crate::eval::MAX_STEPS);
        assert_eq!(failed.bounds, Err(CardinalityIssue::WorkLimit));
        assert!(failed.multiplicities.is_empty());
        assert_eq!(r.cardinality_report(b).bounds.unwrap().size(), Some(2));
    }
    const CONTEXTUAL_BOUNDS: &str = "class Parent {
        feature n=4; feature aliasValue=n;
        multiplicity dynamic[n];
        feature slots {multiplicity subsets dynamic;}
        feature direct[aliasValue];
    }
    class Child specializes Parent {
        feature n redefines Parent::n=6;
        feature slots redefines Parent::slots;
        feature direct redefines Parent::direct;
    }
    class Grandchild specializes Child {
        feature n redefines Child::n=9;
        feature slots redefines Child::slots;
        feature direct redefines Child::direct;
    }
    class Shadow specializes Parent {
        feature n=12; feature slots redefines Parent::slots;
    }";

    #[test]
    fn checked_contextual_references_follow_redefinition_identity() {
        for format in [GraphFormat::LegacyV2, GraphFormat::CanonicalV3] {
            let mut r = fixture(CONTEXTUAL_BOUNDS, format);
            for _ in 0..2 {
                for (name, size) in [
                    ("Parent::slots", 4),
                    ("Parent::direct", 4),
                    ("Child::slots", 6),
                    ("Child::direct", 6),
                    ("Grandchild::slots", 9),
                    ("Grandchild::direct", 9),
                    ("Shadow::slots", 4),
                ] {
                    let report = bounds(&mut r, name);
                    assert_eq!(
                        report
                            .unwrap_or_else(|e| panic!("{format:?} {name}: {e:?}"))
                            .size(),
                        Some(size)
                    );
                }
            }
            let slots = r.resolve_qualified("Child::slots").unwrap();
            assert_eq!(
                r.cardinality_report_with_budget(slots, crate::eval::MAX_STEPS)
                    .bounds,
                Err(CardinalityIssue::WorkLimit)
            );
            assert_eq!(r.cardinality_report(slots).bounds.unwrap().size(), Some(6));
        }
    }

    #[test]
    fn checked_contextual_references_preserve_library_replay_results() {
        use crate::{libcache::LibraryCache, prepared::PreparedLibrary};
        for format in [GraphFormat::LegacyV2, GraphFormat::CanonicalV3] {
            let mut base = Model::with_graph_format(format);
            base.add_library_source("bounds-library.kerml", LIB);
            base.add_library_source("contextual-bounds.kerml", CONTEXTUAL_BOUNDS);
            base.record_library_cache();
            ResolvedModel::build(&base);
            let cache =
                LibraryCache::from_bytes(&base.take_recorded_library_cache().unwrap().to_bytes())
                    .unwrap();
            let prepared = base.prepare_library().unwrap();
            let decoded =
                Arc::new(PreparedLibrary::from_bytes(&prepared.to_bytes(93).unwrap(), 93).unwrap());
            let mut expected = None;
            for mode in 0..4 {
                let mut model = Model::with_graph_format(format);
                match mode {
                    2 => Arc::clone(&prepared).install(&mut model).unwrap(),
                    3 => Arc::clone(&decoded).install(&mut model).unwrap(),
                    _ => {
                        model.add_library_source("bounds-library.kerml", LIB);
                        model.add_library_source("contextual-bounds.kerml", CONTEXTUAL_BOUNDS);
                        if mode == 1 {
                            model.set_library_cache(cache.clone());
                        }
                    }
                }
                let unit = model.add_source("user-bounds.kerml", "class User specializes Grandchild {feature slots redefines Grandchild::slots; feature direct redefines Grandchild::direct;}");
                assert!(unit.diagnostics.is_empty(), "{:?}", unit.diagnostics);
                let mut r = ResolvedModel::build(&model);
                let mut signatures = Vec::new();
                for name in ["User::slots", "User::direct"] {
                    let element = r.resolve_qualified(name).unwrap();
                    let report = r.cardinality_report(element);
                    assert_eq!(
                        report
                            .bounds
                            .unwrap_or_else(|e| panic!("{format:?} {mode} {name}: {e:?}"))
                            .size(),
                        Some(9)
                    );
                    signatures.push(
                        report
                            .multiplicities
                            .iter()
                            .map(|e| r.b.elements[e.0].id)
                            .collect::<Vec<_>>(),
                    );
                }
                match &expected {
                    None => expected = Some(signatures),
                    Some(expected) => assert_eq!(&signatures, expected, "{format:?} mode {mode}"),
                }
            }
        }
    }

    #[test]
    fn checked_contextual_reference_values_use_current_rows_and_complete_aliases() {
        for format in [GraphFormat::LegacyV2, GraphFormat::CanonicalV3] {
            for mutation in 0..3 {
                let mut r = fixture(CONTEXTUAL_BOUNDS, format);
                let selected = r.resolve_qualified("Child::n").unwrap().0;
                let value = r.b.elements[selected]
                    .owned_relationships
                    .iter()
                    .copied()
                    .find(|&rel| r.b.elements[rel].ty == "FeatureValue")
                    .unwrap();
                let literal = r.b.elements[value].children[0];
                assert_eq!(bounds(&mut r, "Child::slots").unwrap().size(), Some(6));
                r.b.elements[literal].props.insert("value", json!(7));
                assert_eq!(bounds(&mut r, "Child::slots").unwrap().size(), Some(7));
                match mutation {
                    0 => {
                        let id = r.b.elements[selected].id;
                        r.b.elements[value]
                            .props
                            .insert("memberElement", json!({"@id": id.to_string()}));
                    }
                    1 => r.b.elements[value].children.make_mut().clear(),
                    _ => {
                        let rel = r.b.elements[selected]
                            .owned_relationships
                            .iter()
                            .copied()
                            .find(|&rel| r.b.elements[rel].ty == "Redefinition")
                            .unwrap();
                        let id = r.b.elements[selected].id;
                        r.b.elements[rel]
                            .props
                            .insert("general", json!({"@id": id.to_string()}));
                    }
                }
                let slots = r.resolve_qualified("Child::slots").unwrap();
                let report = r.cardinality_report(slots);
                assert!(report.bounds.is_err(), "{format:?} mutation {mutation}");
                assert!(report.multiplicities.is_empty());
            }
        }
    }

    #[test]
    fn checked_contextual_references_reject_unlisted_inverse_membership_claims() {
        for key in ["membershipOwningNamespace", "source"] {
            let mut r = fixture(CONTEXTUAL_BOUNDS, GraphFormat::CanonicalV3);
            let slots = r.resolve_qualified("Child::slots").unwrap();
            assert_eq!(r.cardinality_report(slots).bounds.unwrap().size(), Some(6));
            let domain = r.resolve_qualified("Parent::dynamic").unwrap().0;
            let expression =
                r.b.owned_member_elems(domain, false)
                    .into_iter()
                    .find(|&e| r.b.elements[e].ty == "FeatureReferenceExpression")
                    .unwrap();
            let other = r.resolve_qualified("Shadow::n").unwrap().0;
            let membership = r.b.elements[other].owning_relationship.unwrap();
            let claim = json!({"@id": r.b.elements[expression].id.to_string()});
            r.b.elements[membership].props.insert(
                key,
                if key == "source" {
                    json!([claim])
                } else {
                    claim
                },
            );
            let report = r.cardinality_report(slots);
            assert_eq!(
                report.bounds,
                Err(CardinalityIssue::InvalidRelationship),
                "{key}"
            );
            assert!(report.multiplicities.is_empty());
        }
    }

    #[test]
    fn checked_contextual_references_reject_stale_published_receiver_edges() {
        let mut r = fixture(CONTEXTUAL_BOUNDS, GraphFormat::CanonicalV3);
        let slots = r.resolve_qualified("Child::slots").unwrap();
        assert_eq!(r.cardinality_report(slots).bounds.unwrap().size(), Some(6));
        r.implied_relationships(slots);
        assert_eq!(r.cardinality_report(slots).bounds.unwrap().size(), Some(6));
        let n = r.resolve_qualified("Child::n").unwrap().0;
        let relation = r.b.elements[n]
            .owned_relationships
            .iter()
            .copied()
            .find(|&rel| r.b.elements[rel].ty == "Redefinition")
            .unwrap();
        let own_id = r.b.elements[n].id;
        r.b.elements[relation]
            .props
            .insert("redefinedFeature", json!({"@id": own_id.to_string()}));
        let report = r.cardinality_report(slots);
        assert!(report.bounds.is_err());
        assert!(report.multiplicities.is_empty());
    }

    #[test]
    fn checked_contextual_references_keep_metadata_domains_qualified() {
        for on_expression in [false, true] {
            let mut r = fixture(CONTEXTUAL_BOUNDS, GraphFormat::CanonicalV3);
            let slots = r.resolve_qualified("Child::slots").unwrap();
            assert_eq!(r.cardinality_report(slots).bounds.unwrap().size(), Some(6));
            let target = if on_expression {
                let domain = r.resolve_qualified("Parent::dynamic").unwrap().0;
                r.b.owned_member_elems(domain, false)
                    .into_iter()
                    .find(|&e| r.b.elements[e].ty == "FeatureReferenceExpression")
                    .unwrap()
            } else {
                r.resolve_qualified("Child::n").unwrap().0
            };
            r.b.metadata_of.insert(target, vec![target]);
            assert!(r.cardinality_report(slots).bounds.is_err());
        }
    }

    #[test]
    fn checked_contextual_references_do_not_substitute_runtime_parameter_defaults() {
        let mut r = fixture(
            "function F {in n=4; in slots[n]; return result;}",
            GraphFormat::CanonicalV3,
        );
        assert!(bounds(&mut r, "F::slots").is_err());
    }

    #[test]
    fn checked_contextual_references_reject_ambiguous_and_cyclic_values() {
        for source in [
            "class Parent {feature n=4; feature slots[n];}
             class Child specializes Parent {feature choiceA redefines Parent::n=6; feature choiceB redefines Parent::n=7; feature slots redefines Parent::slots;}",
            "class Parent {feature n=4; feature slots[n];}
             class Child specializes Parent {feature n redefines Parent::n=n; feature slots redefines Parent::slots;}",
        ] {
            let mut r = fixture(source, GraphFormat::CanonicalV3);
            assert!(bounds(&mut r, "Child::slots").is_err());
        }
    }

    #[test]
    fn checked_formula_uses_current_graph_operands_and_rejects_stale_publication() {
        for mutation in 0..2 {
            let mut m = Model::with_graph_format(GraphFormat::CanonicalV3);
            m.add_library_source("bounds-library.kerml", "standard library package Base {classifier Anything; feature things:Anything;} standard library package Occurrences {class Occurrence specializes Base::Anything; feature occurrences:Occurrence subsets Base::things;} standard library package Performances {behavior Performance specializes Occurrences::Occurrence; function Evaluation specializes Performance {return result;} step performances:Performance subsets Occurrences::occurrences; expr evaluations:Evaluation subsets performances;} standard library package DataFunctions {function '+' {in a; in b; return r;} function '*' {in a; in b; return r;}} ");
            let unit = m.add_source("formula.kerml", "feature f[(1+2)];");
            assert!(unit.diagnostics.is_empty(), "{:?}", unit.diagnostics);
            let mut r = ResolvedModel::build(&m);
            let f = r.resolve_qualified("f").unwrap();
            let operator =
                r.b.elements
                    .iter()
                    .position(|e| e.ty == "OperatorExpression")
                    .unwrap();
            let two =
                r.b.elements
                    .iter()
                    .position(|e| {
                        e.ty == "LiteralInteger"
                            && matches!(e.props.get("value"), Some(crate::properties::Atom::Number(n)) if n.as_i64() == Some(2))
                    })
                    .unwrap();
            if mutation == 0 {
                r.b.elements[two].props.insert("value", json!(9));
            } else {
                r.b.elements[operator].props.insert("operator", json!("*"));
            }
            r.implied_relationships(f);
            let report = r.cardinality_report(f);
            assert_eq!(
                report.bounds.unwrap().size(),
                Some(if mutation == 0 { 10 } else { 2 })
            );
            // Same IDs and row count do not preserve a certificate after edits.
            r.b.elements[two].props.insert("value", json!(7));
            assert!(r.cardinality_report(f).bounds.is_err());
        }
    }

    #[test]
    fn checked_reference_bounds_follow_current_graph_valuations() {
        for format in [GraphFormat::LegacyV2, GraphFormat::CanonicalV3] {
            let mut r = fixture("feature n=3; feature m=n; feature a[m];", format);
            let literal =
                r.b.elements
                    .iter()
                    .position(|e| e.ty == "LiteralInteger")
                    .unwrap();
            r.b.elements[literal].props.insert("value", json!(9));
            assert_eq!(bounds(&mut r, "a").unwrap().size(), Some(9));
            r.b.elements[literal].props.insert("value", json!(12));
            assert_eq!(bounds(&mut r, "a").unwrap().size(), Some(12));
        }
    }

    #[test]
    fn checked_reference_bounds_ignore_published_result_memberships() {
        let mut r = fixture(
            "feature n=3; feature m=n; feature a[m];",
            GraphFormat::CanonicalV3,
        );
        let a = r.resolve_qualified("a").unwrap();
        assert_eq!(r.cardinality_report(a).bounds.unwrap().size(), Some(3));
        r.implied_relationships(a);
        let references: Vec<_> = r
            .user_elements()
            .filter(|&e| r.element_type(e) == "FeatureReferenceExpression")
            .collect();
        for reference in references {
            assert!(
                semantic_ownership::owned_relationships(&r.b, reference.0)
                    .unwrap()
                    .iter()
                    .any(|rel| r.b.elements[rel].ty == "ReturnParameterMembership")
            );
        }
        assert_eq!(r.cardinality_report(a).bounds.unwrap().size(), Some(3));
    }

    #[test]
    fn compatibility_cardinality_keeps_numeric_domains_separate_from_feature_bounds() {
        for format in [GraphFormat::LegacyV2, GraphFormat::CanonicalV3] {
            let mut r = fixture(
                "multiplicity four[4]; alias named for four; multiplicity chain subsets named; feature exact { multiplicity subsets chain; } feature base[2]; feature inherited subsets base;",
                format,
            );
            let four = r.resolve_qualified("four").unwrap();
            let chain = r.resolve_qualified("chain").unwrap();
            let exact = r.resolve_qualified("exact").unwrap();
            let base = r.resolve_qualified("base").unwrap();
            let inherited = r.resolve_qualified("inherited").unwrap();
            assert_eq!(r.effective_cardinality(four), Some((0, None)));
            assert_eq!(r.effective_cardinality(chain), None);
            assert_eq!(r.effective_cardinality(exact), Some((4, Some(4))));
            assert_eq!(r.cardinality_report(exact).bounds.unwrap().size(), Some(4));
            assert_eq!(r.effective_cardinality(inherited), Some((2, Some(2))));
            let mut exhausted = crate::eval::MAX_STEPS;
            assert_eq!(
                r.b.cardinality_subset_targets(inherited.0, &mut exhausted),
                None
            );
            assert_eq!(r.effective_cardinality(inherited), Some((2, Some(2))));
            let chain_edge = r.b.elements[chain.0].owned_relationships[0];
            // Authored flags cannot turn an unrecorded edge into a generated one.
            r.b.elements[chain_edge]
                .props
                .insert("isImplied", json!(true));
            assert_eq!(r.effective_cardinality(chain), None);
            let edge = r.b.elements[inherited.0].owned_relationships[0];
            let id = r.b.elements[base.0].id;
            r.b.elements[edge]
                .props
                .insert("specific", json!({"@id": id.to_string()}));
            assert_eq!(r.effective_cardinality(inherited), None);
        }
    }

    #[test]
    fn compatibility_structural_default_precedes_published_positional_bounds() {
        for format in [GraphFormat::LegacyV2, GraphFormat::CanonicalV3] {
            let mut model = Model::with_graph_format(format);
            let unit = model.add_source(
                "parameter-bounds.sysml",
                "calc def Base { in original[3]; return result; } calc def Child :> Base { in attribute renamed; return result; }",
            );
            assert!(unit.diagnostics.is_empty(), "{:?}", unit.diagnostics);
            let mut r = ResolvedModel::build(&model);
            let parameter = r.resolve_qualified("Child::renamed").unwrap();
            let original = r.resolve_qualified("Base::original").unwrap();
            assert_eq!(r.effective_cardinality(parameter), Some((1, Some(1))));
            r.implied_relationships(parameter);
            let generated = semantic_ownership::owned_relationships(&r.b, parameter.0)
                .unwrap()
                .iter()
                .find(|&relationship| {
                    relationship >= r.b.explicit_len()
                        && r.b.elements[relationship].ty == "Redefinition"
                })
                .unwrap();
            assert_eq!(
                r.b.cardinality_subset_targets(parameter.0, &mut 0),
                Some(Vec::new())
            );
            assert_eq!(r.effective_cardinality(parameter), Some((1, Some(1))));
            let id = r.b.elements[original.0].id;
            r.b.elements[generated]
                .props
                .insert("specific", json!({"@id": id.to_string()}));
            assert_eq!(r.effective_cardinality(parameter), None);
        }
    }

    #[test]
    fn compatibility_cardinality_edges_refuse_stale_dynamic_suffixes() {
        let mut r = fixture(
            "function F {in p;} feature call=F(1);",
            GraphFormat::CanonicalV3,
        );
        let invocation = r
            .user_elements()
            .find(|&e| r.element_type(e) == "InvocationExpression")
            .unwrap();
        r.implied_relationships(invocation);
        let parameter =
            r.b.elements
                .iter()
                .enumerate()
                .find_map(|(i, e)| {
                    (e.ty == "Redefinition" && i >= r.b.explicit_len())
                        .then(|| {
                            e.props
                                .get("owningRelatedElement")
                                .and_then(|v| v.as_reference())
                        })
                        .flatten()
                })
                .unwrap();
        let parameter = r.b.element_index_of_uuid(parameter).unwrap();
        assert!(r.b.cardinality_subset_targets(parameter, &mut 0).is_some());
        let rows = r.b.elements.observe_revision();
        r.b.lib_qnames.push((
            uuid::Uuid::new_v4(),
            vec!["changed loaded name evidence".into()],
        ));
        assert!(r.b.elements.revision().unwrap().same_as(&rows));
        assert!(r.b.cardinality_subset_targets(parameter, &mut 0).is_none());
    }

    #[test]
    fn compatibility_redefinition_and_candidate_readers_refuse_forged_inverse_evidence() {
        let mut r = fixture(
            "class C { feature a=2; feature b redefines a=3; }",
            GraphFormat::LegacyV2,
        );
        let c = r.resolve_qualified("C").unwrap().0;
        let a = r.resolve_qualified("C::a").unwrap().0;
        let b = r.resolve_qualified("C::b").unwrap().0;
        assert_eq!(
            r.b.cardinality_redefinition_targets(b, &mut 0),
            Some(vec![a])
        );
        let edge = r.b.elements[b]
            .owned_relationships
            .iter()
            .copied()
            .find(|&e| r.b.elements[e].ty == "Redefinition")
            .unwrap();
        let a_id = r.b.elements[a].id;
        r.b.elements[edge]
            .props
            .insert("specific", json!({"@id": a_id.to_string()}));
        assert_eq!(r.b.cardinality_redefinition_targets(b, &mut 0), None);
        let member = r.b.elements[a].owning_relationship.unwrap();
        r.b.elements[c].owned_relationships = r.b.elements[c]
            .owned_relationships
            .iter()
            .copied()
            .filter(|&e| e != member)
            .collect::<Vec<_>>()
            .into();
        assert_eq!(r.b.cardinality_feature_candidates(c, &mut 0), None);
    }
}
