//! Shared ownership projection for the materialized semantic suffix.
//!
//! Source rows and their identity derivation remain unchanged. This module
//! certifies only ownership of nodes produced by the materializer; it does not
//! certify that every normative implied family has been implemented.
use super::Builder;
use crate::metaclass::is_a;
use std::collections::HashMap;
use std::sync::Arc;

#[derive(Clone, Copy, serde::Serialize, serde::Deserialize)]
struct GeneratedNode {
    /// Relationships have a carrier; ordinary elements use their row backlink.
    relationship_owner: Option<usize>,
    /// Always an explicit declaration, not a synthetic scope or target owner.
    source_anchor: usize,
    added_to_source: bool,
    /// Static generic rows have no children or nested ownership.
    generic_relationship: bool,
}

/// Immutable after publication on Builder. There is one ownership view, shared
/// by derived reads, interchange emission and structural proof adapters.
#[derive(Clone, serde::Serialize, serde::Deserialize)]
pub(super) struct SemanticOwnership {
    from: usize,
    nodes: Vec<GeneratedNode>,
    /// Relationships added to an unchanged source row. Relationships physically
    /// owned by generated rows are NOT added here a second time.
    #[serde(serialize_with = "crate::prepared::sorted_map")]
    additions: HashMap<usize, Vec<usize>>,
    /// Positive owned-result projections only. Absence is unsupported/unknown,
    /// never proof that a normative result is absent or a family is complete.
    #[serde(serialize_with = "crate::prepared::sorted_map")]
    results: HashMap<usize, OwnedResult>,
    /// The prepared library's own view, over its materialized rows below
    /// `from` (`Builder::lib_implied_from..lib_boundary`): a lookup of a row
    /// below `from` reads it, and an owner's relationships list the rows it
    /// added before this view's. A prefix view has none, and a snapshot
    /// carries the prefix view alone.
    #[serde(skip)]
    prefix: Option<Arc<SemanticOwnership>>,
}

#[derive(Clone, Copy, serde::Serialize, serde::Deserialize)]
pub(super) struct OwnedResult {
    pub(super) membership: usize,
    pub(super) feature: usize,
}

/// Borrowed lists let checked callers charge the complete iteration before
/// allocating an output. Merely obtaining a row never clones its contents.
pub(super) struct Relationships<'a> {
    stored: &'a [usize],
    /// The rows the prepared library's view added to the owner, before any
    /// this build's did.
    prefix_additions: &'a [usize],
    additions: &'a [usize],
}
impl Relationships<'_> {
    pub(super) fn len(&self) -> usize {
        self.stored
            .len()
            .saturating_add(self.prefix_additions.len())
            .saturating_add(self.additions.len())
    }
    pub(super) fn iter(&self) -> impl Iterator<Item = usize> + '_ {
        self.stored
            .iter()
            .chain(self.prefix_additions)
            .chain(self.additions)
            .copied()
    }
}

/// One semantic owned-relationship projection shared by derived reads and
/// checked adapters. The caller charges len before copying or traversing it.
pub(super) fn owned_relationships(b: &Builder, owner: usize) -> Option<Relationships<'_>> {
    match (&b.semantic_ownership, b.implied_from) {
        (None, None) => Some(Relationships {
            stored: &b.elements.get(owner)?.owned_relationships,
            prefix_additions: b
                .prefix_ownership
                .as_ref()
                .filter(|_| !b.planning())
                .map_or(&[], |prefix| prefix.additions(owner)),
            additions: &[],
        }),
        (Some(view), Some(_)) if view.matches_suffix(b) => view.relationships(b, owner),
        _ => None,
    }
}

/// Checked carrier identity without conflating a standalone relationship's
/// carrier with its source. Typed endpoint readers validate source/target
/// aliases and generic arrays separately. An authored isImplied flag grants
/// no exemption; only the certified in-memory ownership view can add a carrier.
pub(super) fn checked_relationship_carrier(
    b: &Builder,
    raw: &super::structural_index::StoredStructure,
    relationship: usize,
    steps: &mut usize,
) -> Option<Option<usize>> {
    if !raw.ids_unique
        || !crate::metaclass::conforms(b.elements.get(relationship)?.ty, "Relationship")
    {
        return None;
    }
    match (&b.semantic_ownership, b.implied_from) {
        (Some(view), Some(_)) if view.matches_suffix(b) => {
            view.effective_carrier(b, raw, relationship, steps)
        }
        (None, None) => {
            if let Some(prefix) = b
                .prefix_ownership
                .as_ref()
                .filter(|prefix| prefix.contains(relationship))
            {
                return prefix.effective_carrier(b, raw, relationship, steps);
            }
            *steps = steps.saturating_add(1);
            if *steps > crate::eval::MAX_STEPS {
                return None;
            }
            raw.carrier(b, relationship)
        }
        _ => None,
    }
}

/// Whether this overlay adds a known omission to an owned-feature projection.
/// A true result only preserves a caller's previously audited evidence domain;
/// it does NOT certify normative family completeness for Constructor, Invocation,
/// FeatureChain, general Expression, or any other metaclass. Those family proofs
/// remain the caller's responsibility. FeatureReference remains false: the
/// local result/binding projection does not certify complete required connector
/// ancestry, featuring, or every existing-result expression.
pub(super) fn owned_feature_projection_complete(b: &Builder, owner: usize) -> bool {
    b.elements
        .get(owner)
        .is_some_and(|e| !is_a!(e, "FeatureReferenceExpression"))
}

impl SemanticOwnership {
    pub(super) fn clone_with_budget(&self, steps: &mut usize) -> Option<Self> {
        let work = self
            .nodes
            .len()
            .saturating_add(self.additions.capacity().saturating_mul(2))
            .saturating_add(self.results.capacity());
        *steps = steps.saturating_add(work);
        if *steps > crate::eval::MAX_STEPS {
            return None;
        }
        for relationships in self.additions.values() {
            *steps = steps.saturating_add(relationships.len());
            if *steps > crate::eval::MAX_STEPS {
                return None;
            }
        }
        Some(self.clone())
    }

    /// A view over the rows appended from `from`, layered over the prepared
    /// library's `prefix` view when the build has one.
    pub(super) fn new(from: usize, prefix: Option<Arc<SemanticOwnership>>) -> Self {
        Self {
            from,
            nodes: Vec::new(),
            additions: HashMap::new(),
            results: HashMap::new(),
            prefix,
        }
    }

    /// Generated records cover exactly the materialized suffix. This is a
    /// provenance shape check, not a substitute for raw carrier/alias validation.
    pub(super) fn matches_suffix(&self, b: &Builder) -> bool {
        b.implied_from == Some(self.from)
            && self.from.checked_add(self.nodes.len()) == Some(b.elements.len())
    }

    /// Register one newly appended node. The materializer admits endpoints and
    /// raw carriers BEFORE calling this; this is not an arbitrary payload owner
    /// override. Registration order must exactly match the append-only suffix.
    pub(super) fn register(
        &mut self,
        index: usize,
        relationship_owner: Option<usize>,
        source_anchor: usize,
        added_to_source: bool,
    ) -> Option<()> {
        if index != self.from.checked_add(self.nodes.len())?
            || source_anchor >= self.from
            || relationship_owner.is_some_and(|owner| owner >= index)
            || (added_to_source && relationship_owner.is_none_or(|owner| owner >= self.from))
        {
            return None;
        }
        self.nodes.push(GeneratedNode {
            relationship_owner,
            source_anchor,
            added_to_source,
            generic_relationship: false,
        });
        if added_to_source {
            self.additions
                .entry(relationship_owner?)
                .or_default()
                .push(index);
        }
        Some(())
    }

    /// Certify the existing static, childless generic relationship family.
    /// The checked carrier preserves this shape after later row mutations.
    pub(super) fn register_generic(&mut self, index: usize, owner: usize) -> Option<()> {
        self.register(index, Some(owner), owner, true)?;
        self.nodes.last_mut()?.generic_relationship = true;
        Some(())
    }

    /// Publish only after the complete admitted result subtree is registered.
    /// This certifies its ownership projection, not other expression obligations.
    pub(super) fn record_result(
        &mut self,
        expression: usize,
        membership: usize,
        feature: usize,
    ) -> Option<()> {
        if self.generated_relationship_owner(membership) != Some(expression)
            || !self.contains(feature)
            || self.results.contains_key(&expression)
        {
            return None;
        }
        self.results.insert(
            expression,
            OwnedResult {
                membership,
                feature,
            },
        );
        Some(())
    }

    /// Remove only a certified generated-result tail from a cloned view.
    /// The caller invalidates tail-indexed caches before replacing Builder rows.
    pub(super) fn without_result_tail(&self, boundary: usize) -> Option<Self> {
        let keep = boundary.checked_sub(self.from)?;
        if keep > self.nodes.len() {
            return None;
        }
        let mut view = self.clone();
        view.nodes.truncate(keep);
        view.additions.retain(|_, relationships| {
            relationships.retain(|&relationship| relationship < boundary);
            !relationships.is_empty()
        });
        view.results.clear();
        Some(view)
    }

    pub(super) fn result(&self, expression: usize) -> Option<OwnedResult> {
        self.results
            .get(&expression)
            .copied()
            .or_else(|| self.prefix.as_ref()?.result(expression))
    }

    pub(super) fn relationships<'a>(
        &'a self,
        b: &'a Builder,
        owner: usize,
    ) -> Option<Relationships<'a>> {
        Some(Relationships {
            stored: &b.elements.get(owner)?.owned_relationships,
            prefix_additions: self
                .prefix
                .as_ref()
                .filter(|_| !b.planning())
                .map_or(&[], |prefix| prefix.additions(owner)),
            additions: self.additions(owner),
        })
    }

    pub(super) fn additions(&self, owner: usize) -> &[usize] {
        self.additions.get(&owner).map_or(&[], Vec::as_slice)
    }

    /// Does not confuse a generated Feature with a Relationship. Proof adapters
    /// can distinguish a trusted generated carrier from malformed raw ownership.
    pub(super) fn generated_relationship_owner(&self, element: usize) -> Option<usize> {
        if element < self.from {
            return self.prefix.as_ref()?.generated_relationship_owner(element);
        }
        self.nodes
            .get(element.checked_sub(self.from)?)?
            .relationship_owner
    }

    /// Combine raw topology with a certified generated carrier. Never repair
    /// an invalid raw carrier or reinterpret arbitrary source rows as generated.
    pub(super) fn effective_carrier(
        &self,
        b: &Builder,
        raw: &super::structural_index::StoredStructure,
        relationship: usize,
        steps: &mut usize,
    ) -> Option<Option<usize>> {
        use super::structural_index::Carrier;
        *steps = steps.saturating_add(1);
        if *steps > crate::eval::MAX_STEPS {
            return None;
        }
        if !raw.ids_unique {
            return None;
        }
        if relationship < self.from {
            return match self
                .prefix
                .as_ref()
                .filter(|prefix| prefix.contains(relationship))
            {
                Some(prefix) => prefix.effective_carrier(b, raw, relationship, steps),
                None => raw.carrier(b, relationship),
            };
        }
        let Some(owner) = self.generated_relationship_owner(relationship) else {
            return raw.carrier(b, relationship);
        };
        if !crate::metaclass::conforms(b.elements.get(relationship)?.ty, "Relationship")
            || b.elements[relationship].owning_relationship.is_some()
            || self.source_anchor(relationship) >= self.from
        {
            return None;
        }
        b.elements.get(owner)?;
        b.elements.get(self.source_anchor(relationship))?;
        let node = self.nodes.get(relationship.checked_sub(self.from)?)?;
        if node.generic_relationship
            && (owner >= self.from
                || !node.added_to_source
                || !b.elements[relationship].children.is_empty()
                || !b.elements[relationship].owned_relationships.is_empty())
        {
            return None;
        }
        let added = node.added_to_source;
        match raw.raw_carrier(b, relationship)? {
            Carrier::Missing if added => {}
            Carrier::Unique(actual) if actual == owner && !added => {}
            _ => return None,
        }
        if b.elements
            .get(relationship)?
            .props
            .get("owningRelatedElement")
            .is_some_and(|value| value.as_reference() != Some(b.elements[owner].id))
        {
            return None;
        }
        Some(Some(owner))
    }

    pub(super) fn relationship_owners(&self) -> impl Iterator<Item = (usize, usize)> + '_ {
        self.prefix
            .iter()
            .flat_map(|prefix| prefix.prefix_relationship_owners())
            .chain(self.nodes.iter().enumerate().filter_map(|(offset, node)| {
                node.relationship_owner
                    .map(|owner| (self.from + offset, owner))
            }))
    }

    /// [`Self::relationship_owners`] of this view's own rows, as a prefix
    /// view lists them (a prefix view has no prefix of its own).
    fn prefix_relationship_owners(&self) -> Vec<(usize, usize)> {
        self.nodes
            .iter()
            .enumerate()
            .filter_map(|(offset, node)| {
                node.relationship_owner
                    .map(|owner| (self.from + offset, owner))
            })
            .collect()
    }

    pub(super) fn source_anchor(&self, element: usize) -> usize {
        if element < self.from {
            return self
                .prefix
                .as_ref()
                .map_or(element, |prefix| prefix.source_anchor(element));
        }
        element
            .checked_sub(self.from)
            .and_then(|offset| self.nodes.get(offset))
            .map_or(element, |node| node.source_anchor)
    }

    pub(super) fn contains(&self, element: usize) -> bool {
        if element < self.from {
            return self
                .prefix
                .as_ref()
                .is_some_and(|prefix| prefix.contains(element));
        }
        element
            .checked_sub(self.from)
            .is_some_and(|offset| offset < self.nodes.len())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn generated_nodes_have_distinct_carrier_and_source_roles() {
        let mut view = SemanticOwnership::new(10, None);
        assert_eq!(view.register(10, Some(2), 2, true), Some(()));
        assert_eq!(view.register(11, None, 2, false), Some(()));
        assert_eq!(view.register(12, Some(11), 2, false), Some(()));
        assert_eq!(view.additions(2), &[10]);
        assert!(view.additions(11).is_empty());
        assert_eq!(
            view.relationship_owners().collect::<Vec<_>>(),
            vec![(10, 2), (12, 11)]
        );
        assert_eq!(view.generated_relationship_owner(11), None);
        assert_eq!(view.source_anchor(12), 2);
        assert_eq!(view.source_anchor(8), 8);
        assert!(view.contains(11));
        assert!(!view.contains(13));
    }

    #[test]
    fn malformed_registration_is_atomic() {
        let mut view = SemanticOwnership::new(10, None);
        assert_eq!(view.register(11, Some(2), 2, true), None);
        assert_eq!(view.register(10, Some(10), 2, true), None);
        assert_eq!(view.register(10, None, 2, true), None);
        assert_eq!(view.register(10, Some(2), 10, true), None);
        assert!(!view.contains(10));
        assert!(view.additions(2).is_empty());
        assert_eq!(view.register(10, Some(2), 2, true), Some(()));
    }
    #[test]
    fn generic_carrier_keeps_its_childless_shape_for_every_adapter() {
        for corruption in 0..3 {
            let mut model = crate::model::Model::new();
            model.add_library_source("generic.kerml", "standard library package Base {classifier Anything;} standard library package Occurrences {class Occurrence specializes Base::Anything;}");
            model.add_source(
                "source.kerml",
                "class A; feature target=1; feature read=target;",
            );
            let mut r = super::super::ResolvedModel::build(&model);
            let a = r.resolve_qualified("A").unwrap();
            let relation = r.implied_relationships(a)[0].0;
            let view = r.b.semantic_ownership.clone().unwrap();
            let mut steps = 0;
            let raw =
                super::super::structural_index::StoredStructure::for_query(&mut r.b, &mut steps)
                    .unwrap();
            assert_eq!(
                checked_relationship_carrier(&r.b, &raw, relation, &mut steps),
                Some(Some(a.0))
            );
            match corruption {
                0 => r.b.elements[relation].children.push(a.0),
                1 => r.b.elements[relation].owned_relationships.push(relation),
                _ => r.b.elements[relation].owning_relationship = Some(relation),
            }
            let raw =
                super::super::structural_index::StoredStructure::for_query(&mut r.b, &mut steps)
                    .unwrap();
            assert!(view.matches_suffix(&r.b));
            assert_eq!(
                checked_relationship_carrier(&r.b, &raw, relation, &mut steps),
                None
            );
        }
    }
}
