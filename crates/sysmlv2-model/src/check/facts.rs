//! Read-only graph indexes shared by static validators. Constructed once per
//! analysis, so edits and library replay cannot leave stale semantic facts.
mod id_index;

use crate::{json::Builder, layered::LayeredVec, metaclass};
use std::{collections::HashSet, sync::OnceLock};
use sysmlv2_syntax::Span;

#[cfg(test)]
thread_local! {
    static SPAN_STEPS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

/// Ownership steps [`Facts::span`] has taken on the current thread. A
/// step moves from an element to its owner; resolving every element's
/// span takes at most one per element.
#[cfg(test)]
pub(crate) fn span_steps() -> usize {
    SPAN_STEPS.with(|c| c.get())
}

#[cfg(test)]
fn note_span_step() {
    SPAN_STEPS.with(|c| c.set(c.get() + 1));
}

#[cfg(not(test))]
fn note_span_step() {}

#[derive(Clone, Default, serde::Serialize, serde::Deserialize)]
pub(crate) struct Facts {
    ids: id_index::IdIndex,
    pub owner: LayeredVec<Option<usize>>,
    pub members: crate::flat::Rows<usize>,
    pub supers: crate::flat::Rows<usize>,
    contexts: crate::flat::Rows<usize>,
    outgoing: crate::flat::Rows<usize>,
    targets: crate::flat::Rows<(crate::properties::Key, usize)>,
    /// The first element this analysis added; [`Facts::span`] answers
    /// from `spans` for it and every later one.
    #[serde(skip)]
    span_start: usize,
    /// The span of each element from `span_start` on, resolved for all
    /// of them on the first query.
    #[serde(skip)]
    spans: OnceLock<Box<[Span]>>,
}
impl Facts {
    pub(super) fn outgoing_relationships(&self, e: usize) -> &[usize] {
        if e < self.outgoing.len() {
            &self.outgoing[e]
        } else {
            &[]
        }
    }
    pub(crate) fn contains_id(&self, id: &uuid::Uuid) -> bool {
        self.ids.get(id).is_some()
    }
    pub fn new(b: &mut Builder) -> Self {
        // The explicit elements only: the implied relationships the
        // derivation layer may have appended are not the model the checks
        // read.
        let n = b.explicit_len();
        let mut facts = b.library_facts.as_deref().cloned().unwrap_or_default();
        let start = facts.owner.len();
        let mut ids = std::mem::take(&mut facts.ids);
        for i in start..n {
            ids.insert(b.elem_id(i), i);
        }
        let mut targets = facts.targets;
        for e in b.elements.iter().take(n).skip(start) {
            targets.push(
                e.props
                    .references()
                    .filter_map(|(k, id)| ids.get(&id).copied().map(|t| (k, t)))
                    .collect(),
            );
        }
        // Only the new elements own new relationships; the library prefix
        // keeps its shared owner column.
        let mut relation_owner = vec![None; n - start];
        for (owner, e) in b.elements.iter().enumerate().take(n).skip(start) {
            for &rel in &e.owned_relationships {
                if rel >= start {
                    relation_owner[rel - start] = Some(owner);
                }
            }
        }
        let owner_of = |rel: usize| {
            if rel < start {
                facts.owner[rel]
            } else {
                relation_owner[rel - start]
            }
        };
        let mut owner = facts.owner.clone();
        for (i, e) in b.elements.iter().enumerate().take(n).skip(start) {
            owner.push(
                e.owning_relationship
                    .and_then(owner_of)
                    .or_else(|| owner_of(i)),
            );
        }
        let mut members = facts.members;
        members.resize(n);
        for (i, e) in b.elements.iter().enumerate().take(n).skip(start) {
            if e.owning_relationship
                .is_some_and(|rel| is(b, rel, "Membership"))
            {
                if let Some(o) = owner[i] {
                    members.row_mut(o).push(i);
                }
            }
        }
        let mut supers = facts.supers;
        supers.resize(n);
        let mut outgoing = facts.outgoing;
        for e in b.elements.iter().take(n).skip(start) {
            outgoing.push(e.owned_relationships.to_vec());
        }
        // Explicit about may add/remove semantic bases on a library target
        // without adding a source specialization. Empty values preserve touched
        // target history, so removals also refresh the prepared direct context.
        let mut changed: HashSet<usize> = b
            .metadata_about
            .keys()
            .copied()
            .filter(|&target| target < start)
            .collect();
        // Read resolved graph edges, including prefix metadata and standalone
        // relationships which do not all have a spec_targets entry.
        for (rel_index, rel) in b.elements.iter().enumerate().take(n).skip(start) {
            let keys = match rel.ty {
                "FeatureTyping" | "ConjugatedPortTyping" => ("typedFeature", "type"),
                "Subclassification" => ("subclassifier", "superclassifier"),
                "Subsetting" => ("subsettingFeature", "subsettedFeature"),
                "Redefinition" => ("redefiningFeature", "redefinedFeature"),
                "ReferenceSubsetting" => ("subsettingFeature", "referencedFeature"),
                "Specialization" => ("specific", "general"),
                "Conjugation" => ("conjugatedType", "originalType"),
                "TypeFeaturing" => ("featureOfType", "featuringType"),
                "FeatureChaining" => ("featureChained", "chainingFeature"),
                "FeatureInverting" => ("featureInverted", "invertingFeature"),
                _ => continue,
            };
            let target = |key: &str| {
                targets[rel_index]
                    .iter()
                    .find(|(k, _)| k.name() == key)
                    .map(|(_, t)| *t)
            };
            if let Some(e) = target(keys.0) {
                if !outgoing[e].contains(&rel_index) {
                    outgoing.row_mut(e).push(rel_index);
                }
            }
            if let (Some(e), Some(t)) = (target(keys.0), target(keys.1)) {
                if metaclass::conforms(rel.ty, "Specialization") && !supers[e].contains(&t) {
                    supers.row_mut(e).push(t);
                    if e < start {
                        changed.insert(e);
                    }
                }
            }
        }
        let mut contexts = facts.contexts;
        contexts.resize(n);
        for e in (start..n).chain(changed) {
            let mut ts = supers[e].to_vec();
            ts.extend(b.context_bases(e));
            ts.sort_unstable();
            ts.dedup();
            contexts.set(e, ts);
        }
        Self {
            targets,
            outgoing,
            contexts,
            ids,
            owner,
            members,
            supers,
            span_start: start,
            spans: OnceLock::new(),
        }
    }
    pub(crate) fn freeze(&mut self) {
        self.ids.freeze();
        self.targets.freeze();
        self.owner.freeze();
        self.members.freeze();
        self.supers.freeze();
        self.contexts.freeze();
        self.outgoing.freeze();
    }
    pub(crate) fn valid(&self, n: usize) -> bool {
        self.targets.len() == n
            && self.targets.iter().flatten().all(|(_, t)| *t < n)
            && self.owner.len() == n
            && self.members.len() == n
            && self.supers.len() == n
            && self.contexts.len() == n
            && self.outgoing.len() == n
            && self.ids.values().all(|&i| i < n)
            && self.owner.iter().all(|o| o.is_none_or(|i| i < n))
            && self
                .members
                .iter()
                .chain(self.supers.iter())
                .chain(self.contexts.iter())
                .chain(self.outgoing.iter())
                .flatten()
                .all(|&i| i < n)
    }
    pub fn target(&self, _b: &Builder, e: usize, key: &str) -> Option<usize> {
        self.targets[e]
            .iter()
            .find(|(k, _)| k.name() == key)
            .map(|(_, t)| *t)
    }
    pub fn relations(&self, b: &Builder, e: usize, kind: &str, key: &str) -> Vec<usize> {
        self.outgoing[e]
            .iter()
            .filter(|&&r| is(b, r, kind))
            .filter_map(|&r| self.target(b, r, key))
            .collect()
    }
    pub fn context(&self, e: usize) -> Vec<usize> {
        self.walk(e, &self.contexts)
    }
    pub fn closure(&self, e: usize) -> Vec<usize> {
        self.walk(e, &self.supers)
    }
    fn walk(&self, e: usize, edges: &crate::flat::Rows<usize>) -> Vec<usize> {
        let mut seen = HashSet::new();
        let mut out = Vec::new();
        let mut stack = vec![e];
        while let Some(e) = stack.pop() {
            if seen.insert(e) {
                out.push(e);
                stack.extend(edges[e].iter().copied());
            }
        }
        out
    }
    pub fn effective_kind(&self, b: &Builder, e: usize, kind: &str) -> bool {
        let mut seen = HashSet::new();
        let mut stack = vec![e];
        while let Some(e) = stack.pop() {
            if !seen.insert(e) {
                continue;
            }
            if is(b, e, kind) {
                return true;
            }
            stack.extend(
                self.supers[e]
                    .iter()
                    .copied()
                    .filter(|&t| is(b, t, "Feature")),
            );
            let chain: Vec<_> = self.outgoing[e]
                .iter()
                .copied()
                .filter(|&r| is(b, r, "FeatureChaining"))
                .collect();
            if chain
                .iter()
                .all(|&r| self.target(b, r, "chainingFeature").is_some())
            {
                if let Some(t) = chain
                    .last()
                    .and_then(|&r| self.target(b, r, "chainingFeature"))
                {
                    stack.push(t);
                }
            }
        }
        false
    }
    pub fn typed(&self, b: &Builder, e: usize) -> Vec<usize> {
        let mut result = Vec::new();
        let mut seen = HashSet::new();
        let mut stack = vec![e];
        while let Some(e) = stack.pop() {
            if !seen.insert(e) {
                continue;
            }
            for &r in &self.outgoing[e] {
                if is(b, r, "FeatureTyping") {
                    if let Some(t) = self.target(b, r, "type") {
                        if !result.contains(&t) {
                            result.push(t);
                        }
                    }
                } else if is(b, r, "Subsetting") {
                    for key in ["subsettedFeature", "redefinedFeature", "referencedFeature"] {
                        if let Some(t) = self.target(b, r, key) {
                            stack.push(t);
                        }
                    }
                } else if is(b, r, "Conjugation") {
                    if let Some(t) = self.target(b, r, "originalType") {
                        if is(b, t, "Feature") {
                            stack.push(t);
                        }
                    }
                }
            }
            // A partially unresolved chain has no known terminal feature.
            let chain: Vec<_> = b.elements[e]
                .owned_relationships
                .iter()
                .copied()
                .filter(|&rel| is(b, rel, "FeatureChaining"))
                .collect();
            if chain
                .iter()
                .all(|&rel| self.target(b, rel, "chainingFeature").is_some())
            {
                if let Some(t) = chain
                    .last()
                    .and_then(|&rel| self.target(b, rel, "chainingFeature"))
                {
                    stack.push(t);
                }
            }
        }
        result
            .iter()
            .copied()
            .filter(|t| {
                !result
                    .iter()
                    .any(|other| other != t && self.closure(*other).contains(t))
            })
            .collect()
    }
    /// Effective members, removing inherited features replaced by redefinitions.
    pub fn effective_members(&self, b: &Builder, e: usize) -> Vec<usize> {
        let own_ends = self.members[e]
            .iter()
            .filter(|&&m| flag(b, m, "isEnd"))
            .count();
        let all: Vec<_> = self
            .closure(e)
            .into_iter()
            .flat_map(|t| {
                let mut end_index = 0;
                self.members[t].iter().copied().filter(move |&m| {
                    if flag(b, m, "isEnd") {
                        end_index += 1;
                        if t != e && end_index <= own_ends {
                            return false;
                        }
                    }
                    true
                })
            })
            .collect();
        let all: Vec<_> = all
            .iter()
            .copied()
            .filter(|&m| {
                let role = b.elements[m].owning_relationship.map(|r| b.elements[r].ty);
                if !matches!(role, Some("SubjectMembership" | "ObjectiveMembership")) {
                    return true;
                }
                !all.iter().any(|&other| {
                    other != m
                        && b.elements[other]
                            .owning_relationship
                            .map(|r| b.elements[r].ty)
                            == role
                        && self.owner[other]
                            .zip(self.owner[m])
                            .is_some_and(|(a, z)| a != z && self.closure(a).contains(&z))
                })
            })
            .collect();
        let hidden: HashSet<_> = all.iter().flat_map(|&m| self.redefined(b, m)).collect();
        let mut seen = HashSet::new();
        all.into_iter()
            .filter(|m| !hidden.contains(m) && seen.insert(*m))
            .collect()
    }
    pub fn redefined(&self, b: &Builder, e: usize) -> Vec<usize> {
        let mut seen = HashSet::from([e]);
        let mut stack = self.relations(b, e, "Redefinition", "redefinedFeature");
        let mut out = Vec::new();
        while let Some(t) = stack.pop() {
            if seen.insert(t) {
                out.push(t);
                stack.extend(self.relations(b, t, "Redefinition", "redefinedFeature"));
            }
        }
        out
    }
    pub fn feature_target(&self, b: &Builder, e: usize) -> usize {
        let mut e = e;
        let mut seen = HashSet::new();
        while seen.insert(e) {
            let next = self.relations(b, e, "ReferenceSubsetting", "referencedFeature");
            if let [t] = next.as_slice() {
                e = *t;
            } else {
                break;
            }
        }
        e
    }
    pub fn named(&self, b: &Builder, e: usize, fqn: &str) -> bool {
        let mut current = Some(e);
        for name in fqn.rsplit("::") {
            let Some(i) = current else {
                return false;
            };
            if b.elements[i]
                .props
                .get("declaredName")
                .and_then(|v| v.as_str())
                != Some(name)
            {
                return false;
            }
            current = self.owner[i];
        }
        true
    }
    pub fn featuring(&self, b: &Builder, e: usize) -> Option<usize> {
        let rel = b.elements[e].owning_relationship?;
        if is(b, rel, "FeatureMembership") {
            self.owner[e]
        } else {
            None
        }
    }
    /// Where a finding on `e` is reported: its own declaration or member
    /// span, else the nearest owner's, else nowhere (the default span).
    pub fn span(&self, b: &Builder, e: usize) -> Span {
        if (self.span_start..self.owner.len()).contains(&e) {
            let spans = self.spans.get_or_init(|| self.resolve_spans(b));
            return spans[e - self.span_start];
        }
        self.walk_span(b, e)
    }

    /// [`Facts::span`] for every element from `span_start` on, each
    /// ownership step taken once: an element without a span of its own
    /// reports at its owner's, so a resolved owner answers for every
    /// element below it. Walking from each element separately costs its
    /// depth each time, which is quadratic in a nesting as deep as a
    /// lowered operator chain's: four ownership levels per operator.
    fn resolve_spans(&self, b: &Builder) -> Box<[Span]> {
        let (start, end) = (self.span_start, self.owner.len());
        let mut spans: Vec<Option<Span>> = vec![None; end - start];
        let mut on_path = vec![false; end - start];
        let mut path = Vec::new();
        for e in start..end {
            let mut current = Some(e);
            let span = loop {
                let Some(x) = current else {
                    break Span::default();
                };
                if !(start..end).contains(&x) {
                    // The library prefix owns only library elements, so
                    // its walk never comes back to the path.
                    break self.walk_span(b, x);
                }
                if let Some(span) = spans[x - start] {
                    break span;
                }
                if on_path[x - start] {
                    // An ownership cycle with no span anywhere on it.
                    break Span::default();
                }
                if let Some(&span) = b.decl_spans.get(&x).or_else(|| b.member_spans.get(&x)) {
                    spans[x - start] = Some(span);
                    break span;
                }
                on_path[x - start] = true;
                path.push(x);
                note_span_step();
                current = self.owner[x];
            };
            for x in path.drain(..) {
                spans[x - start] = Some(span);
                on_path[x - start] = false;
            }
        }
        spans.into_iter().map(Option::unwrap_or_default).collect()
    }

    /// [`Facts::span`] by walking up from `e` alone.
    fn walk_span(&self, b: &Builder, e: usize) -> Span {
        let mut current = Some(e);
        let mut seen = HashSet::new();
        while let Some(e) = current {
            if !seen.insert(e) {
                break;
            }
            if let Some(span) = b.decl_spans.get(&e).or_else(|| b.member_spans.get(&e)) {
                return *span;
            }
            note_span_step();
            current = self.owner[e];
        }
        Span::default()
    }
}
pub(super) fn is(b: &Builder, e: usize, kind: &str) -> bool {
    metaclass::conforms(b.elements[e].ty, kind)
}
pub(super) fn flag(b: &Builder, e: usize, key: &str) -> bool {
    b.elements[e].props.get(key).and_then(|x| x.as_bool()) == Some(true)
}

#[cfg(test)]
mod tests {
    use super::Facts;
    use crate::{json::ResolvedModel, model::Model};

    /// The spans resolved together answer exactly as a walk up from each
    /// element alone, also where ownership cycles, stops, or leaves the
    /// elements the analysis added for the library's.
    #[test]
    fn resolved_spans_answer_as_the_walk_from_each_element() {
        let mut base = Model::new();
        base.add_library_source("lib.kerml", "package L { class A { feature f = 1 + 2; } }");
        let prepared = base.prepare_library().unwrap();
        let mut model = Model::new();
        prepared.install(&mut model).unwrap();
        model.add_source(
            "user.sysml",
            "package P { part def D { attribute x = 1 + 2 * (3 - 4); } \
             part d : D { attribute :>> x = if true ? 1 else 2; } }",
        );
        assert!(!model.has_errors());
        let mut r = ResolvedModel::build(&model);
        let mut seed = 0x9e37_79b9_7f4a_7c15_u64;
        let mut next = move |bound: usize| {
            seed ^= seed << 13;
            seed ^= seed >> 7;
            seed ^= seed << 17;
            usize::try_from(seed % bound as u64).unwrap()
        };
        for round in 0..64 {
            let mut facts = Facts::new(&mut r.b);
            let (start, end) = (facts.span_start, facts.owner.len());
            assert!(0 < start && start < end, "the library is a prefix");
            // Rewire owners before the first query: to nothing, to the
            // element itself, or anywhere, the library included.
            for _ in 0..round {
                let e = start + next(end - start);
                facts.owner[e] = match next(4) {
                    0 => None,
                    1 => Some(e),
                    _ => Some(next(end)),
                };
            }
            for e in 0..end {
                assert_eq!(
                    facts.span(&r.b, e),
                    facts.walk_span(&r.b, e),
                    "element {e} in round {round}"
                );
            }
        }
    }
}
