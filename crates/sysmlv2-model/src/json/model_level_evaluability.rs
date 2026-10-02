//! Bounded evidence for normative model-level eligibility, separate from execution.
mod adapter;
use std::collections::{HashMap, HashSet};

/// A proof of the model-level eligibility rule, not a promise that evaluation
/// succeeds and not a complete model-validity certificate.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ModelLevelEvaluability {
    Evaluable,
    NotEvaluable,
    Unknown(ModelLevelEvaluabilityUnknown),
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub enum ModelLevelEvaluabilityUnknown {
    InvalidElement,
    MissingOrMalformedMembership,
    MissingOrMalformedValuation,
    IncompleteFeaturing,
    IncompleteSelfConformance,
    IncompleteCallee,
    IncompleteArgumentMapping,
    UnsupportedExpression,
    UnsupportedDirectionOrResult,
    CyclicOwnership,
    DepthLimit,
    WorkLimit,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub struct ModelLevelEvaluabilityReport {
    pub classification: ModelLevelEvaluability,
    pub steps: usize,
}
use ModelLevelEvaluability::{Evaluable as Yes, NotEvaluable as No, Unknown};
type Evidence<T> = Result<T, ModelLevelEvaluabilityUnknown>;
type Node = usize;
fn and(left: ModelLevelEvaluability, right: ModelLevelEvaluability) -> ModelLevelEvaluability {
    match (left, right) {
        (No, _) | (_, No) => No,
        (Yes, Yes) => Yes,
        (Unknown(reason), _) | (_, Unknown(reason)) => Unknown(reason),
    }
}
fn or(left: ModelLevelEvaluability, right: ModelLevelEvaluability) -> ModelLevelEvaluability {
    match (left, right) {
        (Yes, _) | (_, Yes) => Yes,
        (No, No) => No,
        (Unknown(reason), _) | (_, Unknown(reason)) => Unknown(reason),
    }
}
struct Budget {
    used: usize,
    limit: usize,
}
impl Budget {
    fn charge(&mut self, amount: usize) -> Evidence<()> {
        self.used = self.used.saturating_add(amount);
        if self.used > self.limit {
            Err(ModelLevelEvaluabilityUnknown::WorkLimit)
        } else {
            Ok(())
        }
    }
}
#[derive(Clone, Copy)]
enum Kind {
    Leaf,
    Forbidden,
    Reference,
    Invocation,
    Constructor,
    General,
}
struct ReferenceEvidence {
    referent: Node,
    self_conformance: ModelLevelEvaluability,
    expression: bool,
    metadata_owner: ModelLevelEvaluability,
    unfeatured: ModelLevelEvaluability,
    valuation: Evidence<Option<Node>>,
}
struct CallEvidence {
    function: ModelLevelEvaluability,
    // This is a COMPLETE argument projection, never a derived Vec whose
    // missing/unmapped entries have already been discarded.
    arguments: Evidence<Vec<Node>>,
}
struct OwnedFeatureEvidence {
    input_or_result: ModelLevelEvaluability,
    no_owned_features: ModelLevelEvaluability,
    no_valuation: ModelLevelEvaluability,
    result_expression: Evidence<Option<Node>>,
}
struct GeneralEvidence {
    all_specializations_implied: ModelLevelEvaluability,
    owned_features: Evidence<Vec<OwnedFeatureEvidence>>,
}
/// Every successful collection returned here must account for all source
/// relationships, including unresolved, external and contradictory entries.
trait EvidenceProvider {
    fn kind(&mut self, node: Node, budget: &mut Budget) -> Evidence<Kind>;
    fn leaf(&mut self, node: Node, budget: &mut Budget) -> Evidence<()>;
    fn reference(&mut self, node: Node, budget: &mut Budget) -> Evidence<ReferenceEvidence>;
    fn call(
        &mut self,
        node: Node,
        constructor: bool,
        budget: &mut Budget,
    ) -> Evidence<CallEvidence>;
    fn general(&mut self, node: Node, budget: &mut Budget) -> Evidence<GeneralEvidence>;
}
struct Tracking {
    entry_referents: usize,
    guards: HashMap<Node, bool>,
    owned_nodes: HashSet<Node>,
}
#[derive(Clone)]
struct Cached {
    guards: Vec<(Node, bool)>,
    owned_nodes: HashSet<Node>,
    classification: ModelLevelEvaluability,
}
struct Proof<P> {
    provider: P,
    budget: Budget,
    max_depth: usize,
    // Insertion level allows guard propagation without cloning the visited
    // set at each recursion. Referents are inserted and removed path-locally.
    visited: HashMap<Node, usize>,
    active_owned: HashSet<Node>,
    tracking: Vec<Tracking>,
    known: HashMap<(Node, usize), Vec<Cached>>,
}
impl<P: EvidenceProvider> Proof<P> {
    fn new(provider: P, work_limit: usize, max_depth: usize) -> Self {
        Self {
            provider,
            budget: Budget {
                used: 0,
                limit: work_limit,
            },
            max_depth,
            visited: HashMap::new(),
            active_owned: HashSet::new(),
            tracking: Vec::new(),
            known: HashMap::new(),
        }
    }
    fn report(mut self, node: Node) -> ModelLevelEvaluabilityReport {
        let classification = self.walk(node, 0);
        ModelLevelEvaluabilityReport {
            classification,
            steps: self.budget.used,
        }
    }
    fn visited_test(&mut self, node: Node) -> Evidence<bool> {
        self.budget.charge(self.tracking.len())?;
        let level = self.visited.get(&node).copied();
        for frame in &mut self.tracking {
            // A referent inserted inside this frame is constant local state,
            // not a condition on the frame's caller's visited set.
            if level.is_none_or(|level| level <= frame.entry_referents) {
                frame.guards.insert(node, level.is_some());
            }
        }
        Ok(level.is_some())
    }
    fn walk(&mut self, node: Node, depth: usize) -> ModelLevelEvaluability {
        if let Err(reason) = self.budget.charge(1) {
            return Unknown(reason);
        }
        if depth > self.max_depth {
            return Unknown(ModelLevelEvaluabilityUnknown::DepthLimit);
        }
        if let Some(variants) = self.known.get(&(node, depth)) {
            if let Err(reason) = self.budget.charge(
                variants
                    .iter()
                    .map(|cached| cached.guards.len() + cached.owned_nodes.len() + 1)
                    .sum(),
            ) {
                return Unknown(reason);
            }
        }
        let variants = self.known.get(&(node, depth)).cloned().unwrap_or_default();
        for cached in variants {
            if let Err(reason) = self.budget.charge(cached.guards.len()) {
                return Unknown(reason);
            }
            if cached.owned_nodes.is_disjoint(&self.active_owned)
                && cached
                    .guards
                    .iter()
                    .all(|(n, expected)| self.visited.contains_key(n) == *expected)
            {
                if let Err(reason) = self
                    .budget
                    .charge(cached.owned_nodes.len().saturating_mul(self.tracking.len()))
                {
                    return Unknown(reason);
                }
                for frame in &mut self.tracking {
                    frame.owned_nodes.extend(cached.owned_nodes.iter().copied());
                }
                for (n, _) in cached.guards {
                    if let Err(reason) = self.visited_test(n) {
                        return Unknown(reason);
                    }
                }
                return cached.classification;
            }
        }
        let kind = match self.provider.kind(node, &mut self.budget) {
            Ok(kind) => kind,
            Err(reason) => return Unknown(reason),
        };
        // Reference cycles have a normative visited-set rule. Other owning
        // expression cycles are invalid evidence and cannot become vacuous.
        let guarded = !matches!(kind, Kind::Reference);
        if guarded && !self.active_owned.insert(node) {
            return Unknown(ModelLevelEvaluabilityUnknown::CyclicOwnership);
        }
        if let Err(reason) = self.budget.charge(self.tracking.len()) {
            if guarded {
                self.active_owned.remove(&node);
            }
            return Unknown(reason);
        }
        if guarded {
            for frame in &mut self.tracking {
                frame.owned_nodes.insert(node);
            }
        }
        self.tracking.push(Tracking {
            entry_referents: self.visited.len(),
            guards: HashMap::new(),
            owned_nodes: if guarded {
                HashSet::from([node])
            } else {
                HashSet::new()
            },
        });
        let mut classification = self.uncached(node, kind, depth);
        let tracking = self.tracking.pop().expect("balanced eligibility proof");
        if guarded {
            self.active_owned.remove(&node);
        }
        if self.budget.used > self.budget.limit {
            classification = Unknown(ModelLevelEvaluabilityUnknown::WorkLimit);
        }
        if !matches!(classification, Unknown(_)) {
            let variants = self.known.entry((node, depth)).or_default();
            if variants.len() < 8 {
                variants.push(Cached {
                    guards: tracking.guards.into_iter().collect(),
                    owned_nodes: tracking.owned_nodes,
                    classification,
                });
            }
        }
        classification
    }
    fn uncached(&mut self, node: Node, kind: Kind, depth: usize) -> ModelLevelEvaluability {
        match kind {
            Kind::Forbidden => No,
            Kind::Leaf => self
                .provider
                .leaf(node, &mut self.budget)
                .map_or_else(Unknown, |_| Yes),
            Kind::Reference => self.reference(node, depth),
            Kind::Invocation | Kind::Constructor => {
                let constructor = matches!(kind, Kind::Constructor);
                let call = match self.provider.call(node, constructor, &mut self.budget) {
                    Ok(call) => call,
                    Err(reason) => return Unknown(reason),
                };
                let mut result = if constructor { Yes } else { call.function };
                match call.arguments {
                    Err(reason) => and(result, Unknown(reason)),
                    Ok(arguments) => {
                        for argument in arguments {
                            result = and(result, self.walk(argument, depth + 1));
                            if result == No {
                                break;
                            }
                        }
                        result
                    }
                }
            }
            Kind::General => {
                let general = match self.provider.general(node, &mut self.budget) {
                    Ok(general) => general,
                    Err(reason) => return Unknown(reason),
                };
                let mut result = general.all_specializations_implied;
                if result == No {
                    return No;
                }
                let features = match general.owned_features {
                    Ok(features) => features,
                    Err(reason) => return and(result, Unknown(reason)),
                };
                for feature in features {
                    let plain = and(
                        feature.input_or_result,
                        and(feature.no_owned_features, feature.no_valuation),
                    );
                    let result_expression = match feature.result_expression {
                        Ok(Some(child)) if plain != Yes => self.walk(child, depth + 1),
                        Ok(Some(_)) => Yes,
                        Ok(None) => No,
                        Err(reason) => Unknown(reason),
                    };
                    result = and(result, or(plain, result_expression));
                    if result == No {
                        break;
                    }
                }
                result
            }
        }
    }
    fn reference(&mut self, node: Node, depth: usize) -> ModelLevelEvaluability {
        let data = match self.provider.reference(node, &mut self.budget) {
            Ok(data) => data,
            Err(reason) => return Unknown(reason),
        };
        if data.self_conformance == Yes {
            return Yes;
        }
        match self.visited_test(data.referent) {
            Err(reason) => return Unknown(reason),
            Ok(true) => return or(data.self_conformance, No),
            Ok(false) => {}
        }
        self.visited.insert(data.referent, self.visited.len() + 1);
        // These are OCL alternatives. A failed Expression branch must not
        // suppress the metadata-owner or unfeatured-valuation alternatives.
        let mut alternatives = data.metadata_owner;
        if alternatives != Yes && data.expression {
            alternatives = or(alternatives, self.walk(data.referent, depth + 1));
        }
        if alternatives != Yes && data.unfeatured != No {
            let valuation = match data.valuation {
                Ok(None) => Yes,
                Ok(Some(value)) => self.walk(value, depth + 1),
                Err(reason) => Unknown(reason),
            };
            alternatives = or(alternatives, and(data.unfeatured, valuation));
        }
        self.visited.remove(&data.referent);
        or(alternatives, data.self_conformance)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[derive(Clone)]
    enum MockNode {
        Leaf,
        Forbidden,
        Reference {
            referent: Node,
            recursive: bool,
            metadata: bool,
            valuation: Evidence<Option<Node>>,
            unfeatured: ModelLevelEvaluability,
        },
        Call(Evidence<Vec<Node>>, ModelLevelEvaluability),
        Result(Node),
    }
    struct Mock(HashMap<Node, MockNode>);
    impl EvidenceProvider for Mock {
        fn kind(&mut self, node: Node, _: &mut Budget) -> Evidence<Kind> {
            Ok(
                match self
                    .0
                    .get(&node)
                    .ok_or(ModelLevelEvaluabilityUnknown::InvalidElement)?
                {
                    MockNode::Leaf => Kind::Leaf,
                    MockNode::Forbidden => Kind::Forbidden,
                    MockNode::Reference { .. } => Kind::Reference,
                    MockNode::Call(..) => Kind::Invocation,
                    MockNode::Result(_) => Kind::General,
                },
            )
        }
        fn leaf(&mut self, _: Node, _: &mut Budget) -> Evidence<()> {
            Ok(())
        }
        fn reference(&mut self, node: Node, _: &mut Budget) -> Evidence<ReferenceEvidence> {
            let MockNode::Reference {
                referent,
                recursive,
                metadata,
                valuation,
                unfeatured,
            } = self.0[&node].clone()
            else {
                panic!()
            };
            Ok(ReferenceEvidence {
                referent,
                self_conformance: No,
                expression: recursive,
                metadata_owner: if metadata { Yes } else { No },
                unfeatured,
                valuation,
            })
        }
        fn call(&mut self, node: Node, _: bool, _: &mut Budget) -> Evidence<CallEvidence> {
            let MockNode::Call(arguments, function) = self.0[&node].clone() else {
                panic!()
            };
            Ok(CallEvidence {
                function,
                arguments,
            })
        }
        fn general(&mut self, node: Node, _: &mut Budget) -> Evidence<GeneralEvidence> {
            let MockNode::Result(child) = self.0[&node] else {
                panic!()
            };
            Ok(GeneralEvidence {
                all_specializations_implied: Yes,
                owned_features: Ok(vec![OwnedFeatureEvidence {
                    input_or_result: No,
                    no_owned_features: Yes,
                    no_valuation: Yes,
                    result_expression: Ok(Some(child)),
                }]),
            })
        }
    }
    fn proof(nodes: impl IntoIterator<Item = (Node, MockNode)>) -> Proof<Mock> {
        Proof::new(Mock(nodes.into_iter().collect()), 10000, 128)
    }
    fn reference(referent: Node, valuation: Evidence<Option<Node>>) -> MockNode {
        MockNode::Reference {
            referent,
            recursive: false,
            metadata: false,
            valuation,
            unfeatured: Yes,
        }
    }
    #[test]
    fn unknown_dependencies_do_not_become_vacuous_positive() {
        assert_eq!(
            proof([(
                0,
                reference(
                    9,
                    Err(ModelLevelEvaluabilityUnknown::MissingOrMalformedValuation)
                )
            )])
            .report(0)
            .classification,
            Unknown(ModelLevelEvaluabilityUnknown::MissingOrMalformedValuation)
        );
        assert_eq!(
            proof([(
                0,
                MockNode::Call(
                    Err(ModelLevelEvaluabilityUnknown::IncompleteArgumentMapping),
                    Yes
                )
            )])
            .report(0)
            .classification,
            Unknown(ModelLevelEvaluabilityUnknown::IncompleteArgumentMapping)
        );
        assert_eq!(
            proof([(
                0,
                MockNode::Call(
                    Err(ModelLevelEvaluabilityUnknown::IncompleteArgumentMapping),
                    No
                )
            )])
            .report(0)
            .classification,
            No
        );
    }
    #[test]
    fn reference_alternatives_are_or_not_expression_else_if() {
        let root = MockNode::Reference {
            referent: 1,
            recursive: true,
            metadata: false,
            valuation: Ok(None),
            unfeatured: Yes,
        };
        assert_eq!(
            proof([(0, root), (1, MockNode::Forbidden)])
                .report(0)
                .classification,
            Yes
        );
    }
    #[test]
    fn sibling_references_share_no_path_local_visited_state() {
        let report = proof([
            (0, MockNode::Call(Ok(vec![1, 2]), Yes)),
            (1, reference(9, Ok(Some(3)))),
            (2, reference(9, Ok(Some(3)))),
            (3, MockNode::Leaf),
        ])
        .report(0);
        assert_eq!(report.classification, Yes);
        assert_eq!(
            proof([(0, reference(9, Ok(Some(0))))])
                .report(0)
                .classification,
            No
        );
    }
    #[test]
    fn completed_cache_is_guarded_by_visited_referents() {
        let mut proof = proof([(0, reference(9, Ok(None)))]);
        proof.visited.insert(9, 1);
        assert_eq!(proof.walk(0, 0), No);
        proof.visited.remove(&9);
        assert_eq!(proof.walk(0, 0), Yes);
        proof.visited.insert(9, 1);
        assert_eq!(proof.walk(0, 0), No);
    }
    #[test]
    fn ownership_cycle_cannot_reuse_an_unrelated_cached_success() {
        let mut proof = proof([(0, MockNode::Result(1)), (1, MockNode::Leaf)]);
        assert_eq!(proof.walk(0, 0), Yes);
        proof.active_owned.insert(1);
        assert_eq!(
            proof.walk(0, 0),
            Unknown(ModelLevelEvaluabilityUnknown::CyclicOwnership)
        );
    }
    #[test]
    fn budget_checks_precede_cache_and_do_not_poison_retry() {
        let mut proof = proof([(0, MockNode::Leaf)]);
        assert_eq!(proof.walk(0, 0), Yes);
        proof.budget.used = proof.budget.limit;
        assert_eq!(
            proof.walk(0, 0),
            Unknown(ModelLevelEvaluabilityUnknown::WorkLimit)
        );
        proof.budget.used = 0;
        assert_eq!(proof.walk(0, 0), Yes);
        assert_eq!(
            proof.walk(0, 129),
            Unknown(ModelLevelEvaluabilityUnknown::DepthLimit)
        );
    }
}
