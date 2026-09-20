//! Type-operation results and the evaluability residue over the resolved
//! model: the unioning, intersecting and differencing types and their
//! relationship ends, an association's related types, a connector's
//! default featuring type, and `isModelLevelEvaluable`. Each function
//! documents the specification rule it implements; the dispatch is in
//! `derived.rs`.

use super::derived::Reference;
use super::{ElementRef, ResolvedModel};
use std::collections::HashSet;

/// The library packages whose functions the KerML concrete syntax names
/// as model-level evaluable (clause 7.4.10). The clause lists a subset of
/// each package's functions; every function of the three packages counts
/// here, an over-approximation recorded in the API reference.
const EVALUABLE_FUNCTION_PACKAGES: &[&str] =
    &["BaseFunctions", "DataFunctions", "ControlFunctions"];

impl ResolvedModel {
    // ---- type operations ----

    /// `Type::unioningType = ownedUnioning.unioningType` and its
    /// intersecting/differencing twins: the targets of the owned
    /// relationships of `kind`, under `key`.
    pub(super) fn d_operation_types(
        &mut self,
        e: ElementRef,
        kind: &str,
        key: &str,
    ) -> Vec<Reference> {
        self.ensure_by_id();
        self.owned_relationships_of_kind(e, kind)
            .into_iter()
            .filter_map(|r| {
                self.b.elements[r.0]
                    .props
                    .get(key)
                    .and_then(|atom| self.reference_of(atom))
            })
            .collect()
    }

    // ---- associations ----

    /// `Association::relatedType = associationEnd.type`, in end order — a
    /// sequence (`isUnique = false`: a binary association over one type
    /// relates it twice), each end's types, targets outside the model
    /// included. `sourceType` is its first, `targetType` the rest as an
    /// ordered set.
    pub(super) fn d_related_types(&mut self, e: ElementRef) -> Vec<Reference> {
        let features = self.d_features(e);
        let ends = self.d_ends(features);
        let mut out: Vec<Reference> = Vec::new();
        for end in ends {
            out.extend(self.d_types(end));
        }
        out
    }

    /// `Association::targetType = relatedType->subSequence(2, size)->asOrderedSet()`.
    pub(super) fn d_target_types(&mut self, e: ElementRef) -> Vec<Reference> {
        let mut out: Vec<Reference> = Vec::new();
        for t in self.d_related_types(e).into_iter().skip(1) {
            if !out.contains(&t) {
                out.push(t);
            }
        }
        out
    }

    // ---- featuring ----

    /// `Feature::featuringType` at the passthrough level: the owning type,
    /// the owned TypeFeaturings' targets, and — for a chained feature —
    /// the first chaining feature's featuring types; elements of the model
    /// only (a featuring type outside the model cannot enter a
    /// specialization test).
    pub(super) fn d_featuring_types(&mut self, f: ElementRef) -> Vec<ElementRef> {
        self.featuring_types_walk(f, 0)
    }

    fn featuring_types_walk(&mut self, f: ElementRef, depth: usize) -> Vec<ElementRef> {
        self.ensure_by_id();
        let mut out: Vec<ElementRef> = Vec::new();
        if let Some(o) = self.d_owning_type(f) {
            out.push(o);
        }
        for tf in self.owned_relationships_of_kind(f, "TypeFeaturing") {
            if let Some(t) = self.prop_target(tf.0, "featuringType") {
                if !out.contains(&ElementRef(t)) {
                    out.push(ElementRef(t));
                }
            }
        }
        if depth < 32 {
            if let Some(Reference::Element(first)) = self.d_chaining_features(f).into_iter().next()
            {
                for t in self.featuring_types_walk(first, depth + 1) {
                    if !out.contains(&t) {
                        out.push(t);
                    }
                }
            }
        }
        out
    }

    /// `closure(featuringType)` over a set of features and types: every
    /// type featuring them directly or through the owning types of those
    /// types' own features — the owning-type chain, in discovery order.
    fn featuring_closure(&mut self, roots: &[ElementRef]) -> Vec<ElementRef> {
        let mut out: Vec<ElementRef> = Vec::new();
        let mut frontier: Vec<ElementRef> = roots.to_vec();
        let mut seen: HashSet<usize> = roots.iter().map(|r| r.0).collect();
        while let Some(x) = frontier.pop() {
            let next: Vec<ElementRef> = if self.is_kind(x, "Feature") {
                self.d_featuring_types(x)
            } else {
                // A Type that is not a Feature is featured by nothing.
                Vec::new()
            };
            for t in next {
                // A type reached for the first time is expanded; a root
                // reached transitively (the OCL closure includes it then)
                // joins the result without re-expansion.
                if seen.insert(t.0) {
                    frontier.push(t);
                }
                if !out.contains(&t) {
                    out.push(t);
                }
            }
        }
        out
    }

    /// Whether `t` specializes `general`, through the explicit
    /// specializations of the model (`t` itself counts). Three clauses of
    /// the normative `supertypes`/`specializes` are omitted, inert in
    /// this lowering's featuring types: a Feature's `featureTarget` as a
    /// supertype (a chain feature is never a featuring type here), a
    /// conjugated type's `conjugator.originalType`, and
    /// `Feature::isCompatibleWith`'s shared-redefinition clause.
    pub(super) fn specializes(&mut self, t: ElementRef, general: ElementRef) -> bool {
        let mut seen: HashSet<usize> = HashSet::new();
        let mut stack = vec![t];
        while let Some(x) = stack.pop() {
            if x == general {
                return true;
            }
            if !seen.insert(x.0) {
                continue;
            }
            for r in self.d_owned_specializations(x, "Specialization") {
                if let Some(Reference::Element(g)) = self.relationship_ends(r).1.into_iter().next()
                {
                    stack.push(g);
                }
            }
        }
        false
    }

    /// `Feature::isFeaturedWithin(type)` for a non-null type: every
    /// featuring type of `f` is one `t` specializes; or `f` is variable and
    /// `t` specializes its owning type; or `f` is a chain whose first link
    /// is variable and `t` specializes that link's owning type.
    fn is_featured_within(&mut self, f: ElementRef, t: ElementRef) -> bool {
        let featuring = self.d_featuring_types(f);
        if featuring.iter().all(|&ft| self.specializes(t, ft)) {
            return true;
        }
        if self.prop_bool(f.0, "isVariable") {
            if let Some(o) = self.d_owning_type(f) {
                if self.specializes(t, o) {
                    return true;
                }
            }
        }
        if let Some(Reference::Element(first)) = self.d_chaining_features(f).into_iter().next() {
            if self.prop_bool(first.0, "isVariable") {
                if let Some(o) = self.d_owning_type(first) {
                    if self.specializes(t, o) {
                        return true;
                    }
                }
            }
        }
        false
    }

    /// `Connector::defaultFeaturingType`: of the types featuring the related
    /// features directly or indirectly, those every related feature is
    /// featured within; of those, the innermost — one no other of them is
    /// featured within — first. Null when a related feature is outside the
    /// model (its featuring is not visible) or there are none.
    pub(super) fn d_default_featuring_type(&mut self, e: ElementRef) -> Option<ElementRef> {
        let related: Vec<ElementRef> = self
            .d_related_features(e)
            .into_iter()
            .map(|r| r.element())
            .collect::<Option<Vec<_>>>()?;
        if related.is_empty() {
            return None;
        }
        let candidates = self.featuring_closure(&related);
        let mut common: Vec<ElementRef> = Vec::new();
        for t in candidates {
            let mut all = true;
            for &f in &related {
                if !self.is_featured_within(f, t) {
                    all = false;
                    break;
                }
            }
            if all {
                common.push(t);
            }
        }
        // Innermost: reject t1 when another common type's closure reaches it.
        let mut nearest: Vec<ElementRef> = Vec::new();
        for &t1 in &common {
            let mut outer = false;
            for &t2 in &common {
                if t2 != t1 && self.featuring_closure(&[t2]).contains(&t1) {
                    outer = true;
                    break;
                }
            }
            if !outer {
                nearest.push(t1);
            }
        }
        nearest.into_iter().next()
    }

    // ---- model-level evaluability ----

    /// `Expression::isModelLevelEvaluable = modelLevelEvaluable(Set{})`,
    /// the KerML walk: literals, null and metadata-access expressions are
    /// evaluable; an invocation when its arguments are and its function is
    /// a model-level evaluable library function; a constructor when its
    /// arguments are; a feature reference when its referent is
    /// `Anything::self`, or — not yet visited — an evaluable expression, a
    /// feature of a metaclass or metadata feature, or an unfeatured feature
    /// whose value, if any, is evaluable; any other expression when it
    /// specializes nothing explicitly and every owned feature is an input
    /// (or its result) with no features and no value, or an evaluable
    /// result expression.
    pub(super) fn d_is_model_level_evaluable(&mut self, e: ElementRef) -> bool {
        self.model_level_evaluable(e, &HashSet::new(), 0)
    }

    /// `visited` is the set of referents on the path from the root
    /// expression (`visited->including(referent)` in the rule) — a value
    /// per branch, not shared across sibling arguments.
    fn model_level_evaluable(
        &mut self,
        e: ElementRef,
        visited: &HashSet<usize>,
        depth: usize,
    ) -> bool {
        // The tree recursion is over owned arguments (acyclic; reference
        // cycles are guarded by `visited`), so the bound only protects the
        // stack: deeper than any expression the parser accepts.
        if depth > 256 {
            return false;
        }
        let ty = self.b.elements[e.0].ty;
        // SysML redefines `modelLevelEvaluable` as false on calculation
        // and constraint usages (and so on the requirement, concern and
        // case usages under them).
        if self.is_kind(e, "CalculationUsage") || self.is_kind(e, "ConstraintUsage") {
            return false;
        }
        if matches!(ty, "NullExpression" | "MetadataAccessExpression")
            || self.is_kind(e, "LiteralExpression")
        {
            return true;
        }
        if ty == "FeatureReferenceExpression" {
            return self.reference_model_level_evaluable(e, visited, depth);
        }
        // A ConstructorExpression is an InstantiationExpression, not an
        // InvocationExpression: evaluable when its arguments are.
        if self.is_kind(e, "InstantiationExpression") {
            let args: Vec<ElementRef> = self
                .d_arguments(e)
                .into_iter()
                .filter_map(|a| a.element())
                .collect();
            for a in args {
                if !self.model_level_evaluable(a, visited, depth + 1) {
                    return false;
                }
            }
            if self.is_kind(e, "ConstructorExpression") {
                return true;
            }
            let function = self.d_instantiated_type(e);
            return function.is_some_and(|f| self.function_is_model_level_evaluable(&f));
        }
        // The general rule.
        let explicit = self
            .d_owned_specializations(e, "Specialization")
            .into_iter()
            .any(|r| !self.is_implied(r));
        if explicit {
            return false;
        }
        let result = self.d_result(e);
        let features = self.d_owned_features(e);
        for f in features {
            let input = matches!(self.effective_direction(f), Some("in")) || Some(f) == result;
            let plain = input
                && self.d_owned_features(f).is_empty()
                && self
                    .owned_relationships_of_kind(f, "FeatureValue")
                    .is_empty();
            if plain {
                continue;
            }
            let result_expression = self.b.elements[f.0]
                .owning_relationship
                .is_some_and(|m| self.b.elements[m].ty == "ResultExpressionMembership")
                && self.is_kind(f, "Expression")
                && self.model_level_evaluable(f, visited, depth + 1);
            if !result_expression {
                return false;
            }
        }
        true
    }

    fn reference_model_level_evaluable(
        &mut self,
        e: ElementRef,
        visited: &HashSet<usize>,
        depth: usize,
    ) -> bool {
        let Some(referent) = self.d_referent(e) else {
            return false;
        };
        // `referent.conformsTo('Anything::self')`: the library feature
        // `Base::Anything::self` (the standard library package is `Base`),
        // or a feature specializing it (`DataValue::self` redefines it).
        let anything_self = self.library_element_named(&[(
            "Base::Anything::self".to_string(),
            "Base::Anything::self".to_string(),
        )]);
        let referent = match referent {
            Reference::Element(referent) => referent,
            // A referent outside the model is evaluable only as
            // `Anything::self` itself, by id.
            outside => {
                return matches!(
                    (outside, anything_self),
                    (Reference::External(a), Some(Reference::External(b))) if a == b
                );
            }
        };
        if let Some(Reference::Element(anything_self)) = anything_self {
            if self.specializes(referent, anything_self) {
                return true;
            }
        }
        if visited.contains(&referent.0) {
            return false;
        }
        let mut visited = visited.clone();
        visited.insert(referent.0);
        let visited = &visited;
        if self.is_kind(referent, "Expression") {
            return self.model_level_evaluable(referent, visited, depth + 1);
        }
        if let Some(owner) = self.d_owning_type(referent) {
            if self.is_kind(owner, "Metaclass") || self.is_kind(owner, "MetadataFeature") {
                return true;
            }
        }
        if !self.d_featuring_types(referent).is_empty() {
            return false;
        }
        match self
            .owned_relationships_of_kind(referent, "FeatureValue")
            .into_iter()
            .next()
            .and_then(|fv| self.d_owned_member_element(fv))
        {
            None => true,
            Some(value) => self.model_level_evaluable(value, visited, depth + 1),
        }
    }

    /// `Function::isModelLevelEvaluable` for the function an invocation
    /// instantiates: a function of the Kernel Functions Library's
    /// `BaseFunctions`, `DataFunctions` or `ControlFunctions` — an element
    /// of a loaded library, or an external id the library name table names
    /// in one of them.
    pub(super) fn function_is_model_level_evaluable(&mut self, f: &Reference) -> bool {
        match f {
            Reference::Element(f) => {
                self.is_library_element(*f)
                    && self.element_qualified_name(*f).is_some_and(|qn| {
                        qn.split("::")
                            .next()
                            .is_some_and(|p| EVALUABLE_FUNCTION_PACKAGES.contains(&p))
                    })
            }
            Reference::External(id) => self
                .external_package
                .get(id)
                .is_some_and(|p| EVALUABLE_FUNCTION_PACKAGES.contains(&p.as_str())),
            Reference::Unresolved(_) => false,
        }
    }
}
