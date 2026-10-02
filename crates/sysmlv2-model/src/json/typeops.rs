//! Type-operation results and the evaluability residue over the resolved
//! model: the unioning, intersecting and differencing types and their
//! relationship ends, an association's related types, a connector's
//! default featuring type, and `isModelLevelEvaluable`. Each function
//! documents the specification rule it implements; the dispatch is in
//! `derived.rs`.

use super::derived::Reference;
use super::type_relations::{RelationFact, TypeRelations};
use super::{ElementRef, LookupResult, ResolvedModel, split_qualified};
use std::collections::HashSet;
use sysmlv2_syntax::{
    ast::{Name, QualifiedName},
    span::Span,
};

/// KerML 1.0, §§8.2.5.8.1–8.2.5.8.2, Tables 5 and 7. These are
/// designated function identities, not all functions in their packages.
fn evaluable_function_name(package: &str, name: &str) -> bool {
    match package {
        "BaseFunctions" => matches!(
            name,
            "istype"
                | "hastype"
                | "@"
                | "@@"
                | "as"
                | "meta"
                | "=="
                | "!="
                | "==="
                | "!=="
                | "#"
                | ","
        ),
        "DataFunctions" => matches!(
            name,
            "xor"
                | "not"
                | "|"
                | "&"
                | "<"
                | ">"
                | "<="
                | ">="
                | "+"
                | "-"
                | "*"
                | "/"
                | "%"
                | "^"
                | ".."
        ),
        "ControlFunctions" => matches!(
            name,
            "??" | "if" | "or" | "and" | "implies" | "." | "collect" | "select"
        ),
        _ => false,
    }
}

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
    fn featuring_closure(
        &mut self,
        roots: &[ElementRef],
        mut relations: Option<&mut TypeRelations>,
        steps: &mut usize,
    ) -> Option<Vec<ElementRef>> {
        let mut out: Vec<ElementRef> = Vec::new();
        let mut output_seen = HashSet::new();
        let mut frontier: Vec<ElementRef> = roots.to_vec();
        let mut seen: HashSet<usize> = roots.iter().map(|r| r.0).collect();
        while let Some(x) = frontier.pop() {
            let next: Vec<ElementRef> = if self.is_kind(x, "Feature") {
                match relations.as_deref_mut() {
                    Some(proof) => proof
                        .featuring_types(&mut self.b, x.0, steps)?
                        .into_iter()
                        .map(ElementRef)
                        .collect(),
                    None => self.d_featuring_types(x),
                }
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
                if output_seen.insert(t) {
                    out.push(t);
                }
            }
        }
        Some(out)
    }

    // Retained compatibility provider for domains whose snapshot/derived
    // featuring is not yet audited. Domain selection happens before the
    // stronger provider runs; a failed proof never falls back here.
    fn compatibility_specializes(&mut self, t: ElementRef, general: ElementRef) -> bool {
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

    fn compatibility_is_featured_within(&mut self, f: ElementRef, t: ElementRef) -> bool {
        let featuring = self.d_featuring_types(f);
        if featuring
            .iter()
            .all(|&ft| self.compatibility_specializes(t, ft))
        {
            return true;
        }
        if self.prop_bool(f.0, "isVariable") {
            if let Some(o) = self.d_owning_type(f) {
                if self.compatibility_specializes(t, o) {
                    return true;
                }
            }
        }
        if let Some(Reference::Element(first)) = self.d_chaining_features(f).into_iter().next() {
            if self.prop_bool(first.0, "isVariable") {
                if let Some(o) = self.d_owning_type(first) {
                    if self.compatibility_specializes(t, o) {
                        return true;
                    }
                }
            }
        }
        false
    }

    /// `Feature::isFeaturedWithin(type)` for a non-null type: every
    /// featuring type of `f` is one `t` specializes; or `f` is variable and
    /// `t` specializes its owning type; or `f` is a chain whose first link
    /// is variable and `t` specializes that link's owning type.
    fn is_featured_within(
        &mut self,
        f: ElementRef,
        t: ElementRef,
        relations: Option<&mut TypeRelations>,
        steps: &mut usize,
    ) -> Option<bool> {
        let relations = match relations {
            Some(proof) => proof,
            None => return Some(self.compatibility_is_featured_within(f, t)),
        };
        let featuring = relations.featuring_types(&mut self.b, f.0, steps)?;
        let compatibility = RelationFact::all(
            featuring
                .into_iter()
                .map(|ft| relations.compatible(&mut self.b, t.0, ft, steps)),
        );
        if compatibility == RelationFact::Yes {
            return Some(true);
        }
        let mut unknown = compatibility == RelationFact::Unknown;
        let mut alternatives = Vec::new();
        if self.prop_bool(f.0, "isVariable") {
            match relations.owning_type(&mut self.b, f.0, steps) {
                Some(Some(owner)) => alternatives.push(ElementRef(owner)),
                Some(None) => {}
                None => unknown = true,
            }
        }
        if let Some(Reference::Element(first)) = self.d_chaining_features(f).into_iter().next() {
            if self.prop_bool(first.0, "isVariable") {
                match relations.owning_type(&mut self.b, first.0, steps) {
                    Some(Some(owner)) => alternatives.push(ElementRef(owner)),
                    Some(None) => {}
                    None => unknown = true,
                }
            }
        }
        for owner in alternatives {
            match relations.specializes(&mut self.b, t.0, owner.0, steps) {
                RelationFact::Yes => return Some(true),
                RelationFact::No => {}
                RelationFact::Unknown => unknown = true,
            }
        }
        if unknown { None } else { Some(false) }
    }

    /// `Connector::defaultFeaturingType`: of the types featuring the related
    /// features directly or indirectly, those every related feature is
    /// featured within; of those, the innermost — one no other of them is
    /// featured within — first. Null when a related feature is outside the
    /// model (its featuring is not visible), owned evidence is incomplete,
    /// a proof budget is exhausted, or there are no candidates. The strict
    /// reader retains its Approximate refusal; null is not an absence proof.
    pub(super) fn d_default_featuring_type(&mut self, e: ElementRef) -> Option<ElementRef> {
        let related: Vec<ElementRef> = self
            .d_related_features(e)
            .into_iter()
            .map(|r| r.element())
            .collect::<Option<Vec<_>>>()?;
        if related.is_empty() {
            return None;
        }
        let mut proof = TypeRelations::default();
        let mut steps = 0;
        let roots: Vec<_> = related.iter().map(|e| e.0).collect();
        let audited = proof.audited_featuring_domain(&mut self.b, &roots, &mut steps)?;
        let mut relations = audited.then_some(proof);
        let candidates = self.featuring_closure(&related, relations.as_mut(), &mut steps)?;
        let mut common: Vec<ElementRef> = Vec::new();
        for t in candidates {
            let mut all = true;
            for &f in &related {
                match self.is_featured_within(f, t, relations.as_mut(), &mut steps) {
                    Some(true) => {}
                    Some(false) => {
                        all = false;
                        break;
                    }
                    None => return None,
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
                if t2 != t1
                    && self
                        .featuring_closure(&[t2], relations.as_mut(), &mut steps)?
                        .contains(&t1)
                {
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
            if self.compatibility_specializes(referent, anything_self) {
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

    /// Only the designated Kernel Functions Library identities are
    /// model-level evaluable. A spelling selects a candidate; the library
    /// binding must resolve back to the same element or external identity.
    pub(super) fn function_is_model_level_evaluable(&mut self, f: &Reference) -> bool {
        let (package, name) = match f {
            Reference::Element(e) => {
                if !self.is_library_element(*e) || !self.is_kind(*e, "Function") {
                    return false;
                }
                let Some(qn) = self.element_qualified_name(*e) else {
                    return false;
                };
                let segments = split_qualified(&qn);
                let [package, name] = segments.as_slice() else {
                    return false;
                };
                (package.clone(), name.clone())
            }
            Reference::External(id) => {
                let (Some(package), Some(name)) =
                    (self.external_package.get(id), self.external_names.get(id))
                else {
                    return false;
                };
                (package.clone(), name.clone())
            }
            Reference::Unresolved(_) => return false,
        };
        if !evaluable_function_name(&package, &name) {
            return false;
        }
        self.designated_function_binding(&package, &name).as_ref() == Some(f)
    }

    /// Resolve one designated function without allowing an ambiguous loaded
    /// name to fall back to an external name-table identity. General name
    /// lookup retains its compatibility behavior; this is an admission proof.
    fn designated_function_binding(&mut self, package: &str, name: &str) -> Option<Reference> {
        match self.b.designated_function_lookup(package, name) {
            LookupResult::Found(index, _, _) => {
                let e = ElementRef(index);
                (self.is_library_element(e) && self.is_kind(e, "Function"))
                    .then_some(Reference::Element(e))
            }
            LookupResult::Ambiguous => None,
            LookupResult::Missing => {
                let name = format!("{package}::{name}");
                if self.external_ambiguous_names.contains(&name) {
                    return None;
                }
                let id = *self.external_by_name.get(&name)?;
                self.ensure_by_id();
                // An external table cannot relabel an in-model element. The
                // loaded-identity branch must establish its actual binding.
                (!self.by_id.contains_key(&id)).then_some(Reference::External(id))
            }
        }
    }
}

impl super::Builder {
    pub(super) fn designated_function_lookup(&mut self, package: &str, name: &str) -> LookupResult {
        let qn = QualifiedName {
            is_global: false,
            segments: [package, name]
                .into_iter()
                .map(|value| Name {
                    value: value.to_string(),
                    span: Span::default(),
                })
                .collect(),
            span: Span::default(),
        };
        self.resolve_unrestricted(0, &qn)
    }
}

#[cfg(test)]
mod evaluable_function_tests {
    use super::*;
    use crate::model::Model;
    use std::collections::HashMap;
    use uuid::Uuid;

    #[test]
    fn all_designated_external_identities_and_exclusions() {
        // Independently transcribed normative Table 5 / Table 7 identities.
        let rows = [
            (
                "BaseFunctions",
                "istype hastype @ @@ as meta == != === !== # ,",
                true,
            ),
            (
                "DataFunctions",
                "xor not | & < > <= >= + - * / % ^ ..",
                true,
            ),
            (
                "ControlFunctions",
                "?? if or and implies . collect select",
                true,
            ),
            ("BaseFunctions", "all [ custom", false),
            ("DataFunctions", "~ custom", false),
            ("ControlFunctions", "custom", false),
        ];
        let mut names = HashMap::new();
        let mut expected = Vec::new();
        for (package, functions, eligible) in rows {
            for name in functions.split_whitespace() {
                let id = Uuid::from_u128(expected.len() as u128 + 1);
                names.insert(id.to_string(), vec![package.to_string(), name.to_string()]);
                expected.push((id, eligible));
            }
        }
        assert_eq!(
            expected.iter().filter(|(_, eligible)| *eligible).count(),
            35
        );
        let mut r = ResolvedModel::build(&Model::new());
        r.set_library_names(&names);
        for _ in 0..2 {
            for &(id, eligible) in &expected {
                assert_eq!(
                    r.function_is_model_level_evaluable(&Reference::External(id)),
                    eligible,
                    "{id}"
                );
            }
        }
    }
}
