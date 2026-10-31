//! Exact, bounded reads of explicitly constrained multiplicity domains.
use super::multiplicities::NumericBound;
use crate::metaclass::is_a;
use crate::{eval, json::Builder};
use std::sync::Arc;
use sysmlv2_syntax::ast::{Expr, ExprKind, Literal};

#[derive(Clone)]
pub(super) struct Interval {
    pub(super) lower: NumericBound,
    pub(super) upper: NumericBound,
}

/// Index range syntax once per validation pass; memoized values remain local to
/// a comparison because its specializing receiver is part of the interpretation.
pub(super) struct DomainRows(crate::layered::LayeredMap<usize, usize>);

impl DomainRows {
    pub(super) fn new(b: &Builder) -> Self {
        Self(b.multiplicity_range_rows())
    }

    /// [`ExpressionBounds`] of the rows: the library's, kept with the
    /// prepared library while the build left its rows as they are, and the
    /// build's own over them.
    pub(super) fn expression_bounds(&self, b: &mut Builder) -> ExpressionBounds {
        let (seed, from) = match b.library_multiplicity_rows() {
            Some(prepared) => (
                Some(Arc::clone(prepared.library_expression_bounds())),
                b.elements.base_len(),
            ),
            None => (None, 0),
        };
        b.prepare_chain_targets();
        let own = {
            let b = &*b;
            let targets = |owner: usize| b.resolved_chain_targets(owner);
            ExpressionBounds::over(
                b,
                &self.0,
                from..b.explicit_len(),
                seed.as_deref(),
                &targets,
            )
        };
        match seed {
            Some(library) => library.joined(&own),
            None => own,
        }
    }

    pub(super) fn compare(&self, b: &mut Builder, owner: usize, target: usize) -> Comparison {
        let mut comparison = Comparison::default();
        let mut reader = Reader {
            rows: self,
            receiver: b.owner_scope_of(owner),
            steps: 0,
            active: Default::default(),
            memo: Default::default(),
        };
        let mut seen = crate::layered::IdSet::default();
        let mut intervals = [None, None];
        for (index, feature) in [target, owner].into_iter().enumerate() {
            let value = b
                .local_multiplicity(feature)
                .flatten()
                .and_then(|domain| reader.domain(b, domain, 0));
            match value {
                Some(Err(invalid)) => {
                    // Only diagnose a newly invalid contextual range. Authored
                    // invalid ranges belong to the declaration pass. Use lexical
                    // evaluation, not the row's scope as a featuring receiver.
                    if seen.insert(invalid.row)
                        && matches!(
                            reader.range(b, invalid.row, eval::MultiplicityBoundContext::Lexical),
                            Some(Ok(_))
                        )
                    {
                        comparison.reported_rows.push(invalid.row);
                        comparison.invalid.push((index == 0, invalid.reason));
                    }
                }
                Some(Ok(interval)) => intervals[index] = Some(interval),
                None => {}
            }
        }
        if reader.steps > eval::MAX_STEPS {
            return Comparison::default();
        }
        let [general, own] = intervals;
        comparison.intervals = own.zip(general);
        comparison
    }

    /// Validate inherited domains in a supplied receiver, rather than in the
    /// lexical owner of their unchanged Feature identities. Results are staged
    /// until the whole bounded pass succeeds, and only newly invalid ranges
    /// with a valid lexical baseline are diagnostic evidence.
    pub(super) fn inherited_invalid(
        &self,
        b: &mut Builder,
        receiver_scope: usize,
        features: &[usize],
        steps: &mut usize,
    ) -> Vec<(usize, usize, String)> {
        let mut reader = Reader {
            rows: self,
            receiver: Some(receiver_scope),
            steps: *steps,
            active: Default::default(),
            memo: Default::default(),
        };
        let mut invalids = Vec::new();
        let mut seen = crate::layered::IdSet::default();
        for &feature in features {
            reader.steps = reader.steps.saturating_add(1);
            if reader.steps > eval::MAX_STEPS {
                break;
            }
            let value = b
                .local_multiplicity(feature)
                .flatten()
                .and_then(|domain| reader.domain(b, domain, 0));
            if let Some(Err(invalid)) = value {
                if seen.insert(invalid.row)
                    && matches!(
                        reader.range(b, invalid.row, eval::MultiplicityBoundContext::Lexical),
                        Some(Ok(_))
                    )
                {
                    invalids.push((invalid.row, feature, invalid.reason));
                }
            }
        }
        *steps = reader.steps;
        if *steps > eval::MAX_STEPS {
            Vec::new()
        } else {
            invalids
        }
    }
}

/// The multiplicities whose domain has a bound written as an expression —
/// in their own range, or in a multiplicity their range subsets or
/// redefines, transitively — with the features holding them and the scopes
/// those are read in or members of. A literal bound is the same in every
/// receiver; only such a feature can have a domain that is valid where
/// written and invalid in a receiver, which is what
/// [`DomainRows::inherited_invalid`] reports.
#[derive(Clone, Default)]
pub(crate) struct ExpressionBounds {
    multiplicities: crate::layered::IdSet<usize>,
    pub(crate) features: crate::layered::IdSet<usize>,
    pub(crate) scopes: crate::layered::IdSet<usize>,
}

impl ExpressionBounds {
    /// The bounds over the elements in `elements`, whose ranges `rows`
    /// indexes by multiplicity: those rows with a bound written as an
    /// expression, and every multiplicity in `elements` whose chain reaches
    /// one of them or of `seed` (a frozen prefix's, which no row in
    /// `elements` can be reached from). `chain_targets` gives the resolved
    /// targets of a multiplicity's subsettings and redefinitions.
    pub(crate) fn over(
        b: &Builder,
        rows: &crate::layered::LayeredMap<usize, usize>,
        elements: std::ops::Range<usize>,
        seed: Option<&Self>,
        chain_targets: &dyn Fn(usize) -> Vec<usize>,
    ) -> Self {
        let mut elems: crate::layered::IdSet<usize> = rows
            .iter()
            .filter(|(&e, &row)| {
                elements.contains(&e) && {
                    let (_, _, range) = &b.multiplicities[row];
                    literal_bound(&range.upper).is_none()
                        || range
                            .lower
                            .as_ref()
                            .is_some_and(|lower| literal_bound(lower).is_none())
                }
            })
            .map(|(&e, _)| e)
            .collect();
        let reached = |elems: &crate::layered::IdSet<usize>, t: usize| {
            elems.contains(&t) || seed.is_some_and(|seed| seed.multiplicities.contains(&t))
        };
        if elems.is_empty() && seed.is_none_or(|seed| seed.multiplicities.is_empty()) {
            return Self::default();
        }
        let multiplicities: Vec<usize> = elements
            .clone()
            .filter(|&e| is_a!(b.elements[e], "Multiplicity"))
            .collect();
        loop {
            let mut grew = false;
            for &e in &multiplicities {
                if elems.contains(&e) {
                    continue;
                }
                if chain_targets(e).into_iter().any(|t| reached(&elems, t)) {
                    elems.insert(e);
                    grew = true;
                }
            }
            if !grew {
                break;
            }
        }
        // The features holding them (a range's row names its feature; a
        // multiplicity without a range of its own is found as a member of
        // its feature) and the scopes those are read in or members of:
        // inheriting one passes a scope in the set, unless an alias or a
        // membership import stands for it (which the reach test reads).
        let mut out = Self {
            multiplicities: elems,
            ..Self::default()
        };
        let mut without_row = Vec::new();
        let multiplicities: Vec<usize> = out.multiplicities.iter().copied().collect();
        for e in multiplicities {
            match rows.get(&e) {
                Some(&row) => {
                    let (source, read_in, _) = &b.multiplicities[row];
                    out.note(b, *source, Some(*read_in));
                }
                None => without_row.push(e),
            }
        }
        if !without_row.is_empty() {
            for owner in elements {
                for &r in &b.elements[owner].owned_relationships {
                    if !is_a!(b.elements[r], "Membership") {
                        continue;
                    }
                    if b.elements[r]
                        .children
                        .iter()
                        .any(|child| without_row.contains(child))
                    {
                        out.note(b, owner, None);
                    }
                }
            }
        }
        out
    }

    /// Note the feature holding a bound: `element` itself, or, for a
    /// multiplicity written in a feature's body (whose row names the
    /// multiplicity), the feature owning it.
    fn note(&mut self, b: &Builder, element: usize, read_in: Option<usize>) {
        let mut feature = element;
        while is_a!(b.elements[feature], "Multiplicity") {
            match b.owner_elem(feature) {
                Some(owner) => feature = owner,
                None => break,
            }
        }
        self.features.insert(feature);
        self.scopes.extend(read_in);
        self.scopes.extend(b.elem_scope.get(&feature).copied());
        self.scopes.extend(
            b.owner_elem(feature)
                .and_then(|o| b.elem_scope.get(&o).copied()),
        );
    }

    /// These bounds and `other`'s together.
    fn joined(&self, other: &Self) -> Self {
        let mut out = self.clone();
        out.multiplicities
            .extend(other.multiplicities.iter().copied());
        out.features.extend(other.features.iter().copied());
        out.scopes.extend(other.scopes.iter().copied());
        out
    }
}

#[derive(Default)]
pub(super) struct Comparison {
    pub(super) intervals: Option<(Interval, Interval)>,
    pub(super) invalid: Vec<(bool, String)>,
    pub(super) reported_rows: Vec<usize>,
}

#[derive(Clone)]
struct InvalidRange {
    row: usize,
    reason: String,
}

type Domain = Result<Interval, InvalidRange>;

struct Reader<'a> {
    rows: &'a DomainRows,
    receiver: Option<usize>,
    steps: usize,
    active: crate::layered::IdSet<usize>,
    memo: crate::layered::IdMap<(usize, usize), Option<Domain>>,
}

/// A bound written as a literal — a natural number or `*` — as the
/// evaluator values it, read without evaluating: such a bound is the
/// same in every receiver, and most bounds are written so.
fn literal_bound(expr: &Expr) -> Option<eval::Value> {
    match &expr.kind {
        ExprKind::Literal(Literal::Integer(raw)) => {
            raw.parse::<i128>().ok().map(eval::Value::Integer)
        }
        ExprKind::Literal(Literal::Infinity) => Some(eval::Value::Real(f64::INFINITY)),
        _ => None,
    }
}

impl Reader<'_> {
    fn domain(&mut self, b: &mut Builder, e: usize, depth: usize) -> Option<Domain> {
        self.steps = self.steps.saturating_add(1);
        if self.steps > eval::MAX_STEPS || depth >= 64 {
            return None;
        }
        if let Some(value) = self.memo.get(&(e, depth)) {
            return value.clone();
        }
        if !self.active.insert(e) {
            return None;
        }
        let result = self.domain_inner(b, e, depth);
        self.active.remove(&e);
        self.memo.insert((e, depth), result.clone());
        result
    }

    fn domain_inner(&mut self, b: &mut Builder, e: usize, depth: usize) -> Option<Domain> {
        if !is_a!(b.elements[e], "Multiplicity") {
            return None;
        }
        let mut interval = None;
        if b.elements[e].ty == "MultiplicityRange" {
            let i = *self.rows.0.get(&e)?;
            interval = Some(self.range(
                b,
                i,
                eval::MultiplicityBoundContext::Receiver(self.receiver),
            )?);
        }
        self.steps = self
            .steps
            .saturating_add(b.elements[e].owned_relationships.len());
        if self.steps > eval::MAX_STEPS {
            return None;
        }
        for r in b.elements[e].owned_relationships.clone() {
            let relation = &b.elements[r];
            if !is_a!(relation, "Specialization") {
                continue;
            }
            let property = match relation.ty {
                "Subsetting" => "subsettedFeature",
                "Redefinition" => "redefinedFeature",
                _ => return None,
            };
            let id = relation.props.get(property)?.as_reference()?;
            let target = b.element_index_of_uuid(id)?;
            let next = self.domain(b, target, depth + 1)?;
            interval = Some(match (interval, next) {
                (None, next) => next,
                (Some(Err(invalid)), _) | (_, Err(invalid)) => Err(invalid),
                (Some(Ok(current)), Ok(next)) => {
                    let intersection = Interval {
                        lower: current.lower.max(next.lower),
                        upper: current.upper.min(next.upper),
                    };
                    if intersection.lower > intersection.upper {
                        return None;
                    }
                    Ok(intersection)
                }
            });
        }
        interval
    }

    fn range(
        &mut self,
        b: &mut Builder,
        row: usize,
        context: eval::MultiplicityBoundContext,
    ) -> Option<Domain> {
        // Literal bounds are read in place; a bound that is an
        // expression is evaluated in the receiver's context, as it may
        // name a feature the receiver redefines.
        let literal = {
            let (_, _, range) = &b.multiplicities[row];
            let upper = literal_bound(&range.upper);
            let lower = range.lower.as_ref().map(literal_bound);
            match (upper, lower) {
                (Some(upper), None) => Some((upper, None)),
                (Some(upper), Some(Some(lower))) => Some((upper, Some(lower))),
                _ => None,
            }
        };
        let (upper, lower) = match literal {
            Some((upper, lower)) => {
                self.steps = self.steps.saturating_add(1 + usize::from(lower.is_some()));
                if self.steps > eval::MAX_STEPS {
                    return None;
                }
                (upper, lower)
            }
            None => {
                let (source, scope, range) = b.multiplicities[row].clone();
                let upper = eval::evaluate_multiplicity_bound(
                    b,
                    source,
                    scope,
                    context,
                    &range.upper,
                    &mut self.steps,
                )?;
                let lower = match &range.lower {
                    Some(lower) => Some(eval::evaluate_multiplicity_bound(
                        b,
                        source,
                        scope,
                        context,
                        lower,
                        &mut self.steps,
                    )?),
                    None => None,
                };
                (upper, lower)
            }
        };
        // Unknown values must not be mistaken for known values of an invalid kind.
        if matches!(
            upper,
            eval::Value::Indeterminate | eval::Value::Unbound(..) | eval::Value::UnboundMember(..)
        ) || matches!(
            lower,
            Some(
                eval::Value::Indeterminate
                    | eval::Value::Unbound(..)
                    | eval::Value::UnboundMember(..)
            )
        ) {
            return None;
        }
        let invalid = |reason: String| Some(Err(InvalidRange { row, reason }));
        let Some(upper) = NumericBound::from_value(upper) else {
            return invalid("upper bound must be a Natural number (or `*`)".into());
        };
        let lower = match lower {
            Some(lower) => match NumericBound::from_value(lower) {
                Some(lower) => lower,
                None => return invalid("lower bound must be a Natural number".into()),
            },
            None if upper == NumericBound::Infinity => NumericBound::zero(),
            None => upper.clone(),
        };
        if !upper.is_natural(true) {
            return invalid(format!(
                "upper bound {upper} is not a Natural number (or `*`)"
            ));
        }
        if !lower.is_natural(false) {
            return invalid(format!("lower bound {lower} is not a Natural number"));
        }
        if lower > upper {
            return invalid(format!("lower bound {lower} exceeds upper bound {upper}"));
        }
        Some(Ok(Interval { lower, upper }))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{json::ResolvedModel, model::Model};
    use std::collections::HashMap;

    #[test]
    fn inherited_domains_restore_origin_and_retry_after_exhaustion() {
        let mut model = Model::new();
        model.add_source("unrelated.kerml", "package Other;");
        model.add_source("base.kerml", "class Base { feature n default = 3; feature x[0..n]; } class Child specializes Base { feature n redefines Base::n = -1; }");
        let mut r = ResolvedModel::build(&model);
        let x = r.resolve_qualified("Base::x").unwrap().0;
        let child = r.resolve_qualified("Child").unwrap().0;
        let scope = r.b.elem_scope.get(&child).copied().unwrap();
        let rows = DomainRows::new(&r.b);
        for origin in [None, Some(0)] {
            r.b.identity_origin_unit = origin;
            let mut exhausted = eval::MAX_STEPS;
            assert!(
                rows.inherited_invalid(&mut r.b, scope, &[x], &mut exhausted)
                    .is_empty()
            );
            assert!(exhausted > eval::MAX_STEPS);
            assert_eq!(r.b.identity_origin_unit, origin);
            let mut fresh = 0;
            let findings = rows.inherited_invalid(&mut r.b, scope, &[x, x], &mut fresh);
            assert_eq!(findings.len(), 1);
            assert!(findings[0].2.contains("upper bound -1"));
            assert_eq!(r.b.identity_origin_unit, origin);
        }
    }

    #[test]
    fn contextual_errors_require_complete_domains_and_unwind_after_failure() {
        for mutation in 0..4 {
            let mut model = Model::new();
            model.add_source("test.kerml", "class Base { feature n default = 3; feature x { multiplicity domain[0..n]; } } class Child specializes Base { feature n redefines Base::n = -1; feature y redefines x; } multiplicity extra[0..*]; multiplicity link subsets extra;");
            assert!(!model.has_errors());
            let mut r = ResolvedModel::build(&model);
            let x = r.resolve_qualified("Base::x").unwrap().0;
            let y = r.resolve_qualified("Child::y").unwrap().0;
            let range = r.resolve_qualified("Base::x::domain").unwrap().0;
            let link = r.resolve_qualified("link").unwrap().0;
            let edge = r.b.elements[link].owned_relationships[0];
            // Move the constraint to the range; a duplicate relationship
            // carrier is malformed and cannot support receiver evidence.
            r.b.elements[link].owned_relationships = Vec::new().into();
            r.b.elements[range].owned_relationships.push(edge);
            let range_id = r.element_id(crate::json::ElementRef(range));
            r.b.elements[edge]
                .props
                .insert("owningRelatedElement", serde_json::json!({"@id": range_id}));
            let rows = DomainRows::new(&r.b);
            assert_eq!(rows.compare(&mut r.b, y, x).invalid.len(), 1);
            let previous = r.b.elements[edge].clone();
            match mutation {
                0 => r.b.elements[edge].set_ty("Subclassification"),
                1 => {
                    r.b.elements[edge].props.insert(
                        "subsettedFeature",
                        serde_json::json!({"@id": "11111111-1111-4111-8111-111111111111"}),
                    );
                }
                2 => {
                    let id = r.element_id(crate::json::ElementRef(range));
                    r.b.elements[edge]
                        .props
                        .insert("subsettedFeature", serde_json::json!({"@id": id}));
                }
                _ => {
                    let extra = r.resolve_qualified("extra").unwrap().0;
                    r.b.elements[extra].set_ty("Feature");
                }
            }
            assert!(rows.compare(&mut r.b, y, x).invalid.is_empty());
            r.b.elements[edge] = previous;
            if mutation != 3 {
                assert_eq!(rows.compare(&mut r.b, y, x).invalid.len(), 1);
            }
        }
    }

    #[test]
    fn domain_intersection_requires_every_constraint_to_be_valid_and_complete() {
        for (range, expected) in [
            ("0..8", Some(("2", "5"))),
            ("4..9", Some(("4", "5"))),
            ("7..9", None),
            ("6..3", None),
        ] {
            let mut model = Model::new();
            model.add_source("test.kerml", &format!("multiplicity domain[{range}]; multiplicity restriction[2..5]; multiplicity link subsets restriction;"));
            assert!(!model.has_errors());
            let mut r = ResolvedModel::build(&model);
            let domain = r.resolve_qualified("domain").unwrap().0;
            let link = r.resolve_qualified("link").unwrap().0;
            let edge = r.b.elements[link].owned_relationships[0];
            r.b.elements[domain].owned_relationships.push(edge);
            let rows = DomainRows::new(&r.b);
            let read = |b: &mut Builder| {
                Reader {
                    rows: &rows,
                    receiver: None,
                    steps: 0,
                    active: Default::default(),
                    memo: Default::default(),
                }
                .domain(b, domain, 0)
                .and_then(Result::ok)
                .map(|i| (i.lower.to_string(), i.upper.to_string()))
            };
            assert_eq!(read(&mut r.b), expected.map(|(l, u)| (l.into(), u.into())));
            r.b.elements[edge].set_ty("Subclassification");
            assert!(read(&mut r.b).is_none());
            r.b.elements[edge].set_ty("Subsetting");
            r.b.elements[edge].props.insert(
                "subsettedFeature",
                serde_json::json!({"@id": "11111111-1111-4111-8111-111111111111"}),
            );
            assert!(read(&mut r.b).is_none());
        }
    }

    #[test]
    fn domain_limits_unwind_and_do_not_poison_shallower_reads() {
        let mut model = Model::new();
        model.add_source("test.kerml", "multiplicity good[2..4]; multiplicity chain subsets good; multiplicity cycle subsets cycle;");
        assert!(!model.has_errors());
        let mut r = ResolvedModel::build(&model);
        let good = r.resolve_qualified("good").unwrap().0;
        let chain = r.resolve_qualified("chain").unwrap().0;
        let cycle = r.resolve_qualified("cycle").unwrap().0;
        let rows = DomainRows::new(&r.b);
        let mut reader = Reader {
            rows: &rows,
            receiver: None,
            steps: 0,
            active: Default::default(),
            memo: Default::default(),
        };
        assert!(reader.domain(&mut r.b, chain, 63).is_none());
        assert!(reader.active.is_empty());
        let bounds = reader.domain(&mut r.b, chain, 0).unwrap().ok().unwrap();
        assert_eq!(bounds.lower.to_string(), "2");
        assert_eq!(bounds.upper.to_string(), "4");
        assert!(reader.domain(&mut r.b, cycle, 0).is_none());
        assert!(reader.active.is_empty());
        let before = reader.steps;
        assert!(reader.domain(&mut r.b, good, 0).is_some());
        assert!(reader.steps > before);
        let before = reader.steps;
        assert!(reader.domain(&mut r.b, good, 0).is_some());
        assert!(reader.steps > before, "memo hits consume shared budget");
        reader.steps = eval::MAX_STEPS;
        assert!(reader.domain(&mut r.b, good, 0).is_none());
        reader.steps = usize::MAX;
        assert!(reader.domain(&mut r.b, good, 0).is_none());
    }

    #[test]
    fn bound_wrapper_shares_work_preserves_exact_values_and_restores_origin() {
        let mut model = Model::new();
        model.add_source("first.kerml", "package A;");
        model.add_source("second.kerml", "package B { feature n = 170141183460469231731687303715884105729; multiplicity exact['bbbbbbbb-bbbb-4bbb-8bbb-bbbbbbbbbbbb']; multiplicity unknown[missing]; }");
        assert!(!model.has_errors());
        let mut r = ResolvedModel::build(&model);
        let n = r.resolve_qualified("B::n").unwrap();
        let id = "bbbbbbbb-bbbb-4bbb-8bbb-bbbbbbbbbbbb".parse().unwrap();
        r.override_ids(&HashMap::from([(r.element_id(n), id)]));
        assert!(r.bind_id_spelled_references().contains(&id));
        let previous = r.b.set_identity_origin(n.0);
        assert_eq!(r.b.identity_origin_unit, Some(1));
        r.b.identity_origin_unit = previous;
        for name in ["exact", "unknown"] {
            let element = r.resolve_qualified(&format!("B::{name}")).unwrap().0;
            let (source, scope, range) =
                r.b.multiplicities
                    .iter()
                    .find(|row| row.0 == element)
                    .unwrap()
                    .clone();
            for context in [
                eval::MultiplicityBoundContext::Lexical,
                eval::MultiplicityBoundContext::Receiver(None),
            ] {
                for origin in [Some(0), None] {
                    for initial in [0, eval::MAX_STEPS, usize::MAX] {
                        r.b.identity_origin_unit = origin;
                        let mut steps = initial;
                        let value = eval::evaluate_multiplicity_bound(
                            &mut r.b,
                            source,
                            scope,
                            context,
                            &range.upper,
                            &mut steps,
                        );
                        assert_eq!(r.b.identity_origin_unit, origin);
                        assert!(steps > initial || initial == usize::MAX);
                        if initial == 0 && name == "exact" {
                            assert_eq!(
                                NumericBound::from_value(value.unwrap())
                                    .unwrap()
                                    .to_string(),
                                "170141183460469231731687303715884105729"
                            );
                        } else {
                            assert!(value.is_none());
                        }
                    }
                }
            }
        }
    }
}
