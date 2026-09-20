//! Quantity-dimension analysis over the resolved model: reading the
//! standard library's quantity/unit structure so hosts can compare a
//! declared quantity type against the unit a value is written in, and
//! suggest a type where none is declared.
//!
//! The library encodes dimensions twice, and this module joins the two
//! encodings on the base-quantity elements:
//!
//! - A *quantity value* type (`AccelerationValue`) carries an `mRef`
//!   member typed by its *unit definition* (`AccelerationUnit`), whose
//!   `QuantityPowerFactor` members each bind a base quantity (`isq.L`)
//!   and an integer exponent — the type's dimension as declared.
//! - A *bracket unit* (`[m/s^2]`) evaluates to a [`Unit`]: an exponent
//!   map over base **unit** elements (`m`, `s`). Each base unit is
//!   itself typed by a unit definition (`LengthUnit`) carrying power
//!   factors — composing the two maps lands the unit in the same
//!   base-quantity space.
//!
//! Everything here is best-effort and silent on indeterminacy: no
//! library, an opaque user unit, or an unevaluable structure yields
//! `None`, never a guess — callers (the `dimensional-consistency` lint
//! rule) only speak when both sides are determinate.

use std::collections::{HashMap, HashSet, VecDeque};

use sysmlv2_syntax::Span;
use sysmlv2_syntax::ast::{Dialect, Expr, ExprKind, Name, QualifiedName, TargetRef};

use crate::eval::{Unit, Value};
use crate::json::{ElementRef, ResolvedModel, ScopeRef};

/// A quantity dimension: a product of base-quantity powers, ordered by
/// base-quantity element, exponents as reduced rationals (`den > 0`,
/// gcd 1, zero factors dropped). Two dimensions are equal iff the
/// factor lists are — the commensurability test.
#[derive(Clone, Debug, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub struct QuantityDims {
    /// `(base-quantity element, exponent numerator, denominator)`.
    factors: Vec<(usize, i32, i32)>,
}

impl QuantityDims {
    pub(crate) fn valid(&self, n: usize) -> bool {
        self.factors
            .iter()
            .all(|&(e, num, den)| e < n && num != 0 && den > 0)
    }
    pub(crate) fn dimensionless() -> Self {
        Self {
            factors: Vec::new(),
        }
    }

    pub(crate) fn product(&self, other: &Self, divide: bool) -> Option<Self> {
        let sign = if divide { -1 } else { 1 };
        normalize(
            self.factors
                .iter()
                .map(|&(q, n, d)| (q, i64::from(n), i64::from(d)))
                .chain(
                    other
                        .factors
                        .iter()
                        .map(|&(q, n, d)| (q, i64::from(n) * sign, i64::from(d))),
                )
                .collect(),
        )
    }

    pub(crate) fn pow(&self, exponent: i32) -> Option<Self> {
        normalize(
            self.factors
                .iter()
                .map(|&(q, n, d)| (q, i64::from(n) * i64::from(exponent), i64::from(d)))
                .collect(),
        )
    }

    /// Dimension one — no base-quantity factors.
    #[must_use]
    pub fn is_dimensionless(&self) -> bool {
        self.factors.is_empty()
    }

    /// Render for diagnostics with the base quantities' declared names:
    /// `L*T^-2`, `M`, `1` (dimensionless).
    #[must_use]
    pub fn render(&self, model: &ResolvedModel) -> String {
        if self.factors.is_empty() {
            return "1".to_string();
        }
        self.factors
            .iter()
            .map(|&(q, n, d)| {
                let name = model.element_name(ElementRef(q)).unwrap_or("?");
                if n == 1 && d == 1 {
                    name.to_string()
                } else if d == 1 {
                    format!("{name}^{n}")
                } else {
                    format!("{name}^({n}/{d})")
                }
            })
            .collect::<Vec<_>>()
            .join("*")
    }
}

fn gcd(a: i64, b: i64) -> i64 {
    let (mut a, mut b) = (a.abs(), b.abs());
    while b != 0 {
        (a, b) = (b, a % b);
    }
    a.max(1)
}

/// Sum raw `(element, num, den)` factors into a canonical dimension:
/// same-element exponents add as rationals, zeros drop, results reduce.
/// `None` on arithmetic overflow (never for real models).
fn normalize(mut raw: Vec<(usize, i64, i64)>) -> Option<QuantityDims> {
    raw.sort_by_key(|&(q, _, _)| q);
    let mut factors: Vec<(usize, i32, i32)> = Vec::new();
    let mut i = 0;
    while i < raw.len() {
        let q = raw[i].0;
        let (mut num, mut den) = (0i64, 1i64);
        while i < raw.len() && raw[i].0 == q {
            let (n, d) = (raw[i].1, raw[i].2);
            if d == 0 {
                return None;
            }
            num = num.checked_mul(d)?.checked_add(n.checked_mul(den)?)?;
            den = den.checked_mul(d)?;
            i += 1;
        }
        if num == 0 {
            continue;
        }
        if den < 0 {
            num = -num;
            den = -den;
        }
        let g = gcd(num, den);
        factors.push((
            q,
            i32::try_from(num / g).ok()?,
            i32::try_from(den / g).ok()?,
        ));
    }
    Some(QuantityDims { factors })
}

fn simple_qn(name: &str) -> QualifiedName {
    QualifiedName {
        is_global: false,
        segments: vec![Name {
            value: name.to_string(),
            span: Span::default(),
        }],
        span: Span::default(),
    }
}

impl ResolvedModel {
    /// The dimension a quantity value type declares: its `mRef`
    /// measurement reference's unit definition, read through
    /// its own `unit_def_dims`. `None` when the type does not carry a
    /// determinable dimension (not a quantity type, no standard
    /// library, an abstract measurement reference).
    pub fn quantity_dims_of_type(&mut self, ty: ElementRef) -> Option<QuantityDims> {
        if !self.b.semantic_ready {
            return self.quantity_dims_of_type_uncached(ty);
        }
        if let Some(hit) = self
            .b
            .semantic_memo
            .types
            .get(&(ty.0, crate::eval::unit_spelling_expansion()))
            .cloned()
        {
            self.b.used_imports.extend(hit.imports);
            return hit.value;
        }
        let imports = std::mem::take(&mut self.b.used_imports);
        let value = self.quantity_dims_of_type_uncached(ty);
        let proof = crate::semantic_memo::Proven {
            value: value.clone(),
            imports: self.b.used_imports.iter().copied().collect(),
        };
        self.b.used_imports.extend(imports);
        self.b
            .semantic_memo
            .types
            .insert((ty.0, crate::eval::unit_spelling_expansion()), proof);
        value
    }
    fn quantity_dims_of_type_uncached(&mut self, ty: ElementRef) -> Option<QuantityDims> {
        let (mref, _) = self.member_of(ty, &simple_qn("mRef"))?;
        self.typings(mref)
            .into_iter()
            .find_map(|def| self.unit_def_dims(def))
    }

    /// The dimension of an evaluated [`Unit`]: each base-unit element
    /// maps through its unit definition's power factors into
    /// base-quantity space, scaled by the base unit's exponent. `None`
    /// when any base unit's dimension is not declared (an opaque user
    /// unit) — the unit is incommensurable with the library's space
    /// and consistency cannot be judged.
    pub fn unit_quantity_dims(&mut self, unit: &Unit) -> Option<QuantityDims> {
        let dims: Vec<(usize, i32, i32)> =
            unit.dims.iter().map(|d| (d.elem, d.num, d.den)).collect();
        let mut raw: Vec<(usize, i64, i64)> = Vec::new();
        for (elem, num, den) in dims {
            let base = self
                .typings(ElementRef(elem))
                .into_iter()
                .find_map(|def| self.unit_def_dims(def))?;
            for &(q, n, d) in &base.factors {
                raw.push((
                    q,
                    (n as i64).checked_mul(num as i64)?,
                    (d as i64).checked_mul(den as i64)?,
                ));
            }
        }
        normalize(raw)
    }

    /// The dimension a *unit definition* element declares: its owned
    /// `QuantityPowerFactor` members, or — the explicitly dimensionless
    /// spelling — an owned empty power-factor binding (`:>>
    /// unitPowerFactors = ()`); a definition stating neither reads
    /// through its explicit supertypes.
    fn unit_def_dims(&mut self, def: ElementRef) -> Option<QuantityDims> {
        if !self.b.semantic_ready {
            return self.unit_def_dims_uncached(def);
        }
        if let Some(hit) = self
            .b
            .semantic_memo
            .definitions
            .get(&(def.0, crate::eval::unit_spelling_expansion()))
            .cloned()
        {
            self.b.used_imports.extend(hit.imports);
            return hit.value;
        }
        let imports = std::mem::take(&mut self.b.used_imports);
        let value = self.unit_def_dims_uncached(def);
        let proof = crate::semantic_memo::Proven {
            value: value.clone(),
            imports: self.b.used_imports.iter().copied().collect(),
        };
        self.b.used_imports.extend(imports);
        self.b
            .semantic_memo
            .definitions
            .insert((def.0, crate::eval::unit_spelling_expansion()), proof);
        value
    }
    fn unit_def_dims_uncached(&mut self, def: ElementRef) -> Option<QuantityDims> {
        let qpf = self.resolve_qualified("Quantities::QuantityPowerFactor")?;
        let mut seen: HashSet<ElementRef> = HashSet::new();
        let mut queue = VecDeque::from([def]);
        while let Some(t) = queue.pop_front() {
            if !seen.insert(t) || seen.len() > 64 {
                continue;
            }
            let mut raw: Vec<(usize, i64, i64)> = Vec::new();
            let mut any = false;
            for f in self.owned_features(t) {
                if !self.typings(f).into_iter().any(|ft| self.conforms(ft, qpf)) {
                    continue;
                }
                any = true;
                let (q, exp) = self.power_factor(f)?;
                raw.push((q, exp, 1));
            }
            if any {
                return normalize(raw);
            }
            if self.explicit_empty_factors(t) {
                return Some(QuantityDims {
                    factors: Vec::new(),
                });
            }
            for s in self.explicit_supertypes(t) {
                queue.push_back(s);
            }
        }
        None
    }

    /// One `QuantityPowerFactor` member: `(base-quantity element,
    /// integer exponent)` from its bound `quantity` and `exponent`.
    fn power_factor(&mut self, f: ElementRef) -> Option<(usize, i64)> {
        let (qm, _) = self.member_of(f, &simple_qn("quantity"))?;
        let (qscope, qexpr) = self.value_expr(qm)?;
        let quantity = self.expr_element(qscope, &qexpr)?;
        let (em, _) = self.member_of(f, &simple_qn("exponent"))?;
        let (escope, eexpr) = self.value_expr(em)?;
        let exp = match self.evaluate_in(escope, &eexpr).ok()? {
            Value::Integer(i) => i64::try_from(i).ok()?,
            // A literal `2.0` canonicalizes to the integer arm; the double
            // arm covers a computed approximate integer.
            Value::Real(r) if r.fract() == 0.0 && r.abs() < i64::MAX as f64 => r as i64,
            _ => return None,
        };
        Some((quantity.0, exp))
    }

    /// The element a bound expression stands for: evaluation when it
    /// settles on an element, else a structural read of a plain
    /// reference / member-chain spelling (`isq.L`).
    fn expr_element(&mut self, scope: ScopeRef, expr: &Expr) -> Option<ElementRef> {
        if let Ok(Value::Element(e) | Value::Unbound(e) | Value::UnboundMember(e)) =
            self.evaluate_in(scope, expr)
        {
            return Some(e);
        }
        fn flatten(e: &Expr, out: &mut Vec<Name>) -> bool {
            match &e.kind {
                ExprKind::Ref(qn) => {
                    out.extend(qn.segments.iter().cloned());
                    true
                }
                ExprKind::ChainStep { target, member } => {
                    if !flatten(target, out) {
                        return false;
                    }
                    match member {
                        TargetRef::Name(qn) => {
                            out.extend(qn.segments.iter().cloned());
                            true
                        }
                        _ => false,
                    }
                }
                _ => false,
            }
        }
        let mut segments = Vec::new();
        if !flatten(expr, &mut segments) || segments.is_empty() {
            return None;
        }
        self.resolve_in(
            scope,
            &QualifiedName {
                is_global: false,
                segments,
                span: Span::default(),
            },
        )
    }

    /// Whether the element owns an *empty* power-factor binding —
    /// `:>> unitPowerFactors = ()` on the definition itself or inside
    /// its `quantityDimension` member — the library's explicit spelling
    /// of "dimension one".
    fn explicit_empty_factors(&mut self, t: ElementRef) -> bool {
        let mut hosts = vec![t];
        hosts.extend(self.owned_members(t));
        for h in hosts {
            for m in self.owned_members(h) {
                let names_factors = self.redefinition_targets(m).into_iter().any(|r| {
                    matches!(
                        self.element_name(r),
                        Some("quantityPowerFactors" | "unitPowerFactors")
                    )
                });
                if !names_factors {
                    continue;
                }
                if let Some((_, expr)) = self.value_expr(m) {
                    if matches!(&expr.kind, ExprKind::Sequence(items) if items.is_empty())
                        || matches!(&expr.kind, ExprKind::Null)
                    {
                        return true;
                    }
                }
            }
        }
        false
    }

    /// Library scalar-quantity types declaring `dims`, in deterministic
    /// preference order (shortest qualified name, then lexical — the
    /// generic base types sort ahead of their specializations). Built
    /// lazily once per resolved model; empty without a standard
    /// library.
    pub fn quantity_type_candidates(&mut self, dims: &QuantityDims) -> Vec<ElementRef> {
        self.ensure_quantity_index();
        self.quantity_index
            .as_ref()
            .and_then(|ix| ix.by_dims.get(dims))
            .map(|v| v.iter().map(|&e| ElementRef(e)).collect())
            .unwrap_or_default()
    }

    /// Library scalar-quantity types whose `mRef` is typed by `def` —
    /// the types a unit *written by name* denotes directly (`[J]` names
    /// the energy unit, so the energy type outranks everything else
    /// that merely shares its dimension). Same lazy index and ordering
    /// as [`Self::quantity_type_candidates`].
    pub fn quantity_types_for_unit_def(&mut self, def: ElementRef) -> Vec<ElementRef> {
        self.ensure_quantity_index();
        self.quantity_index
            .as_ref()
            .and_then(|ix| ix.by_unit_def.get(&def.0))
            .map(|v| v.iter().map(|&e| ElementRef(e)).collect())
            .unwrap_or_default()
    }

    fn ensure_quantity_index(&mut self) {
        if self.quantity_index.is_none() {
            let index = self.build_quantity_index();
            self.quantity_index = Some(index);
        }
    }

    fn build_quantity_index(&mut self) -> crate::json::QuantityIndex {
        let mut by_dims: HashMap<QuantityDims, Vec<usize>> = HashMap::new();
        let mut by_unit_def: HashMap<usize, Vec<usize>> = HashMap::new();
        let Some(sqv) = self.resolve_qualified("Quantities::ScalarQuantityValue") else {
            return crate::json::QuantityIndex {
                by_dims,
                by_unit_def,
            };
        };
        for e in self.elements_of_metaclass("AttributeDefinition") {
            if !self.is_library_element(e)
                || !self.conforms(e, sqv)
                || self.prefix_keywords(e).contains(&"abstract")
            {
                continue;
            }
            let Some(d) = self.quantity_dims_of_type(e) else {
                continue;
            };
            by_dims.entry(d).or_default().push(e.0);
            if let Some((mref, _)) = self.member_of(e, &simple_qn("mRef")) {
                for def in self.typings(mref) {
                    let bucket = by_unit_def.entry(def.0).or_default();
                    if !bucket.contains(&e.0) {
                        bucket.push(e.0);
                    }
                }
            }
        }
        let order = |bucket: Vec<usize>, model: &mut Self| -> Vec<usize> {
            let mut named: Vec<(usize, String)> = bucket
                .into_iter()
                .map(|e| {
                    let qn = model
                        .element_qualified_name(ElementRef(e))
                        .unwrap_or_default();
                    (e, qn)
                })
                .collect();
            named.sort_by(|a, b| (a.1.len(), &a.1).cmp(&(b.1.len(), &b.1)));
            named.into_iter().map(|(e, _)| e).collect()
        };
        for bucket in by_dims.values_mut() {
            *bucket = order(std::mem::take(bucket), self);
        }
        for bucket in by_unit_def.values_mut() {
            *bucket = order(std::mem::take(bucket), self);
        }
        crate::json::QuantityIndex {
            by_dims,
            by_unit_def,
        }
    }

    /// The scalar-value library type a plain literal value reads as
    /// (`Boolean`, `Integer`, `Real`, `String`), resolved — `None` for
    /// non-scalar values or without the standard library.
    pub fn scalar_literal_type(&mut self, v: &Value) -> Option<ElementRef> {
        let name = match v {
            Value::Boolean(_) => "Boolean",
            Value::Integer(_) => "Integer",
            Value::Rational(_) | Value::Real(_) => "Real",
            Value::String(_) => "String",
            _ => return None,
        };
        self.resolve_qualified(&format!("ScalarValues::{name}"))
    }

    /// The shortest reference spelling that resolves to `target` from
    /// `scope` — what a generated typing should write. Candidates, all
    /// verified by resolution: the simple name (visible under an
    /// import), the standard `ISQ` wrapper package's re-export, and
    /// every qualified suffix up to the full owner chain. `None` when
    /// nothing resolves to the target from there.
    pub fn type_spelling_at(
        &mut self,
        dialect: Option<Dialect>,
        scope: ScopeRef,
        target: ElementRef,
    ) -> Option<String> {
        self.reference_spelling_at(dialect, scope, None, target)
    }

    /// [`Self::type_spelling_at`] for an arbitrary reference site: the
    /// shortest spelling resolving to `target` from `scope` with the
    /// site's resolution exclusion applied (a feature's own
    /// specialization targets and value must not capture the feature
    /// itself — `RefSite::exclude`).
    pub fn reference_spelling_at(
        &mut self,
        dialect: Option<Dialect>,
        scope: ScopeRef,
        exclude: Option<ElementRef>,
        target: ElementRef,
    ) -> Option<String> {
        let chain = self.owner_name_chain(target)?;
        let simple = chain.last()?.clone();
        let mut candidates: Vec<Vec<String>> = vec![vec![simple.clone()]];
        candidates.push(vec!["ISQ".to_string(), simple]);
        for i in (0..chain.len().saturating_sub(1)).rev() {
            candidates.push(chain[i..].to_vec());
        }
        let mut spelled: Vec<(String, Vec<String>)> = candidates
            .into_iter()
            .map(|segs| (spell_segments(dialect, &segs), segs))
            .collect();
        spelled.sort_by(|a, b| (a.0.len(), &a.0).cmp(&(b.0.len(), &b.0)));
        spelled.dedup_by(|a, b| a.0 == b.0);
        for (spelling, segs) in spelled {
            if self.resolve_in_excluding(scope, &segments_qn(segs), exclude) == Some(target) {
                return Some(spelling);
            }
        }
        None
    }

    /// The fully qualified spelling of `target` — its named owner chain
    /// from the document root, each segment spelled for `dialect` (see
    /// `spell_segments`). `None` for anonymous elements.
    pub fn full_spelling(
        &mut self,
        dialect: Option<Dialect>,
        target: ElementRef,
    ) -> Option<String> {
        Some(spell_segments(dialect, &self.owner_name_chain(target)?))
    }

    /// Whether `segments` (raw name values, unescaped) resolve to
    /// `target` from `scope` under the site's exclusion — the validity
    /// gate every generated respelling passes before it becomes an
    /// edit.
    pub fn segments_resolve_to(
        &mut self,
        scope: ScopeRef,
        exclude: Option<ElementRef>,
        segments: &[String],
        target: ElementRef,
    ) -> bool {
        !segments.is_empty()
            && self.resolve_in_excluding(scope, &segments_qn(segments.to_vec()), exclude)
                == Some(target)
    }

    /// `target`'s named owner chain, root-first, ending in its own
    /// name. `None` when the element itself is anonymous.
    fn owner_name_chain(&mut self, target: ElementRef) -> Option<Vec<String>> {
        let mut chain: Vec<String> = vec![self.element_name(target)?.to_string()];
        let mut cur = target;
        while let Some(o) = self.owner(cur) {
            if let Some(n) = self.element_name(o) {
                chain.push(n.to_string());
            }
            cur = o;
        }
        chain.reverse();
        Some(chain)
    }
}

/// Spell raw segment names as a source reference (`::`-joined). Reserved
/// words of `dialect` — the unit the text is spliced into — and
/// non-identifier segments are quoted, so the result re-parses there
/// and the formatter leaves it alone; `None` quotes the words of either
/// dialect for text without a known destination.
fn spell_segments(dialect: Option<Dialect>, segments: &[String]) -> String {
    sysmlv2_syntax::name::spell_path(dialect, segments)
}

fn segments_qn(segments: Vec<String>) -> QualifiedName {
    QualifiedName {
        is_global: false,
        segments: segments
            .into_iter()
            .map(|value| Name {
                value,
                span: Span::default(),
            })
            .collect(),
        span: Span::default(),
    }
}

impl ResolvedModel {
    pub(crate) fn prepare_quantity_memo(&mut self) {
        let imports = self.b.used_imports.clone();
        let unit_type = self.resolve_qualified("Quantities::MeasurementUnit");
        if let Some(unit_type) = unit_type {
            for e in 0..self.b.elements.len() {
                if crate::metaclass::conforms(self.b.elements[e].ty, "DataType") {
                    self.quantity_dims_of_type(ElementRef(e));
                    if self.conforms(ElementRef(e), unit_type) {
                        self.unit_def_dims(ElementRef(e));
                    }
                } else if crate::metaclass::conforms(self.b.elements[e].ty, "Feature")
                    && self
                        .typings(ElementRef(e))
                        .into_iter()
                        .any(|t| self.conforms(t, unit_type))
                {
                    crate::eval::prepare_unit(&mut self.b, e);
                }
            }
        }
        self.b.used_imports = imports;
    }
}

#[cfg(test)]
mod memo_tests {
    use super::*;
    #[test]
    fn dimensions_match_uncached_queries_and_replay_complete_import_evidence() {
        let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../../spec-refs/SysML-v2-Release/sysml.library");
        if !path.exists() {
            return;
        }
        let mut model = crate::model::Model::new();
        model.load_library_dir(&path).unwrap();
        let mut r = ResolvedModel::build(&model);
        for name in [
            "ISQ::AccelerationValue",
            "ISQ::LengthValue",
            "ISQ::MassValue",
            "ScalarValues::Real",
        ] {
            let ty = r.resolve_qualified(name).unwrap();
            r.b.semantic_ready = false;
            r.b.used_imports.clear();
            let expected = r.quantity_dims_of_type(ty);
            let imports = r.b.used_imports.clone();
            r.b.semantic_ready = true;
            assert_eq!(r.quantity_dims_of_type(ty), expected);
            assert!(
                r.b.semantic_memo
                    .types
                    .get(&(ty.0, crate::eval::unit_spelling_expansion()))
                    .is_some()
            );
            r.b.used_imports.clear();
            assert_eq!(r.quantity_dims_of_type(ty), expected);
            assert_eq!(r.b.used_imports, imports, "{name}");
        }
    }
}
