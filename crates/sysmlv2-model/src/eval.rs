//! Model-level expression evaluation.
//!
//! Evaluates syntax expressions against the resolved element graph:
//! literals, arithmetic/logical/comparison operators, ranges, sequences,
//! conditionals and null-coalescing, feature references (following bound
//! feature values, cycle-guarded, with redefinition shadowing coming from
//! scope lookup itself), feature-chain steps, and the commonly used Kernel
//! Function Library intrinsics — including the control functions
//! (`collect`/`select`/`reject`/`forAll`/`exists`/`reduce`) with `{ … }`
//! lambda bodies.
//!
//! KerML values are sequences; here scalars are singleton values and
//! `null`/`()` is the empty [`Value::Sequence`]. Intrinsics are matched by
//! the *last segment* of the invoked name (the Kernel Function Library
//! names are treated as reserved), so models evaluated without the library
//! loaded still compute. User-defined calculations — any resolvable element
//! whose body carries a trailing result expression — invoke with
//! positional and named arguments (parameters bind like lambda
//! parameters; recursion is allowed to a fixed depth). Quantity brackets
//! (`10 [mm]`) evaluate to [`Value::Quantity`]: units normalize to
//! exponent maps over base unit elements with a scale (derived-unit
//! definitions like `N = kg*m/s^2` expand; library `unitConversion`
//! declarations make `min` ≡ `{s}`×60 and `km` ≡ `{m}`×1000), so
//! same-dimension arithmetic and comparison *convert* across scales,
//! `*`/`/`/`**` combine exponents and cancel (folding scales into the
//! number), and different *dimensions* never mix.
//!
//! Constructors (`new T(…)`) build [`Value::Instance`] data values:
//! positional arguments bind the type's own value-less data usages in
//! declaration order, named arguments bind by name, equality is
//! structural, and chain steps read the bound fields.
//!
//! Classification (`istype`/`hastype`/`as`) evaluates with open-world
//! discipline: declared-conformance hits are definite, misses on model
//! features are undecided (the instance may be more specific), and only
//! closed values (constructed instances, scalar literals) answer false.
//!
//! Metadata reflection (KerML 9.2): `X.metadata` evaluates to the
//! element's metaobjects — its metadata annotations (each standing for
//! an instance of its metadata definition) plus an instance of the
//! element's own reflective metaclass (`SysML::PartDefinition` …)
//! carrying the serialized scalar properties as fields. `x meta M`
//! filters those metaobjects to the ones conforming to `M`, `x @@ M`
//! tests that they all conform, and `x @ M` is the annotation test the
//! import-filter machinery answers (with the reflection-metaclass
//! fallback). Misses are definite against reflection metaclasses and
//! user-defined types; other library targets stay undecided.
//!
//! Documented v1 gaps (all reported as [`EvalError::Unsupported`]):
//! extents (`all T`).

use crate::json::{Builder, ElementRef, ResolvedModel, Tri};

/// Owner-context library collections per member metaclass — the
/// systems library's counterpart rows of SysML 8.4.2 Table 32 (the
/// kind-keyed rows come from [`crate::json::implicit_usage_bases`]).
/// Matched against the accessed member, so a row only ever fires when
/// the receiver actually owns members of the kind.
fn implied_collection_extras(metaclass: &str) -> &'static [&'static str] {
    match metaclass {
        "PerformActionUsage" => &["Parts::Part::performedActions"],
        "ExhibitStateUsage" => &["Parts::Part::exhibitedStates"],
        "IncludeUseCaseUsage" => &["UseCases::UseCase::includedUseCases"],
        "ActionUsage" => &["Actions::Action::subactions"],
        "StateUsage" => &["States::StateAction::substates"],
        _ => &[],
    }
}
use std::collections::{HashMap, HashSet};
use std::fmt;
use sysmlv2_syntax::Span;
use sysmlv2_syntax::ast::*;

pub use crate::rational::Rational;

/// An evaluated value. KerML's `null` is the empty sequence.
#[derive(Clone, Debug, PartialEq)]
pub enum Value {
    Boolean(bool),
    Integer(i128),
    /// An exact rational that is not an integer in `i128` range —
    /// integral values in range are always [`Value::Integer`].
    Rational(Rational),
    /// An approximate binary double: the result of a transcendental
    /// function, a non-exact power or root, or infinity. Any operation
    /// with a `Real` operand is approximate; everything else is exact.
    Real(f64),
    String(String),
    /// A model element used as a *closed* value: an enum literal, a
    /// query-mode reflection result, or a collected member standing for
    /// itself.
    Element(ElementRef),
    /// A placeholder for the *unknown* value of an unbound feature:
    /// member access, chains, and classification treat it like the
    /// element itself, but cardinality/emptiness questions refuse to
    /// fabricate answers (the declared multiplicity answers when it is
    /// exact). Defaults read through a parameter or reference that still
    /// stands for an argument are indeterminate. Minted only for features
    /// outside library evaluation frames — library calc bodies keep the
    /// closed one-element convention their semantics rely on.
    Unbound(ElementRef),
    /// An unvalued member reached through an unknown receiver. Like
    /// [`Value::Unbound`], but retains the receiver's uncertainty through
    /// aliases, conditionals, sequences and calculation arguments. A
    /// later chain step must not read the member type's defaults.
    UnboundMember(ElementRef),
    /// The result of an operation over an unknown operand: arithmetic,
    /// comparison, or logic over an unbound feature is not a type error —
    /// the formula is parametric and its value simply is not determined.
    /// Strictly propagating (any operation over an indeterminate value is
    /// indeterminate; a boolean context reads it as *unknown*, never as a
    /// fabricated `true`/`false`), and classified as undecided by
    /// constraint verdicts. Unlike [`Value::Unbound`] it carries no
    /// element: member access on it has nothing to resolve against.
    Indeterminate,
    /// A quantity `num [unit]`. Same-unit quantities add, subtract, and
    /// compare on their numbers; scalars scale them; mixing *different*
    /// units is a type error (no unit conversion), except `*`/`/`, which
    /// combine the units structurally.
    Quantity(Box<Value>, Unit),
    /// A constructed instance (`new T(…)`): the type, its declared name
    /// (display), and the bound fields. Attribute instances are data
    /// values — equality is structural (same type, same fields) — and
    /// chain steps read the bound fields.
    Instance {
        ty: ElementRef,
        ty_name: String,
        fields: Vec<(String, Value)>,
    },
    Sequence(Vec<Value>),
}

/// One base factor of a normalized unit: a resolved unit element raised
/// to a reduced rational exponent (`den > 0`, `num != 0`, gcd 1). The
/// name is the element's simple name, kept for display only — identity
/// is the element.
#[derive(Clone, Debug, PartialEq, serde::Serialize, serde::Deserialize)]
pub(crate) struct Dim {
    pub(crate) elem: usize,
    pub(crate) name: String,
    pub(crate) num: i32,
    pub(crate) den: i32,
}

/// A measurement unit attached to a [`Value::Quantity`]: a canonical
/// exponent map over resolved *base* unit elements (sorted by element)
/// plus a `scale` — the multiplier taking this unit's magnitudes to the
/// reference magnitude. A named unit whose own definition is a pure
/// power product of other units expands recursively (`'m⋅s⁻¹'` ≡ `m/s`,
/// `N` ≡ `kg*m/s**2`); a unit with a library-declared `unitConversion`
/// (factor + reference unit, or prefix) normalizes to its reference
/// dimensions with the factor as scale (`min` is `{s}`×60, `km` is
/// `{m}`×1000), so same-dimension quantities *convert* at operation
/// boundaries; anything else is an opaque base. Two units are the same
/// unit iff dims and scale agree; same dims with different scales
/// convert, different dims are a type error.
#[derive(Clone, Debug)]
pub struct Unit {
    pub(crate) dims: Vec<Dim>,
    pub(crate) scale: Rational,
    pub(crate) display: String,
}

impl Unit {
    /// A reference-magnitude unit (scale 1) with the canonical display:
    /// what arithmetic produces after folding scales into the number.
    pub(crate) fn from_dims(dims: Vec<Dim>) -> Unit {
        let merged = normalize_dims(dims);
        let display = render_dims(&merged);
        Unit {
            dims: merged,
            scale: Rational::one(),
            display,
        }
    }

    /// Canonical identity key — units are equal iff their keys are.
    pub fn key(&self) -> String {
        use std::fmt::Write as _;
        let mut out = self.dims_key();
        if !self.scale.is_one() {
            let _ = write!(out, "x{};", self.scale);
        }
        out
    }

    /// The dimensional part of the key alone — two units with equal
    /// `dims_key` but different [`Self::scale`]s measure the same
    /// dimension and *convert* into one another.
    pub fn dims_key(&self) -> String {
        let mut out = String::new();
        for d in &self.dims {
            use std::fmt::Write;
            let _ = write!(out, "e{}^{}/{};", d.elem, d.num, d.den);
        }
        out
    }

    /// Multiplier taking this unit's magnitudes to the reference
    /// magnitude (`min` → 60, base units → 1). Exact: library
    /// conversion factors are decimals, small fractions and integer
    /// powers, and every composition of them stays a rational.
    pub fn scale(&self) -> &Rational {
        &self.scale
    }

    /// Display spelling: the source spelling for bracket-constructed
    /// units (`km/h`), the canonical reference rendering for
    /// arithmetic results (`kg*m/s**2`, `1/h`, `m**(1/2)`).
    pub fn display(&self) -> &str {
        &self.display
    }
}

/// Dimensional equality — same exponent map, ignoring scale. Same dims
/// with different scales are *convertible*, not equal.
fn same_dims(a: &Unit, b: &Unit) -> bool {
    a.dims.len() == b.dims.len()
        && a.dims
            .iter()
            .zip(&b.dims)
            .all(|(x, y)| x.elem == y.elem && x.num == y.num && x.den == y.den)
}

impl PartialEq for Unit {
    fn eq(&self, other: &Unit) -> bool {
        same_dims(self, other) && self.scale == other.scale
    }
}

/// Process-wide switch for expanding *spelled* power-product unit names:
/// a quoted unit whose element carries neither a `unitConversion` nor a
/// power-product definition, but whose own spelling is systematic
/// (`'m³⋅s⁻²'`, `'kg⋅m⋅s⁻¹'`), expands by parsing the name — so it
/// converts against the units it is spelled from instead of standing as
/// an incommensurable opaque base. On by default; every host surface
/// (CLI flag, binding call, IDE setting) exposes the opt-out for models
/// that rely on such spellings staying opaque.
static UNIT_SPELLING_EXPANSION: std::sync::atomic::AtomicBool =
    std::sync::atomic::AtomicBool::new(true);

/// Enable or disable spelled power-product unit expansion (default on).
pub fn set_unit_spelling_expansion(on: bool) {
    UNIT_SPELLING_EXPANSION.store(on, std::sync::atomic::Ordering::Relaxed);
}

/// Whether spelled power-product unit expansion is enabled.
pub fn unit_spelling_expansion() -> bool {
    UNIT_SPELLING_EXPANSION.load(std::sync::atomic::Ordering::Relaxed)
}

/// Parse a unit-name spelling that is itself a power product —
/// `'m³⋅s⁻²'`, `'kg⋅m⋅s⁻¹'`, `'Bq/m³'` — into (symbol, exponent)
/// factors: symbols separated by `⋅`/`·`/`*` (multiply) or `/` (the
/// next factor divides), each with an optional superscript exponent.
/// `None` when the name is not such a spelling — a single bare symbol
/// (that is just the unit's own name) or anything beyond the notation
/// (grouping parentheses, spaces). Public for style tooling (the
/// unit-spelling lint) — expansion itself goes through evaluation.
pub fn parse_unit_spelling(name: &str) -> Option<Vec<(String, i32)>> {
    fn sup_digit(c: char) -> Option<i32> {
        Some(match c {
            '⁰' => 0,
            '¹' => 1,
            '²' => 2,
            '³' => 3,
            '⁴' => 4,
            '⁵' => 5,
            '⁶' => 6,
            '⁷' => 7,
            '⁸' => 8,
            '⁹' => 9,
            _ => return None,
        })
    }
    struct Factor {
        base: String,
        mag: Option<i32>,
        neg: bool,
    }
    impl Factor {
        fn flush(&mut self, invert: bool, out: &mut Vec<(String, i32)>) -> bool {
            if self.base.is_empty() {
                return false;
            }
            let mut e = self.mag.unwrap_or(1);
            if self.neg {
                e = -e;
            }
            if invert {
                e = -e;
            }
            out.push((std::mem::take(&mut self.base), e));
            self.mag = None;
            self.neg = false;
            true
        }
    }
    let mut out: Vec<(String, i32)> = Vec::new();
    let mut f = Factor {
        base: String::new(),
        mag: None,
        neg: false,
    };
    // Whether the factor being read follows a `/`.
    let mut invert = false;
    for c in name.chars() {
        match c {
            '⋅' | '·' | '*' => {
                if !f.flush(invert, &mut out) {
                    return None;
                }
                invert = false;
            }
            '/' => {
                if !f.flush(invert, &mut out) {
                    return None;
                }
                invert = true;
            }
            '⁻' => {
                if f.base.is_empty() || f.mag.is_some() || f.neg {
                    return None;
                }
                f.neg = true;
            }
            c if let Some(d) = sup_digit(c) => {
                if f.base.is_empty() {
                    return None;
                }
                f.mag = Some(f.mag.unwrap_or(0).checked_mul(10)?.checked_add(d)?);
            }
            c => {
                // A base character after a superscript (or a construct
                // beyond the notation) means this is not a spelled
                // product.
                if f.mag.is_some() || f.neg || c.is_whitespace() || c == '(' || c == ')' {
                    return None;
                }
                f.base.push(c);
            }
        }
    }
    if !f.flush(invert, &mut out) {
        return None;
    }
    // A single bare factor is the unit's own name, not a product.
    if out.len() == 1 && out[0].1 == 1 {
        return None;
    }
    Some(out)
}

/// Merge duplicate elements, drop zero exponents, sort by element.
fn normalize_dims(dims: Vec<Dim>) -> Vec<Dim> {
    let mut merged: Vec<Dim> = Vec::with_capacity(dims.len());
    for d in dims {
        match merged.iter_mut().find(|m| m.elem == d.elem) {
            Some(m) => (m.num, m.den) = exp_add((m.num, m.den), (d.num, d.den)),
            None => merged.push(d),
        }
    }
    merged.retain(|d| d.num != 0);
    merged.sort_by_key(|d| d.elem);
    merged
}

fn gcd(a: i64, b: i64) -> i64 {
    let (mut a, mut b) = (a.abs(), b.abs());
    while b != 0 {
        (a, b) = (b, a % b);
    }
    a.max(1)
}

/// Reduced rational sum of two exponents.
fn exp_add((an, ad): (i32, i32), (bn, bd): (i32, i32)) -> (i32, i32) {
    let n = an as i64 * bd as i64 + bn as i64 * ad as i64;
    let d = ad as i64 * bd as i64;
    let g = gcd(n, d);
    ((n / g) as i32, (d / g) as i32)
}

/// Reduced rational product of two exponents.
fn exp_mul((an, ad): (i32, i32), (bn, bd): (i32, i32)) -> (i32, i32) {
    let n = an as i64 * bn as i64;
    let d = ad as i64 * bd as i64;
    let g = gcd(n, d);
    ((n / g) as i32, (d / g) as i32)
}

/// Combine two dimension vectors: `b`'s exponents scaled by `sign` (1
/// for `*`, -1 for `/`) merge into `a`'s.
fn dims_combine(a: &[Dim], b: &[Dim], sign: i32) -> Vec<Dim> {
    let mut out = a.to_vec();
    out.extend(b.iter().map(|d| Dim {
        elem: d.elem,
        name: d.name.clone(),
        num: d.num * sign,
        den: d.den,
    }));
    out
}

/// Raise a dimension vector to a rational power.
fn dims_pow(dims: &[Dim], exp: (i32, i32)) -> Vec<Dim> {
    dims.iter()
        .map(|d| {
            let (num, den) = exp_mul((d.num, d.den), exp);
            Dim {
                elem: d.elem,
                name: d.name.clone(),
                num,
                den,
            }
        })
        .collect()
}

/// A numeric value as a reduced small rational, for unit exponents:
/// integers directly, exact rationals with a denominator up to 16 and a
/// numerator up to 1024 in magnitude (`^(1/2)` after rational division
/// is 1/2). An approximate double counts as the small fraction whose
/// nearest double it is, so a computed `0.5` or `0.1` still names a
/// root; its exact dyadic expansion would never have a small
/// denominator.
fn small_ratio(v: &Value) -> Option<(i32, i32)> {
    let small = |n: i32, d: i32| (d <= 16 && n.abs() <= 1024).then_some((n, d));
    match v.num()? {
        Num::Exact(r) => {
            let (n, d) = r.to_i32_parts()?;
            small(n, d)
        }
        Num::Approx(f) => (1..=16i32).find_map(|den| {
            let n = f * den as f64;
            (n.fract() == 0.0 && n.abs() <= 1024.0 && (n as i32 as f64 / den as f64) == f)
                .then(|| {
                    let g = gcd(n as i64, den as i64);
                    ((n as i64 / g) as i32, (den as i64 / g) as i32)
                })
                .and_then(|(n, d)| small(n, d))
        }),
    }
}

/// `a / b` for unit scales, which are never zero.
fn scale_ratio(a: &Rational, b: &Rational) -> Rational {
    a.div(b).unwrap_or_else(Rational::one)
}

/// An integer-literal unit exponent, allowing the negated spelling the
/// library uses (`s^-1`).
fn unit_exponent(e: &Expr) -> Option<i32> {
    match &e.kind {
        ExprKind::Literal(Literal::Integer(k)) => k.parse().ok(),
        ExprKind::Unary {
            op: UnaryOp::Minus,
            operand,
        } => match &operand.kind {
            ExprKind::Literal(Literal::Integer(k)) => k.parse::<i32>().ok().map(|k| -k),
            _ => None,
        },
        _ => None,
    }
}

/// Render a canonical display: positive-exponent factors (sorted by
/// name) joined with `*`, negative ones after `/` (parenthesized when
/// compound), fractional exponents as `**(n/d)`.
fn render_dims(dims: &[Dim]) -> String {
    let factor = |d: &Dim| {
        let n = d.num.abs();
        if n == 1 && d.den == 1 {
            d.name.clone()
        } else if d.den == 1 {
            format!("{}**{}", d.name, n)
        } else {
            format!("{}**({}/{})", d.name, n, d.den)
        }
    };
    let mut pos: Vec<String> = dims.iter().filter(|d| d.num > 0).map(factor).collect();
    let mut neg: Vec<String> = dims.iter().filter(|d| d.num < 0).map(factor).collect();
    pos.sort();
    neg.sort();
    let head = if pos.is_empty() {
        "1".to_string()
    } else {
        pos.join("*")
    };
    match neg.len() {
        0 => head,
        1 => format!("{head}/{}", neg[0]),
        _ => format!("{head}/({})", neg.join("*")),
    }
}

impl Value {
    fn null() -> Value {
        Value::Sequence(Vec::new())
    }

    fn is_null(&self) -> bool {
        matches!(self, Value::Sequence(s) if s.is_empty())
    }

    /// Flatten into a sequence of scalars (KerML sequences are flat).
    pub(crate) fn items(self) -> Vec<Value> {
        match self {
            Value::Sequence(s) => s.into_iter().flat_map(Value::items).collect(),
            v => vec![v],
        }
    }

    fn as_f64(&self) -> Option<f64> {
        self.num().map(|n| n.to_f64())
    }

    /// The scalar number this value is, if it is one.
    pub(crate) fn num(&self) -> Option<Num> {
        match self {
            Value::Integer(i) => Some(Num::Exact(Rational::from_integer(*i))),
            Value::Rational(r) => Some(Num::Exact(r.clone())),
            Value::Real(f) => Some(Num::Approx(*f)),
            _ => None,
        }
    }

    /// The canonical value of a number: an exact integer in `i128` range
    /// is [`Value::Integer`], any other exact value [`Value::Rational`],
    /// an approximate one [`Value::Real`].
    pub(crate) fn from_num(n: Num) -> Value {
        match n {
            Num::Exact(r) => match r.to_i128() {
                Some(i) => Value::Integer(i),
                None => Value::Rational(r),
            },
            Num::Approx(f) => Value::Real(f),
        }
    }
}

/// A scalar number as the evaluator computes with it: exact, or an
/// explicitly approximate double. Exact operands give exact results;
/// one approximate operand makes the result approximate. Comparisons
/// are exact in every combination — a finite double compares as the
/// dyadic rational it denotes.
#[derive(Clone, Debug)]
pub(crate) enum Num {
    Exact(Rational),
    Approx(f64),
}

impl Num {
    fn to_f64(&self) -> f64 {
        match self {
            Num::Exact(r) => r.to_f64(),
            Num::Approx(f) => *f,
        }
    }

    /// The exact value: itself, or the dyadic rational of a finite
    /// double; `None` for infinities and NaN.
    fn exact(&self) -> Option<Rational> {
        match self {
            Num::Exact(r) => Some(r.clone()),
            Num::Approx(f) => Rational::from_f64(*f),
        }
    }

    fn is_zero(&self) -> bool {
        match self {
            Num::Exact(r) => r.is_zero(),
            Num::Approx(f) => *f == 0.0,
        }
    }

    fn is_one(&self) -> bool {
        match self {
            Num::Exact(r) => r.is_one(),
            Num::Approx(f) => *f == 1.0,
        }
    }

    fn is_negative(&self) -> bool {
        match self {
            Num::Exact(r) => r.is_negative(),
            Num::Approx(f) => *f < 0.0,
        }
    }

    fn add(&self, o: &Num) -> Num {
        match (self, o) {
            (Num::Exact(a), Num::Exact(b)) => Num::Exact(a.add(b)),
            _ => Num::Approx(self.to_f64() + o.to_f64()),
        }
    }

    fn sub(&self, o: &Num) -> Num {
        match (self, o) {
            (Num::Exact(a), Num::Exact(b)) => Num::Exact(a.sub(b)),
            _ => Num::Approx(self.to_f64() - o.to_f64()),
        }
    }

    fn mul(&self, o: &Num) -> Num {
        match (self, o) {
            (Num::Exact(a), Num::Exact(b)) => Num::Exact(a.mul(b)),
            _ => Num::Approx(self.to_f64() * o.to_f64()),
        }
    }

    fn div(&self, o: &Num) -> Result<Num, EvalError> {
        if o.is_zero() {
            return Err(EvalError::DivisionByZero);
        }
        Ok(match (self, o) {
            (Num::Exact(a), Num::Exact(b)) => Num::Exact(a.div(b).expect("non-zero divisor")),
            _ => Num::Approx(self.to_f64() / o.to_f64()),
        })
    }

    /// Truncated remainder.
    fn rem(&self, o: &Num) -> Result<Num, EvalError> {
        if o.is_zero() {
            return Err(EvalError::DivisionByZero);
        }
        Ok(match (self, o) {
            (Num::Exact(a), Num::Exact(b)) => Num::Exact(a.rem(b).expect("non-zero divisor")),
            _ => Num::Approx(self.to_f64() % o.to_f64()),
        })
    }

    /// `self ** e`: exact for an integer exponent and for a rational
    /// exponent whose root exists, otherwise a double power.
    fn pow(&self, e: &Num) -> Num {
        if let (Num::Exact(a), Num::Exact(b)) = (self, e) {
            let exact = match b.to_i128().and_then(|k| i32::try_from(k).ok()) {
                Some(k) => a.pow(k),
                None => a.pow_rational(b),
            };
            if let Some(r) = exact {
                return Num::Exact(r);
            }
        }
        Num::Approx(self.to_f64().powf(e.to_f64()))
    }

    /// The `n`-th root: exact when it exists, otherwise a double root.
    fn root(&self, n: u32) -> Num {
        if let Num::Exact(a) = self {
            if let Some(r) = a.root(n) {
                return Num::Exact(r);
            }
        }
        let f = self.to_f64();
        Num::Approx(if n == 2 {
            f.sqrt()
        } else {
            f.powf(1.0 / n as f64)
        })
    }

    fn neg(&self) -> Num {
        match self {
            Num::Exact(r) => Num::Exact(r.neg()),
            Num::Approx(f) => Num::Approx(-f),
        }
    }

    fn abs(&self) -> Num {
        match self {
            Num::Exact(r) => Num::Exact(r.abs()),
            Num::Approx(f) => Num::Approx(f.abs()),
        }
    }

    /// Multiply by an exact factor (a unit scale).
    fn scale(&self, s: &Rational) -> Num {
        self.mul(&Num::Exact(s.clone()))
    }

    /// The greatest integer not above the value; `None` for a non-finite
    /// double.
    fn floor(&self) -> Option<Num> {
        self.exact().map(|r| Num::Exact(r.floor()))
    }

    /// The nearest integer, halves away from zero; `None` for a
    /// non-finite double.
    fn round(&self) -> Option<Num> {
        self.exact().map(|r| Num::Exact(r.round()))
    }

    /// Exact ordering; `None` only when a NaN is involved.
    fn cmp(&self, o: &Num) -> Option<std::cmp::Ordering> {
        match (self, o) {
            (Num::Exact(a), Num::Exact(b)) => Some(a.cmp(b)),
            _ => match (self.exact(), o.exact()) {
                (Some(a), Some(b)) => Some(a.cmp(&b)),
                _ => self.to_f64().partial_cmp(&o.to_f64()),
            },
        }
    }

    fn eq(&self, o: &Num) -> bool {
        self.cmp(o) == Some(std::cmp::Ordering::Equal)
    }
}

impl Value {
    /// `Display`, except that a rational without a terminating decimal
    /// expansion shows as an approximate decimal (`≈0.3333333333333333`)
    /// instead of a fraction. For glanceable surfaces such as editor
    /// hints; `Display` stays exact and re-parseable.
    pub fn to_approx_string(&self) -> String {
        match self {
            Value::Rational(r) => r.to_approx_string(),
            Value::Quantity(n, u) => format!("{} [{}]", n.to_approx_string(), u.display),
            Value::Instance {
                ty_name, fields, ..
            } => {
                let fields = fields
                    .iter()
                    .map(|(name, v)| format!("{name} = {}", v.to_approx_string()))
                    .collect::<Vec<_>>()
                    .join(", ");
                format!("{ty_name}({fields})")
            }
            Value::Sequence(s) if !s.is_empty() => {
                let items = s
                    .iter()
                    .map(Value::to_approx_string)
                    .collect::<Vec<_>>()
                    .join(", ");
                format!("({items})")
            }
            v => v.to_string(),
        }
    }
}

impl fmt::Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Value::Boolean(b) => write!(f, "{b}"),
            Value::Integer(i) => write!(f, "{i}"),
            Value::Rational(r) => write!(f, "{r}"),
            Value::Real(r) => write!(f, "{r}"),
            Value::String(s) => write!(f, "{s:?}"),
            Value::Element(_) => write!(f, "<element>"),
            Value::Unbound(_) | Value::UnboundMember(_) => write!(f, "<unbound feature>"),
            Value::Indeterminate => write!(f, "<indeterminate>"),
            Value::Quantity(n, u) => write!(f, "{n} [{}]", u.display),
            Value::Instance {
                ty_name, fields, ..
            } => {
                write!(f, "{ty_name}(")?;
                for (i, (name, v)) in fields.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{name} = {v}")?;
                }
                write!(f, ")")
            }
            Value::Sequence(s) if s.is_empty() => write!(f, "null"),
            Value::Sequence(s) => {
                write!(f, "(")?;
                for (i, v) in s.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{v}")?;
                }
                write!(f, ")")
            }
        }
    }
}

#[derive(Clone, Debug, PartialEq)]
pub enum EvalError {
    /// A referenced name did not resolve.
    Unresolved(String),
    /// The construct is outside the evaluator's supported fragment.
    Unsupported(String),
    /// Operand type mismatch.
    Type(String),
    /// A feature's value (transitively) references itself.
    Cycle(String),
    DivisionByZero,
    /// The evaluation budget ([`MAX_STEPS`], [`MAX_SEQUENCE`],
    /// [`MAX_STRING`], [`MAX_ALLOCATION`], [`MAX_CALL_DEPTH`]) was
    /// exceeded.
    Budget(String),
}

impl std::error::Error for EvalError {}

impl fmt::Display for EvalError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            EvalError::Unresolved(n) => write!(f, "unresolved reference `{n}`"),
            EvalError::Unsupported(w) => write!(f, "unsupported for evaluation: {w}"),
            EvalError::Type(m) => write!(f, "type error: {m}"),
            EvalError::Cycle(n) => write!(f, "cyclic feature value involving `{n}`"),
            EvalError::DivisionByZero => write!(f, "division by zero"),
            EvalError::Budget(w) => write!(f, "evaluation budget exceeded: {w}"),
        }
    }
}

type Result_ = Result<Value, EvalError>;

/// A control function's per-item computation: a `{ … }` lambda body, or
/// a referenced function (`->reduce '+'`, `->minimize someCalc`).
enum Applier<'a> {
    Lambda(&'a Expr),
    FnRef(&'a QualifiedName),
}

/// Evaluate an arbitrary expression in `scope` (used by semantic checks,
/// e.g. multiplicity bounds).
pub(crate) fn evaluate_expr_in(b: &mut Builder, scope: usize, e: &Expr) -> Result_ {
    Evaluator {
        b,
        env: Vec::new(),
        in_progress: HashSet::new(),
        overrides: HashMap::new(),
        unbound_receiver: None,
        lib_frames: 0,
        call_depth: 0,
        steps: 0,
        allocated: 0,
        query: false,
    }
    .expr(scope, e)
}

/// [`evaluate_expr_in`] with feature-value overrides: elements in
/// `overrides` evaluate to the given value instead of their bound (or
/// unbound) feature value — how a satisfaction claim binds a
/// requirement's subject to the satisfying feature before the
/// requirement's constraints evaluate.
pub(crate) fn evaluate_expr_with(
    b: &mut Builder,
    scope: usize,
    e: &Expr,
    overrides: HashMap<usize, Value>,
) -> Result_ {
    Evaluator {
        b,
        env: Vec::new(),
        in_progress: HashSet::new(),
        overrides,
        unbound_receiver: None,
        lib_frames: 0,
        call_depth: 0,
        steps: 0,
        allocated: 0,
        query: false,
    }
    .expr(scope, e)
}

/// The measurement [`Unit`] denoted by a bracket's unit expression
/// (`[mm]`, `[km/h]`, `[N*m]`), with references resolving from `scope`.
/// The unit expression evaluates on its own — the magnitude may be
/// anything, including unbound (which is why this entry exists: the
/// solver tags quantity terms whose magnitudes it cannot fold).
pub(crate) fn unit_of_expr_in(b: &mut Builder, scope: usize, e: &Expr) -> Result<Unit, EvalError> {
    Evaluator {
        b,
        env: Vec::new(),
        in_progress: HashSet::new(),
        overrides: HashMap::new(),
        unbound_receiver: None,
        lib_frames: 0,
        call_depth: 0,
        steps: 0,
        allocated: 0,
        query: false,
    }
    .unit_of(scope, e)
}

/// Evaluate an ad-hoc *query* expression in `scope`: like
/// [`evaluate_expr_in`], plus the query-mode extensions — closed-world
/// element classification (`istype` against a user-defined type answers
/// `false` on a miss: the operand is the declaration itself, not a
/// possibly-more-specific instance) and the reflection intrinsics
/// `ownedMember(x)` / `ownedFeature(x)`. Model-file evaluation semantics
/// are untouched; see `ResolvedModel::query`.
pub(crate) fn evaluate_query_in(b: &mut Builder, scope: usize, e: &Expr) -> Result_ {
    Evaluator {
        b,
        env: Vec::new(),
        in_progress: HashSet::new(),
        overrides: HashMap::new(),
        unbound_receiver: None,
        lib_frames: 0,
        call_depth: 0,
        steps: 0,
        allocated: 0,
        query: true,
    }
    .expr(scope, e)
}

/// [`evaluate_query_in`] with an initial environment: `env` binds names
/// the expression may reference (a template's loop variables and
/// inputs), innermost last — the rendering backend's entry point.
pub(crate) fn evaluate_query_with_env(
    b: &mut Builder,
    scope: usize,
    e: &Expr,
    env: Vec<(String, Value)>,
) -> Result_ {
    Evaluator {
        b,
        env,
        in_progress: HashSet::new(),
        overrides: HashMap::new(),
        unbound_receiver: None,
        lib_frames: 0,
        call_depth: 0,
        steps: 0,
        allocated: 0,
        query: true,
    }
    .expr(scope, e)
}

/// Evaluate the feature-value expression of `e`.
pub(crate) fn evaluate_feature(model: &mut ResolvedModel, e: ElementRef) -> Result_ {
    Evaluator {
        b: &mut model.b,
        env: Vec::new(),
        in_progress: HashSet::new(),
        overrides: HashMap::new(),
        unbound_receiver: None,
        lib_frames: 0,
        call_depth: 0,
        steps: 0,
        allocated: 0,
        query: false,
    }
    .feature_value(e.0)
}

/// Evaluate the feature chain `root.m1.m2…` off an already-resolved
/// root element: each member is a chain step over the value so far, so
/// every receiver establishes the featuring context and redefinitions
/// shadow inherited values — exactly the textual chain semantics.
pub(crate) fn evaluate_chain_of(
    model: &mut ResolvedModel,
    root: ElementRef,
    members: &[&QualifiedName],
) -> Result_ {
    let mut ev = Evaluator {
        b: &mut model.b,
        env: Vec::new(),
        in_progress: HashSet::new(),
        overrides: HashMap::new(),
        unbound_receiver: None,
        lib_frames: 0,
        call_depth: 0,
        steps: 0,
        allocated: 0,
        query: false,
    };
    let mut v = ev.feature_value(root.0)?;
    for m in members {
        v = ev.chain_into(v, m)?;
    }
    Ok(v)
}

/// Evaluate `member` as a chain step off `receiver` — the semantics of
/// `receiver.member`, so the receiver establishes the featuring context
/// and its redefinitions shadow inherited values. Returns `None` when
/// the chain shape does not apply (the receiver evaluates to a scalar,
/// or cannot reach the member as a chain step) so callers can fall back
/// to plain own-scope evaluation.
pub(crate) fn evaluate_member_of(
    model: &mut ResolvedModel,
    receiver: ElementRef,
    member: &QualifiedName,
) -> Option<Result_> {
    let mut ev = Evaluator {
        b: &mut model.b,
        env: Vec::new(),
        in_progress: HashSet::new(),
        overrides: HashMap::new(),
        unbound_receiver: None,
        lib_frames: 0,
        call_depth: 0,
        steps: 0,
        allocated: 0,
        query: false,
    };
    let target = match ev.feature_value(receiver.0) {
        Ok(
            v @ (Value::Element(_)
            | Value::Unbound(_)
            | Value::UnboundMember(_)
            | Value::Sequence(_)
            | Value::Instance { .. }),
        ) => v,
        _ => return None,
    };
    match ev.chain_into(target, member) {
        Err(EvalError::Unresolved(_)) => None,
        out => Some(out),
    }
}

/// Evaluation budget: an expression that would run or allocate without
/// bound (`1..1000000000`, a calculation doubling a string on every
/// recursion, nested collects over large ranges, a product folding into
/// a million-digit integer) fails with [`EvalError::Budget`] instead of
/// hanging or exhausting memory. Steps count expression nodes; the
/// allocation budget counts the bytes of every sequence or string an
/// operator materializes, so many individually admissible values cannot
/// add up without bound; exact numbers are refused past
/// [`crate::rational::MAX_BITS`]. The limits are far above anything a
/// model's feature values or a document's query tags legitimately need.
pub const MAX_STEPS: usize = 10_000_000;
/// The most elements a range (`a..b`) materializes.
pub const MAX_SEQUENCE: usize = 1_000_000;
/// The longest string (in bytes) an operation produces.
pub const MAX_STRING: usize = 1 << 24;
/// The most bytes of sequences and strings one evaluation materializes
/// through operators, cumulatively.
pub const MAX_ALLOCATION: usize = 256 << 20;
/// The most nested user-calculation calls one evaluation may have open.
/// Recursion is allowed; a recursion that does not terminate exhausts
/// this instead of the stack. Far above any legitimate call chain — a
/// recursive calculation that needs more frames than this is a runaway,
/// not a deep model.
pub const MAX_CALL_DEPTH: usize = 64;

struct Evaluator<'m> {
    b: &'m mut Builder,
    /// Lambda- and calculation-parameter bindings, innermost last.
    env: Vec<(String, Value)>,
    /// (feature, evaluation scope) pairs currently being evaluated
    /// (cycle guard — context-aware, see [`Self::feature_value_in`]).
    in_progress: HashSet<(usize, usize)>,
    /// Feature-value overrides: element → value, consulted before the
    /// recorded feature value. Seeded by satisfaction checks (a
    /// requirement's subject binds to the satisfying feature); empty
    /// everywhere else.
    overrides: HashMap<usize, Value>,
    /// Depth of library-owned calculation bodies on the call stack.
    /// Inside them, unbound features keep the closed [`Value::Element`]
    /// convention (library functions legitimately count and compare
    /// placeholders); at user level they mint [`Value::Unbound`].
    lib_frames: usize,
    /// Receiver whose members are currently evaluated without a bound
    /// instance. Cleared for unrelated references and concrete receivers.
    unbound_receiver: Option<usize>,
    /// User-defined calculation call depth (recursion is allowed, bounded).
    call_depth: usize,
    /// Expression nodes evaluated so far (the step budget, [`MAX_STEPS`]).
    steps: usize,
    /// Bytes of sequences and strings materialized by operators so far
    /// (the allocation budget, [`MAX_ALLOCATION`]).
    allocated: usize,
    /// Ad-hoc query mode ([`evaluate_query_in`]): closed-world element
    /// classification and the reflection intrinsics. Never set for model
    /// feature values — corpus evaluation semantics must not drift.
    query: bool,
}

impl Evaluator<'_> {
    /// The value of feature element `e`: its bound expression if any,
    /// otherwise the element itself (enum literals, unbound features).
    fn feature_value(&mut self, e: usize) -> Result_ {
        self.feature_value_in(e, None)
    }

    /// [`Self::feature_value`] with an optional featuring context: when a
    /// member is reached through a chain step (`car.totalMass`), its
    /// expression's references re-resolve from the *target's* scope, so
    /// redefinitions (`:>> baseMass = 1200`) shadow the inherited values.
    /// The context *persists* through nested simple-name references (see
    /// [`Self::reference`]), so `totalMass → mass → dryMass` keeps
    /// resolving against the instance it was reached through; the cycle
    /// guard keys on (element, context) so a recursive rollup
    /// (`totalMass = mass + sum(subcomponents.totalMass)`) re-enters the
    /// same element under each subcomponent's context legitimately.
    /// The value standing for a feature with no binding: user-owned
    /// features at user level are [`Value::Unbound`] placeholders;
    /// enum literals (variant members), library-owned features, and
    /// anything inside a library evaluation frame keep the closed
    /// [`Value::Element`] convention. Non-feature elements (packages,
    /// definitions referenced as values) are closed element values.
    fn placeholder(&mut self, e: usize) -> Value {
        let ty = self.b.elements[e].ty;
        let feature_like = ty.ends_with("Usage")
            || matches!(
                ty,
                "Feature"
                    | "Step"
                    | "Connector"
                    | "BindingConnector"
                    | "Succession"
                    | "Expression"
                    | "Invariant"
            );
        let variant = self.b.elements[e]
            .owning_relationship
            .is_some_and(|r| self.b.elements[r].ty == "VariantMembership");
        // Library-owned features get placeholders too when evaluation
        // *starts* outside a library frame (standalone evaluation of a
        // parametric library formula) — inside an invocation frame
        // (`lib_frames > 0`) the closed one-element convention that
        // library sequence semantics rely on still applies, except when
        // navigating a receiver already known to be unbound.
        let unknown_member = self.receiver_member(e).is_some();
        if feature_like && !variant && (self.lib_frames == 0 || unknown_member) {
            if unknown_member {
                Value::UnboundMember(ElementRef(e))
            } else {
                Value::Unbound(ElementRef(e))
            }
        } else {
            Value::Element(ElementRef(e))
        }
    }

    fn feature_value_in(&mut self, e: usize, ctx: Option<usize>) -> Result_ {
        // Reading a local/output directly must not bypass the refusal at
        // invocation: its initializer need not be its value after execution.
        let mut owner = self.b.owner_elem(e);
        while let Some(o) = owner {
            if self.b.calculation_requires_execution(o) {
                return Err(EvalError::Unsupported(
                    "calculation body requires statement execution".into(),
                ));
            }
            owner = self.b.owner_elem(o);
        }
        if let Some(v) = self.overrides.get(&e) {
            return Ok(v.clone());
        }
        let (scope, expr, inherited) = match self.b.values.get(&e).cloned() {
            Some((s, x)) => (s, x, false),
            // A redefining feature with no value of its own inherits a
            // `default` value expression from its redefinition target
            // (KerML FeatureValue isDefault: a default applies unless
            // overridden), re-evaluated in the redefining context so
            // redefined sub-features shadow — `attribute :>> mass;` under
            // a pruned structure recomputes the inherited roll-up. A
            // *non-default* inherited value stops the walk: whether it
            // survives redefinition is spec-ambiguous, so those stay
            // unbound (the element itself) as before.
            None => match (self.inherited_default(e), self.b.owner_scope_of(e)) {
                (Some(expr), Some(s)) => (s, expr, true),
                _ => return Ok(self.placeholder(e)),
            },
        };
        if (inherited || self.b.default_values.contains(&e)) && self.receiver_member(e).is_some() {
            return Ok(Value::Indeterminate);
        }
        let scope = ctx.unwrap_or(scope);
        if !self.in_progress.insert((e, scope)) {
            if inherited {
                return Ok(self.placeholder(e));
            }
            let name = self.b.elements[e]
                .props
                .get("declaredName")
                .and_then(|v| v.as_str())
                .unwrap_or("<anonymous>")
                .to_string();
            return Err(EvalError::Cycle(name));
        }
        let out = self.expr(scope, &expr);
        self.in_progress.remove(&(e, scope));
        // The inherited-default path is best-effort: a default written for
        // the general feature may reference names its defining scope
        // imported that the redefining context cannot reach — degrade to
        // the unbound element (the pre-fallback answer) instead of
        // erroring, so downstream member access keeps working.
        if inherited && out.is_err() {
            return Ok(self.placeholder(e));
        }
        out
    }

    /// The nearest `default` value expression on the redefinition-target
    /// closure of `e` (declaration order, breadth-first through valueless
    /// targets). A target carrying a *non-default* value ends the walk —
    /// whether such a binding survives redefinition is spec-ambiguous, so
    /// the caller keeps the feature unbound.
    fn inherited_default(&mut self, e: usize) -> Option<Expr> {
        let mut seen = HashSet::new();
        let mut frontier = vec![e];
        while let Some(cur) = frontier.pop() {
            if !seen.insert(cur) {
                continue;
            }
            for t in self.b.redefinition_target_elems(cur) {
                if let Some((_, expr)) = self.b.values.get(&t) {
                    let expr = expr.clone();
                    return self.b.default_values.contains(&t).then_some(expr);
                }
                frontier.push(t);
            }
        }
        None
    }

    /// The knowable cardinality of an unbound feature, from its declared
    /// multiplicity: `(lower, upper)` bounds, `[1..1]` when none is
    /// written (the KerML default), `None` when the bounds cannot be
    /// evaluated.
    fn unbound_cardinality(&mut self, e: usize) -> Option<(f64, f64)> {
        let Some((scope, m)) = self
            .b
            .multiplicities
            .iter()
            .find(|(o, _, _)| *o == e)
            .map(|(_, s, m)| (*s, m.clone()))
        else {
            return Some((1.0, 1.0));
        };
        let as_num = |v: Value| v.as_f64();
        let hi = as_num(self.expr(scope, &m.upper).ok()?)?;
        let lo = match &m.lower {
            Some(l) => as_num(self.expr(scope, l).ok()?)?,
            None if hi.is_infinite() => 0.0,
            None => hi,
        };
        Some((lo, hi))
    }

    /// The single exit for a freshly materialized value: it charges a
    /// sequence or string against the allocation budget and hands it
    /// back. Every operator that *builds* one passes it through here —
    /// arithmetic and ranges, the control functions, the intrinsics, a
    /// lambda or function reference applied per item, and sequence
    /// construction — so many individually admissible values cannot add
    /// up without bound. Values that merely flow through references
    /// (a feature read, an index, a parameter binding) are not charged
    /// again.
    fn charged(&mut self, value: Value) -> Result_ {
        let bytes = match &value {
            Value::Sequence(items) => items.len().saturating_mul(std::mem::size_of::<Value>()),
            Value::String(s) => s.len(),
            _ => return Ok(value),
        };
        self.allocated = self.allocated.saturating_add(bytes);
        if self.allocated > MAX_ALLOCATION {
            return Err(EvalError::Budget(format!(
                "evaluation materialized more than {MAX_ALLOCATION} bytes of sequences and strings"
            )));
        }
        Ok(value)
    }

    fn expr(&mut self, scope: usize, e: &Expr) -> Result_ {
        self.steps += 1;
        if self.steps > MAX_STEPS {
            return Err(EvalError::Budget(format!(
                "evaluation exceeded {MAX_STEPS} steps"
            )));
        }
        match &e.kind {
            ExprKind::Literal(l) => self.literal(l),
            ExprKind::Null => Ok(Value::null()),
            ExprKind::Ref(qn) => self.reference(scope, qn),
            ExprKind::Conditional {
                cond,
                then_branch,
                else_branch,
            } => match self.tri_boolean(scope, cond)? {
                Some(true) => self.expr(scope, then_branch),
                Some(false) => self.expr(scope, else_branch),
                None => Ok(Value::Indeterminate),
            },
            ExprKind::Binary { op, lhs, rhs } => self.binary(scope, *op, lhs, rhs),
            ExprKind::Unary { op, operand } => {
                let v = self.expr(scope, operand)?;
                if matches!(
                    v,
                    Value::Unbound(_) | Value::UnboundMember(_) | Value::Indeterminate
                ) && !matches!(op, UnaryOp::Tilde)
                {
                    return Ok(Value::Indeterminate);
                }
                match op {
                    UnaryOp::Plus => Ok(v),
                    UnaryOp::Minus => match v {
                        Value::Quantity(n, u) => match n.num() {
                            Some(x) => Ok(Value::Quantity(Box::new(Value::from_num(x.neg())), u)),
                            None => Err(EvalError::Type("unary `-` needs a number".into())),
                        },
                        v => match v.num() {
                            Some(x) => Ok(Value::from_num(x.neg())),
                            None => Err(EvalError::Type("unary `-` needs a number".into())),
                        },
                    },
                    UnaryOp::Not => match v {
                        Value::Boolean(b) => Ok(Value::Boolean(!b)),
                        _ => Err(EvalError::Type("`not` needs a boolean".into())),
                    },
                    UnaryOp::Tilde => Err(EvalError::Unsupported("`~` conjugation".into())),
                }
            }
            ExprKind::ChainStep { target, member } => self.chain_step(scope, target, member),
            ExprKind::Index { target, index } => {
                let tval = self.expr(scope, target)?;
                let i = match self.expr(scope, index)? {
                    Value::Integer(i) => i,
                    Value::Unbound(_) | Value::UnboundMember(_) | Value::Indeterminate => {
                        return Ok(Value::Indeterminate);
                    }
                    _ => return Err(EvalError::Type("index must be an integer".into())),
                };
                // Indexing an *unknown* collection answers from the
                // declared multiplicity, like `size`/`isEmpty` do: an
                // index the bounds admit denotes an unknown item (never a
                // fabricated one — the item placeholder would mis-answer
                // cardinality questions, so it is indeterminate, except a
                // declared singleton whose `x#(1)` *is* `x`); beyond a
                // finite upper bound it is out of bounds like a concrete
                // sequence.
                match &tval {
                    Value::Indeterminate => return Ok(Value::Indeterminate),
                    Value::Unbound(ElementRef(e)) | Value::UnboundMember(ElementRef(e)) => {
                        let bounds = self.unbound_cardinality(*e);
                        let admitted = i >= 1
                            && bounds.is_none_or(|(_, hi)| hi.is_infinite() || i as f64 <= hi);
                        if admitted {
                            return if i == 1 && bounds.is_some_and(|(_, hi)| hi <= 1.0) {
                                Ok(tval)
                            } else {
                                Ok(Value::Indeterminate)
                            };
                        }
                        return Err(EvalError::Type(format!("index {i} out of bounds")));
                    }
                    _ => {}
                }
                let items = tval.items();
                // KerML sequence indexing is 1-based.
                usize::try_from(i)
                    .ok()
                    .filter(|&i| i >= 1 && i <= items.len())
                    .map(|i| items[i - 1].clone())
                    .ok_or_else(|| EvalError::Type(format!("index {i} out of bounds")))
            }
            ExprKind::Bracket { target, arg } => {
                let num = self.expr(scope, target)?;
                if matches!(
                    num,
                    Value::Unbound(_) | Value::UnboundMember(_) | Value::Indeterminate
                ) {
                    return Ok(Value::Indeterminate);
                }
                let unit = self.unit_of(scope, arg)?;
                // A bracket over an already-dimensioned value: the
                // explicit annotation wins. Same dimensions convert
                // across scales (`(1 [m]) [mm]` is `1000 [mm]`);
                // different dimensions take the magnitude as written —
                // the normative precedence binds a trailing unit to the
                // last primary (`mass / rho [kg]` annotates `rho`), so
                // erroring here would poison every value downstream of
                // that common spelling.
                let num = match num {
                    Value::Quantity(n, u) => {
                        if same_dims(&u, &unit) && u.scale != unit.scale {
                            scale_magnitude(*n, &scale_ratio(&u.scale, &unit.scale))?
                        } else {
                            *n
                        }
                    }
                    n => n,
                };
                if unit.dims.is_empty() {
                    // A bracket expression that cancels completely
                    // (`[m/m]`, `[mm/m]`) is dimensionless — any
                    // residual scale folds into the number.
                    return if unit.scale.is_one() {
                        Ok(num)
                    } else {
                        match num.num() {
                            Some(n) => Ok(Value::from_num(n.scale(&unit.scale))),
                            None => Ok(num),
                        }
                    };
                }
                match num {
                    Value::Integer(_) | Value::Rational(_) | Value::Real(_) => {
                        Ok(Value::Quantity(Box::new(num), unit))
                    }
                    // A sequence magnitude is a vector quantity —
                    // `(1670, 720, 80) [frame]`. Numeric components tag
                    // with the measurement reference collectively;
                    // components already carrying their own unit keep it
                    // (`(0, 7.5 [mm], 0) [frame]` — the frame's per-axis
                    // references are not resolvable to one unit); an
                    // unknown component makes the vector indeterminate.
                    Value::Sequence(items) => {
                        for it in &items {
                            match it {
                                Value::Integer(_)
                                | Value::Rational(_)
                                | Value::Real(_)
                                | Value::Quantity(..) => {}
                                Value::Unbound(_)
                                | Value::UnboundMember(_)
                                | Value::Indeterminate => {
                                    return Ok(Value::Indeterminate);
                                }
                                other => {
                                    return Err(EvalError::Type(format!(
                                        "a quantity needs a numeric magnitude, got {other}"
                                    )));
                                }
                            }
                        }
                        Ok(Value::Quantity(Box::new(Value::Sequence(items)), unit))
                    }
                    other => Err(EvalError::Type(format!(
                        "a quantity needs a numeric magnitude, got {other}"
                    ))),
                }
            }
            ExprKind::Arrow { target, ty, args } => self.arrow(scope, target, ty, args),
            ExprKind::Collect { target, body } => self.control_over(scope, target, body, "collect"),
            ExprKind::Select { target, body } => self.control_over(scope, target, body, "select"),
            ExprKind::Invocation { ty, args } => {
                let mut values = Vec::with_capacity(args.len());
                for a in args {
                    let name = a.name.as_ref().map(|n| n.to_display_string());
                    values.push((name, self.expr(scope, &a.value)?));
                }
                // Kernel Function Library names are reserved: intrinsics
                // first (positional only), user-defined calculations after.
                if values.iter().all(|(n, _)| n.is_none()) {
                    let positional: Vec<Value> = values.iter().map(|(_, v)| v.clone()).collect();
                    match self.intrinsic(ty, &positional) {
                        Err(EvalError::Unsupported(_)) => {}
                        out => return out,
                    }
                }
                self.user_calc(scope, ty, values)
            }
            ExprKind::Constructor { ty, args } => self.construct(scope, ty, args),
            ExprKind::Body { members } => self.body_result(scope, members),
            ExprKind::BodyTerminator => self.body_result(scope, &[]),
            ExprKind::Sequence(items) => {
                let mut out = Vec::new();
                for i in items {
                    out.extend(self.expr(scope, i)?.items());
                }
                self.charged(Value::Sequence(out))
            }
            ExprKind::Classification { op, operand, ty } => {
                self.classification(scope, *op, operand.as_deref(), ty)
            }
            ExprKind::Extent { .. } => Err(EvalError::Unsupported("`all` extents".into())),
            ExprKind::MetadataAccess { target } => self.metadata_access(scope, target),
        }
    }

    fn literal(&self, l: &Literal) -> Result_ {
        Ok(match l {
            Literal::Bool(b) => Value::Boolean(*b),
            Literal::String(s) => Value::String(s.clone()),
            // Numbers are exact: an integer beyond `i128` and every
            // decimal spelling become rationals with no intermediate
            // double. Only an exponent too large to materialize degrades
            // to the double parser (infinity).
            Literal::Integer(raw) => match raw.parse::<i128>() {
                Ok(i) => Value::Integer(i),
                Err(_) => Rational::parse_decimal(raw)
                    .map(|r| Value::from_num(Num::Exact(r)))
                    .unwrap_or_else(|| Value::Real(raw.parse().unwrap_or(f64::INFINITY))),
            },
            Literal::Real(raw) => Rational::parse_decimal(raw)
                .map(|r| Value::from_num(Num::Exact(r)))
                .unwrap_or_else(|| Value::Real(raw.parse().unwrap_or(f64::INFINITY))),
            Literal::Infinity => Value::Real(f64::INFINITY),
        })
    }

    /// The value of KerML `that` for `elem` — `Base::things::that`, "the
    /// featuring instance": a feature's `that` is the instance of its
    /// owner (the receiver, under a featuring context); a type's body
    /// reads `that` as the type's own instance.
    fn featuring_instance(&mut self, elem: usize) -> Value {
        if let Some(receiver) = self.unbound_receiver {
            return Value::UnboundMember(ElementRef(receiver));
        }
        let ty = self.b.elements[elem].ty;
        let feature_like = ty.ends_with("Usage")
            || matches!(
                ty,
                "Feature"
                    | "Step"
                    | "Connector"
                    | "BindingConnector"
                    | "Succession"
                    | "Expression"
                    | "BooleanExpression"
                    | "Invariant"
            );
        let anchor = if feature_like {
            self.b.owner_elem(elem).unwrap_or(elem)
        } else {
            elem
        };
        self.placeholder(anchor)
    }

    fn reference(&mut self, scope: usize, qn: &QualifiedName) -> Result_ {
        // Lambda parameters shadow model names.
        if qn.segments.len() == 1 && !qn.is_global {
            let name = &qn.segments[0].value;
            if let Some((_, v)) = self.env.iter().rev().find(|(n, _)| n == name) {
                return Ok(v.clone());
            }
        }
        let Some(mut elem) = self.b.resolve(scope, qn, 0) else {
            // KerML `that` lives on the implied root feature `things`,
            // an implied specialization the resolver does not
            // materialize — a resolved declaration always wins, and only
            // the bare unresolved spelling falls back to the featuring
            // instance of the scope's owner.
            if qn.segments.len() == 1 && !qn.is_global && qn.segments[0].value == "that" {
                if let Some(o) = self.b.nearest_scope_owner(scope) {
                    return Ok(self.featuring_instance(o));
                }
            }
            return Err(EvalError::Unresolved(qn.to_display_string()));
        };
        // A simple name reached the element through the current
        // (featuring) scope — keep evaluating there, so an inherited
        // expression chain (`totalMass → mass → dryMass`) sees the
        // redefinitions of the instance it was reached through. A
        // qualified path names an element elsewhere; its value uses its
        // own scope.
        let previous = self.unbound_receiver;
        let mut member_scope = scope;
        if let Some(receiver) = previous {
            let hit = if qn.segments.len() == 1 && !qn.is_global {
                self.receiver_member(elem)
            } else {
                None
            };
            if let Some(hit) = hit {
                // A method body resolves lexical names from its declaring
                // type. Re-enter the receiver's redefinition context before
                // reading them, just as a direct member chain does.
                elem = hit;
                member_scope = self.b.elem_scope.get(&receiver).copied().unwrap_or(scope);
            } else if !self.receiver_context_contains(elem) {
                self.unbound_receiver = None;
            }
        }
        let value = if qn.segments.len() == 1 && !qn.is_global {
            self.feature_value_in(elem, Some(member_scope))
        } else {
            self.feature_value(elem)
        };
        self.unbound_receiver = previous;
        value
    }

    /// The receiver's version of a lexical member, including a member
    /// reached through an inherited method and redefined by the receiver. Call-local defaults and unrelated lexical declarations
    /// do not become unknown just because their caller has no instance.
    fn receiver_member(&mut self, elem: usize) -> Option<usize> {
        let receiver = self.unbound_receiver?;
        let value = self.b.id_name(elem)?;
        let name = Name {
            value,
            span: Span::default(),
        };
        let sub = self.b.elem_scope.get(&receiver).copied();
        let hit = self.b.resolve_rest(receiver, sub, &[name], 0)?;
        let hit_owner = self.b.owner_elem(hit)?;
        if !self.b.indexed_conforms(receiver, hit_owner) {
            return None;
        }
        if self.b.indexed_conforms(hit, elem) {
            return Some(hit);
        }
        // SysML also permits redefinition by name in a specializing
        // type, without an explicit :>> edge (the resolver's same-name
        // shadowing rule). Unrelated locals with the same name do not
        // satisfy this owner relationship.
        if self.b.elements[hit].ty.ends_with("Usage") {
            let owner = self.b.owner_elem(hit)?;
            let base_owner = self.b.owner_elem(elem)?;
            if owner != base_owner
                && self.b.indexed_conforms(owner, base_owner)
                && !self.b.indexed_conforms(base_owner, owner)
            {
                return Some(hit);
            }
        }
        None
    }

    /// A method-local expression may still read the receiver's fields.
    /// Preserve its lexical context without treating the local itself as
    /// a receiver member; imported declarations have unrelated owners.
    fn receiver_context_contains(&mut self, elem: usize) -> bool {
        let Some(receiver) = self.unbound_receiver else {
            return false;
        };
        let mut owner = self.b.owner_elem(elem);
        while let Some(o) = owner {
            if self.b.indexed_conforms(receiver, o) {
                return true;
            }
            owner = self.b.owner_elem(o);
        }
        false
    }

    /// `new T(args)` — instantiate `T`, binding arguments to its owned
    /// data usages: positionally to the value-less ones in declaration
    /// order, or by name.
    fn construct(&mut self, scope: usize, ty: &TargetRef, args: &[Arg]) -> Result_ {
        let TargetRef::Name(qn) = ty else {
            return Err(EvalError::Unsupported("chained constructor type".into()));
        };
        let ty_name = qn
            .segments
            .last()
            .map(|s| s.value.clone())
            .unwrap_or_default();
        let Some(elem) = self.b.resolve(scope, qn, 0) else {
            return Err(EvalError::Unresolved(qn.to_display_string()));
        };
        let mut values = Vec::with_capacity(args.len());
        for a in args {
            let name = a.name.as_ref().map(|n| n.to_display_string());
            values.push((name, self.expr(scope, &a.value)?));
        }
        let is_data = |b: &Builder, e: usize| {
            // Plain `Feature` covers KerML datatype fields
            // (`Collections::KeyValuePair`'s `key`/`val`).
            matches!(
                b.elements[e].ty,
                "AttributeUsage" | "ReferenceUsage" | "ItemUsage" | "PartUsage" | "Feature"
            )
        };
        let own_fields = |b: &Builder, owner: usize| -> Vec<(String, usize)> {
            b.ctor_fields
                .get(&owner)
                .map(|fs| fs.iter().filter(|(_, e)| is_data(b, *e)).cloned().collect())
                .unwrap_or_default()
        };
        // A type's own fields, then those it *inherits* and does not
        // redeclare (breadth-first over the explicit specialization
        // closure, cycle-guarded). Inherited slots come last so every
        // positional binding a type's own declaration already had keeps
        // its position. Without this a library collection could not be
        // constructed at all: `List`/`Array`/`Set`/`Bag` declare no
        // members of their own — their `elements` is inherited from
        // `Collection` — unlike `Map`/`OrderedSet`, which redeclare it.
        let mut declared: Vec<(String, usize)> = own_fields(self.b, elem);
        let mut seen_types = HashSet::from([elem]);
        let mut queue = std::collections::VecDeque::from([elem]);
        while let Some(t) = queue.pop_front() {
            for base in self.b.explicit_supertype_elems(t) {
                if !seen_types.insert(base) {
                    continue;
                }
                queue.push_back(base);
                for (name, e) in own_fields(self.b, base) {
                    if !declared.iter().any(|(n, _)| *n == name) {
                        declared.push((name, e));
                    }
                }
            }
        }
        // Positional arguments fill the fields that carry no value of
        // their own, in declaration order.
        let mut open = declared
            .iter()
            .filter(|(_, e)| !self.b.values.contains_key(e));
        let mut fields = Vec::with_capacity(values.len());
        let mut bound = HashSet::new();
        for (name, v) in values {
            match name {
                Some(n) => {
                    if !declared.iter().any(|(f, _)| *f == n) {
                        return Err(EvalError::Unresolved(format!("field `{n}` of `{ty_name}`")));
                    }
                    if !bound.insert(n.clone()) {
                        return Err(EvalError::Type(format!(
                            "constructor field `{n}` is bound more than once"
                        )));
                    }
                    fields.push((n, v));
                }
                None => {
                    let Some((f, _)) = open.next() else {
                        return Err(EvalError::Type(format!(
                            "too many constructor arguments for `{ty_name}`"
                        )));
                    };
                    if !bound.insert(f.clone()) {
                        return Err(EvalError::Type(format!(
                            "constructor field `{f}` is bound more than once"
                        )));
                    }
                    fields.push((f.clone(), v));
                }
            }
        }
        Ok(Value::Instance {
            ty: ElementRef(elem),
            ty_name,
            fields,
        })
    }

    /// `target.member` — the member feature of the target element's scope,
    /// or a bound field of a constructed instance.
    fn chain_step(&mut self, scope: usize, target: &Expr, member: &TargetRef) -> Result_ {
        let TargetRef::Name(member) = member else {
            return Err(EvalError::Unsupported("chained chain member".into()));
        };
        let target = self.expr(scope, target)?;
        self.chain_into(target, member)
    }

    /// One chain step over an evaluated target. Per KFL `'.'`, a
    /// multi-valued source maps the member access over its items and the
    /// result feature is *unique* (its `source`/`target` are declared
    /// nonunique, the `chain` result carries KerML's default) — equal
    /// values collapse to one, and a singleton is the value itself
    /// (KerML values are flat sequences). This is why rollups over
    /// possibly-equal values need `collect`, and why
    /// `engines.specificImpulseVacuum` over five identical engines is
    /// one number, not five.
    /// Uncertainty follows the evaluated receiver, including a receiver
    /// returned by an alias, conditional or calculation.
    fn chain_into(&mut self, target: Value, member: &QualifiedName) -> Result_ {
        // An unknown target has nothing to resolve a member against, and
        // the step is as parametric as the target was: strictly
        // propagating (see [`Value::Indeterminate`]) rather than a type
        // error, so `subject.part.attribute` stays one undecided verdict.
        if matches!(target, Value::Indeterminate) {
            return Ok(Value::Indeterminate);
        }
        if let Value::Sequence(items) = target {
            let mut out: Vec<Value> = Vec::new();
            for item in items {
                for v in self.chain_into(item, member)?.items() {
                    if !out.iter().any(|x| value_eq(x, &v)) {
                        out.push(v);
                    }
                }
            }
            return Ok(match out.len() {
                1 => out.pop().unwrap(),
                _ => Value::Sequence(out),
            });
        }
        if let Value::Instance {
            ty_name, fields, ..
        } = &target
        {
            let name = &member.segments.last().unwrap().value;
            return fields
                .iter()
                .find(|(f, _)| f == name)
                .map(|(_, v)| v.clone())
                .ok_or_else(|| {
                    EvalError::Type(format!("field `{name}` of `{ty_name}` is not bound"))
                });
        }
        let unbound = match &target {
            Value::UnboundMember(_) => true,
            Value::Unbound(e) => self.b.is_reference_feature(e.0),
            _ => false,
        };
        let (Value::Element(ElementRef(elem))
        | Value::Unbound(ElementRef(elem))
        | Value::UnboundMember(ElementRef(elem))) = target
        else {
            return Err(EvalError::Type(
                "chain target must be a model element".into(),
            ));
        };
        let sub = self.b.elem_scope.get(&elem).copied();
        let Some(hit) = self.b.resolve_rest(elem, sub, &member.segments, 0) else {
            // `x.that` — the featuring instance of `x` (see `reference`
            // for why the bare spelling only falls back on resolution
            // failure).
            if member.segments.len() == 1 && member.segments[0].value == "that" {
                return Ok(self.featuring_instance(elem));
            }
            return Err(EvalError::Unresolved(member.to_display_string()));
        };
        // A member with no bound value may be a *collection the receiver
        // populates*: features of the receiver that specialize it —
        // explicitly, or through their usage kind's implied subsettings
        // (SysML 8.4.2 Table 32), which the model deliberately does not
        // materialize as relationships. `p.performedActions` collects
        // p's perform usages, each standing for its referenced action.
        if !unbound && !self.b.values.contains_key(&hit) {
            // A named slot answers with its owned parts before the general
            // collection rule, which would otherwise collect the slot
            // itself (it specializes the member it redefines).
            if let Some(v) = self.slot_projection(elem, hit)? {
                return Ok(v);
            }
            if let Some(items) = self.collection_items(elem, hit)? {
                return Ok(match items.len() {
                    1 => items.into_iter().next().unwrap(),
                    _ => Value::Sequence(items),
                });
            }
            if let Some(v) = self.dom_projection(elem, hit)? {
                return Ok(v);
            }
        }
        // Evaluate fixed formulas in the unknown receiver's context too:
        // `eligible = willing` fixes the formula, not a default on willing.
        // A concrete receiver establishes a fresh, known context.
        let previous = self.unbound_receiver;
        self.unbound_receiver = unbound.then_some(elem);
        let value = self.feature_value_in(hit, sub);
        self.unbound_receiver = previous;
        value
    }

    /// A named slot's value: when the receiver owns a part that only
    /// redefines `hit` (`part <n> :>> body { … }`, `:>> props { … }`),
    /// that member's value is the slot's owned parts in membership order
    /// — ownership is the sufficient representation. `None` when the
    /// receiver owns no such slot.
    fn slot_projection(&mut self, receiver: usize, hit: usize) -> Result<Option<Value>, EvalError> {
        let owned = self.b.owned_member_elems(receiver, true);
        let mut slot = None;
        for m in owned {
            if self.b.elements[m].ty != "PartUsage" || !self.is_dom_slot(m) {
                continue;
            }
            // Only the *redefined* member projects; the slot addressed by
            // its own short name stays the slot (a fragment node).
            if self.b.redefinition_target_elems(m).contains(&hit) {
                slot = Some(m);
                break;
            }
        }
        let Some(slot) = slot else {
            return Ok(None);
        };
        let mut items = Vec::new();
        for m in self.b.owned_member_elems(slot, true) {
            if self.b.elements[m].ty == "PartUsage" {
                items.extend(self.feature_value_in(m, None)?.items());
            }
        }
        Ok(Some(match items.len() {
            1 => items.into_iter().next().unwrap(),
            _ => Value::Sequence(items),
        }))
    }

    /// The Web platform library's constructed navigation: an imported
    /// document stores only structural
    /// ownership, so a derived DOM member reached on a node usage —
    /// `childNodes`, `children`, `firstChild`, `lastChild`, `parentNode`,
    /// `parentElement`, the sibling views, `childElementCount`,
    /// `attributes` — is projected from the receiver's owned parts in
    /// membership order: tree nodes are the owned parts that do not
    /// conform to `Attr`; attributes are the ones that do. Applies only
    /// to members declared by `Web::DOM`, so user features of the same
    /// names are untouched. `None` for any other member.
    fn dom_projection(&mut self, receiver: usize, hit: usize) -> Result<Option<Value>, EvalError> {
        const NAV: &[&str] = &[
            "childNodes",
            "children",
            "firstChild",
            "lastChild",
            "parentNode",
            "parentElement",
            "previousSibling",
            "nextSibling",
            "firstElementChild",
            "lastElementChild",
            "previousElementSibling",
            "nextElementSibling",
            "childElementCount",
            "attributes",
        ];
        // A redefining member (`:>> attributes : AttributeLike[0..*]`)
        // carries its name through the redefinition, not a declaration.
        let Some(name) = self.b.id_name(hit) else {
            return Ok(None);
        };
        if !NAV.contains(&name.as_str()) {
            return Ok(None);
        }
        let scope = self.b.elem_scope.get(&receiver).copied().unwrap_or(0);
        let attr_def = self
            .b
            .resolve(scope, &crate::json::lib_qn("Web::DOM::Attr"), 0);
        let element_def = self
            .b
            .resolve(scope, &crate::json::lib_qn("Web::DOM::Element"), 0);
        let node_def = self
            .b
            .resolve(scope, &crate::json::lib_qn("Web::DOM::Node"), 0);
        let (Some(attr_def), Some(element_def), Some(node_def)) = (attr_def, element_def, node_def)
        else {
            return Ok(None);
        };
        // The member is a DOM view when it (or a feature it redefines) is
        // declared inside `Web::DOM`, or when its owning definition is a
        // node kind (a template element's redefined `attributes`).
        let owner_is_node = self
            .b
            .owner_elem(hit)
            .is_some_and(|o| self.b.conforms_upward(o, node_def));
        if !owner_is_node && !self.redefines_web_dom_member(hit) {
            return Ok(None);
        }
        let is_part = |b: &Builder, e: usize| b.elements[e].ty == "PartUsage";
        // The receiver's owned parts split into tree nodes and attributes.
        // A slot — a part with no typing of its own that redefines a
        // collection (`part <n> :>> body { … }`, `:>> props { … }`) — is
        // transparent: its owned parts are projected in its place.
        let (nodes, attrs) = self.dom_owned(receiver, attr_def, node_def);
        let mut elements = Vec::new();
        for &m in &nodes {
            if self.b.conforms_upward(m, element_def) {
                elements.push(m);
            }
        }
        // The receiver among its owner's tree nodes, for the parent and
        // sibling views (a package-level node has no DOM parent, and an
        // attribute is never a child of the element owning it).
        let parent = if self.b.conforms_upward(receiver, attr_def) {
            None
        } else {
            // Through transparent slots up to the nearest typed node.
            let mut cur = self.b.owner_elem(receiver);
            while let Some(o) = cur {
                if !is_part(self.b, o) {
                    cur = None;
                    break;
                }
                if !self.is_dom_slot(o) {
                    break;
                }
                cur = self.b.owner_elem(o);
            }
            cur.filter(|&o| self.b.conforms_upward(o, node_def))
        };
        let siblings: Vec<usize> = match parent {
            Some(p) => self.dom_owned(p, attr_def, node_def).0,
            None => Vec::new(),
        };
        let at = siblings.iter().position(|&m| m == receiver);
        let before = |v: &[usize], i: Option<usize>| i.and_then(|i| v[..i].last().copied());
        let after = |v: &[usize], i: Option<usize>| i.and_then(|i| v.get(i + 1).copied());
        let element_siblings: Vec<usize> = {
            let mut out = Vec::new();
            for &m in &siblings {
                if self.b.conforms_upward(m, element_def) {
                    out.push(m);
                }
            }
            out
        };
        let at_el = element_siblings.iter().position(|&m| m == receiver);
        let picked: Vec<usize> = match name.as_str() {
            "childNodes" => nodes,
            "children" => elements,
            "firstChild" => nodes.first().copied().into_iter().collect(),
            "lastChild" => nodes.last().copied().into_iter().collect(),
            "firstElementChild" => elements.first().copied().into_iter().collect(),
            "lastElementChild" => elements.last().copied().into_iter().collect(),
            "parentNode" => parent.into_iter().collect(),
            "parentElement" => parent
                .filter(|&p| self.b.conforms_upward(p, element_def))
                .into_iter()
                .collect(),
            "previousSibling" => before(&siblings, at).into_iter().collect(),
            "nextSibling" => after(&siblings, at).into_iter().collect(),
            "previousElementSibling" => before(&element_siblings, at_el).into_iter().collect(),
            "nextElementSibling" => after(&element_siblings, at_el).into_iter().collect(),
            "childElementCount" => return Ok(Some(Value::Integer(elements.len() as i128))),
            "attributes" => attrs,
            _ => return Ok(None),
        };
        let mut items = Vec::with_capacity(picked.len());
        for m in picked {
            items.extend(self.feature_value_in(m, None)?.items());
        }
        Ok(Some(match items.len() {
            1 => items.into_iter().next().unwrap(),
            _ => Value::Sequence(items),
        }))
    }

    /// The receiver's owned tree nodes and attributes in membership
    /// order, transparent slots flattened.
    fn dom_owned(
        &mut self,
        receiver: usize,
        attr_def: usize,
        node_def: usize,
    ) -> (Vec<usize>, Vec<usize>) {
        let mut nodes = Vec::new();
        let mut attrs = Vec::new();
        let mut stack: Vec<Vec<usize>> = vec![self.b.owned_member_elems(receiver, true)];
        // Depth-first in order: a slot's members replace the slot.
        let mut queue: Vec<usize> = Vec::new();
        while let Some(batch) = stack.pop() {
            queue.extend(batch);
        }
        let mut i = 0;
        while i < queue.len() {
            let m = queue[i];
            i += 1;
            if self.b.elements[m].ty != "PartUsage" {
                continue;
            }
            if self.is_dom_slot(m) {
                let inner = self.b.owned_member_elems(m, true);
                queue.splice(i..i, inner);
                continue;
            }
            if self.b.conforms_upward(m, attr_def) {
                attrs.push(m);
            } else if self.b.conforms_upward(m, node_def) {
                nodes.push(m);
            }
        }
        (nodes, attrs)
    }

    /// A part usage that only redefines (no typing of its own): a named
    /// slot of a template block or component.
    fn is_dom_slot(&mut self, e: usize) -> bool {
        let specs = self.b.explicit_specialization_elems(e);
        !specs.is_empty() && specs.iter().all(|(kind, _)| *kind == "Redefinition")
    }

    /// Does `e`, or a feature it (transitively) redefines, live inside
    /// `Web::DOM`?
    fn redefines_web_dom_member(&mut self, e: usize) -> bool {
        let mut seen = HashSet::new();
        let mut stack = vec![e];
        while let Some(x) = stack.pop() {
            if !seen.insert(x) {
                continue;
            }
            if self.declared_in_web_dom(x) {
                return true;
            }
            stack.extend(self.b.redefinition_target_elems(x));
        }
        false
    }

    /// Is `e` a member declared inside package `Web::DOM` (by owner
    /// chain: some owner named `DOM` whose owner is named `Web`)?
    fn declared_in_web_dom(&self, e: usize) -> bool {
        let mut cur = self.b.owner_elem(e);
        while let Some(o) = cur {
            let owner = self.b.owner_elem(o);
            if self.b.effective_name(o).as_deref() == Some("DOM")
                && owner.is_some_and(|w| self.b.effective_name(w).as_deref() == Some("Web"))
            {
                return true;
            }
            cur = owner;
        }
        false
    }

    /// The values of the receiver's owned features that specialize
    /// `hit`, in declaration order — `None` when none does (an ordinary
    /// member access, not a collection). Implied subsettings resolve by
    /// library name, so a model loaded without the standard library
    /// degrades to the explicit-edge answer. A reference usage stands
    /// for its referenced feature (`perform t1` collects as `t1` — the
    /// declared closure then classifies it, and members resolve against
    /// the redefinitions the referenced feature carries).
    fn collection_items(
        &mut self,
        receiver: usize,
        hit: usize,
    ) -> Result<Option<Vec<Value>>, EvalError> {
        let scope = self.b.elem_scope.get(&receiver).copied().unwrap_or(0);
        let mut items = Vec::new();
        let mut any = false;
        for m in self.b.owned_member_elems(receiver, true) {
            if m == hit {
                continue;
            }
            let mut is_member = self.b.conforms_upward(m, hit);
            if !is_member {
                let metaclass = self.b.elements[m].ty;
                let mut names: Vec<&'static str> =
                    match crate::lift::usage_kind_of(metaclass, Dialect::Sysml) {
                        Some(kind) => crate::json::implicit_usage_bases(kind).to_vec(),
                        None => Vec::new(),
                    };
                names.extend(implied_collection_extras(metaclass));
                is_member = names.iter().any(|n| {
                    self.b
                        .resolve(scope, &crate::json::lib_qn(n), 0)
                        .is_some_and(|c| c == hit || self.b.conforms_upward(c, hit))
                });
            }
            if !is_member {
                continue;
            }
            any = true;
            let target = self.reference_target(m).unwrap_or(m);
            items.extend(self.feature_value_in(target, None)?.items());
        }
        Ok(if any { Some(items) } else { None })
    }

    /// The resolved target of `m`'s own `ReferenceSubsetting`, if any —
    /// read back from the relationship's id-valued property (implied
    /// relationships are never materialized, so this is the only edge).
    fn reference_target(&mut self, m: usize) -> Option<usize> {
        let rels: Vec<usize> = self.b.elements[m]
            .owned_relationships
            .iter()
            .copied()
            .filter(|&r| self.b.elements[r].ty == "ReferenceSubsetting")
            .collect();
        for r in rels {
            let id = self.b.elements[r]
                .props
                .get("referencedFeature")
                .and_then(|v| v.as_reference());
            if let Some(t) = id.and_then(|id| self.b.element_index_of_uuid(id)) {
                return Some(t);
            }
        }
        None
    }

    /// Canonicalize a quantity-bracket unit expression: unit references
    /// resolve to elements and expand through pure power-product
    /// definitions and `unitConversion` declarations (so `kg`, `SI::kg`,
    /// and any spelling of one dimension get one exponent map, and `min`
    /// or `km` carry their factor to the reference as `scale`); `* / **`
    /// combine exponents and scales. The display keeps the source
    /// spelling (`km/h`).
    fn unit_of(&mut self, scope: usize, e: &Expr) -> Result<Unit, EvalError> {
        let (dims, scale, display) = self.unit_dims(scope, e)?;
        Ok(Unit {
            dims: normalize_dims(dims),
            scale,
            display,
        })
    }

    fn unit_dims(
        &mut self,
        scope: usize,
        e: &Expr,
    ) -> Result<(Vec<Dim>, Rational, String), EvalError> {
        match &e.kind {
            ExprKind::Ref(qn) => {
                let elem = self
                    .b
                    .resolve(scope, qn, 0)
                    .ok_or_else(|| EvalError::Unresolved(qn.to_display_string()))?;
                let name = qn
                    .segments
                    .last()
                    .map(|s| s.value.clone())
                    .unwrap_or_default();
                let (dims, scale) = self.expanded_unit(scope, elem, name.clone(), 0);
                Ok((dims, scale, name))
            }
            ExprKind::Binary { op, lhs, rhs } => {
                let (ld, ls, ldisp) = self.unit_dims(scope, lhs)?;
                match op {
                    BinaryOp::Mul => {
                        let (rd, rs, rdisp) = self.unit_dims(scope, rhs)?;
                        Ok((
                            dims_combine(&ld, &rd, 1),
                            ls.mul(&rs),
                            format!("{ldisp}*{rdisp}"),
                        ))
                    }
                    BinaryOp::Div => {
                        let (rd, rs, rdisp) = self.unit_dims(scope, rhs)?;
                        Ok((
                            dims_combine(&ld, &rd, -1),
                            scale_ratio(&ls, &rs),
                            format!("{ldisp}/{rdisp}"),
                        ))
                    }
                    BinaryOp::Pow | BinaryOp::Caret => match unit_exponent(rhs) {
                        Some(k) => Ok((
                            dims_pow(&ld, (k, 1)),
                            ls.pow_or_approx(k),
                            format!("{ldisp}**{k}"),
                        )),
                        None => Err(EvalError::Unsupported(
                            "a unit exponent that is not an integer literal".into(),
                        )),
                    },
                    _ => Err(EvalError::Unsupported(
                        "quantity-unit expressions beyond `*`, `/`, `**`".into(),
                    )),
                }
            }
            _ => Err(EvalError::Unsupported(
                "quantity-unit expressions beyond `*`, `/`, `**`".into(),
            )),
        }
    }

    /// A named unit's dimension vector and scale. In priority order: a
    /// library-declared `unitConversion` with an evaluable numeric
    /// factor and reference unit normalizes to the reference dimensions
    /// scaled by the factor (`min` → `{s}`×60; prefixes work through the
    /// inherited `conversionFactor = prefix.conversionFactor` chain); a
    /// value expression that is a pure power product of other units
    /// expands recursively (`N = kg*m/s^2`, `J = N*m`); a *spelled*
    /// power product without either (`'m³⋅s⁻²' : SimpleUnit;`) expands
    /// by parsing its own name, when enabled (the default — see
    /// [`set_unit_spelling_expansion`]); anything else — base units, a
    /// literal factor, an expansion that cancels completely (`rad =
    /// m/m` stays a named unit, not a number) — is an opaque base with
    /// scale 1. `scope` is the use site, the resolution fallback for
    /// spelled components when the element has no declaring scope.
    fn expanded_unit(
        &mut self,
        scope: usize,
        elem: usize,
        name: String,
        depth: u32,
    ) -> (Vec<Dim>, Rational) {
        // Recursive/bound evaluations can have context-dependent cutoffs.
        // Cache only complete unbound top-level reductions, and include the
        // spelling switch and fallback scope in the key.
        let cacheable = self.b.semantic_ready
            && depth == 0
            && self.env.is_empty()
            && self.overrides.is_empty()
            && self.in_progress.is_empty()
            && !self.query
            && self.call_depth == 0;
        if !cacheable {
            return self.expanded_unit_uncached(scope, elem, name, depth);
        }
        let key = (
            self.b.owner_scope_of(elem).unwrap_or(scope),
            elem,
            name.clone(),
            unit_spelling_expansion(),
        );
        if let Some(hit) = self.b.semantic_memo.units.get(&key).cloned() {
            self.b.used_imports.extend(hit.imports);
            return hit.value;
        }
        let imports = std::mem::take(&mut self.b.used_imports);
        let value = self.expanded_unit_uncached(scope, elem, name, depth);
        self.b.semantic_memo.units.insert(
            key,
            crate::semantic_memo::Proven {
                value: value.clone(),
                imports: self.b.used_imports.iter().copied().collect(),
            },
        );
        self.b.used_imports.extend(imports);
        value
    }
    fn expanded_unit_uncached(
        &mut self,
        scope: usize,
        elem: usize,
        name: String,
        depth: u32,
    ) -> (Vec<Dim>, Rational) {
        if depth < 8 {
            if let Some(out) = self.conversion_dims(elem, depth) {
                return out;
            }
            if let Some((scope, expr)) = self.b.values.get(&elem).cloned() {
                if let Some((dims, scale)) = self.power_product_dims(scope, &expr, depth) {
                    let dims = normalize_dims(dims);
                    if !dims.is_empty() {
                        return (dims, scale);
                    }
                }
            }
            if unit_spelling_expansion() {
                if let Some((dims, scale)) = self.spelled_product_dims(scope, elem, &name, depth) {
                    let dims = normalize_dims(dims);
                    if !dims.is_empty() {
                        return (dims, scale);
                    }
                }
            }
        }
        (
            vec![Dim {
                elem,
                name,
                num: 1,
                den: 1,
            }],
            Rational::one(),
        )
    }

    /// Expansion of a unit whose *name* spells a power product
    /// (`'m³⋅s⁻²'`): every spelled factor must resolve to a unit — in
    /// the spelled unit's declaring scope when it has one, else at the
    /// use site — and expands recursively, so prefixes and derived
    /// names inside the spelling (`'km⋅h⁻¹'`) carry their scales.
    /// `None` (stay opaque) when the name is not a spelled product or
    /// any factor fails to resolve.
    fn spelled_product_dims(
        &mut self,
        scope: usize,
        elem: usize,
        name: &str,
        depth: u32,
    ) -> Option<(Vec<Dim>, Rational)> {
        let factors = parse_unit_spelling(name)?;
        let scope = self.b.owner_scope_of(elem).unwrap_or(scope);
        let mut dims: Vec<Dim> = Vec::new();
        let mut scale = Rational::one();
        for (sym, exp) in factors {
            let qn = QualifiedName {
                is_global: false,
                segments: vec![Name {
                    value: sym.clone(),
                    span: Span::default(),
                }],
                span: Span::default(),
            };
            let c = self.b.resolve(scope, &qn, 0)?;
            if c == elem {
                return None;
            }
            let (cd, cs) = self.expanded_unit(scope, c, sym, depth + 1);
            dims = dims_combine(&dims, &dims_pow(&cd, (exp, 1)), 1);
            scale = scale.mul(&cs.pow_or_approx(exp));
        }
        Some((dims, scale))
    }

    /// The `unitConversion` declaration of a unit element, if it carries
    /// one that this evaluator can use: both members must be *bound* —
    /// `referenceUnit` to a unit element and `conversionFactor` to a
    /// finite positive number (the abstract inherited members on every
    /// `MeasurementUnit` are valueless and fall out here).
    fn conversion_dims(&mut self, elem: usize, depth: u32) -> Option<(Vec<Dim>, Rational)> {
        let seg = |s: &str| {
            vec![Name {
                value: s.to_string(),
                span: Span::default(),
            }]
        };
        let sub = self.b.elem_scope.get(&elem).copied();
        let conv = self.b.resolve_rest(elem, sub, &seg("unitConversion"), 0)?;
        let conv_scope = self.b.elem_scope.get(&conv).copied();
        // A member of the conversion, evaluated in its featuring context;
        // `None` when it is unbound (the abstract `UnitConversion`
        // members every `MeasurementUnit` inherits are valueless).
        let member = |b: &mut Self, owner: usize, scope: Option<usize>, name: &str| {
            let hit = b.b.resolve_rest(owner, scope, &seg(name), 0)?;
            match b.feature_value_in(hit, scope) {
                Ok(
                    Value::Element(ElementRef(e))
                    | Value::Unbound(ElementRef(e))
                    | Value::UnboundMember(ElementRef(e)),
                ) if e == hit => None,
                Ok(v) => Some(v),
                Err(_) => None,
            }
        };
        let ref_unit = match member(self, conv, conv_scope, "referenceUnit")? {
            Value::Element(ElementRef(e))
            | Value::Unbound(ElementRef(e))
            | Value::UnboundMember(ElementRef(e)) => e,
            _ => return None,
        };
        // `ConversionByConvention` binds `conversionFactor` directly;
        // `ConversionByPrefix` derives it as `prefix.conversionFactor`
        // (MeasurementReferences.sysml) — follow that derivation
        // explicitly when the direct member is unbound.
        let factor = match member(self, conv, conv_scope, "conversionFactor").and_then(|v| v.num())
        {
            Some(f) => f,
            None => {
                let prefix = match member(self, conv, conv_scope, "prefix")? {
                    Value::Element(ElementRef(e))
                    | Value::Unbound(ElementRef(e))
                    | Value::UnboundMember(ElementRef(e)) => e,
                    _ => return None,
                };
                let p_scope = self.b.elem_scope.get(&prefix).copied();
                member(self, prefix, p_scope, "conversionFactor")?.num()?
            }
        };
        // An approximate factor (an irrational user conversion) enters
        // the scale as the exact value of its double.
        let factor = factor.exact()?;
        if !factor.is_positive() {
            return None;
        }
        let ref_name = self.b.elements[ref_unit]
            .props
            .get("declaredShortName")
            .or_else(|| self.b.elements[ref_unit].props.get("declaredName"))
            .and_then(|v| v.as_str())
            .unwrap_or("unit")
            .to_string();
        // The reference unit resolves its own spelled components from
        // its declaring scope; the conversion's scope is only the
        // fallback.
        let ref_scope = conv_scope.unwrap_or(0);
        let (dims, ref_scale) = self.expanded_unit(ref_scope, ref_unit, ref_name, depth + 1);
        Some((dims, factor.mul(&ref_scale)))
    }

    /// `unit_dims`, but for a candidate derived-unit *definition*: any
    /// non-power-product construct means "not a derived unit" (`None`)
    /// rather than an error.
    fn power_product_dims(
        &mut self,
        scope: usize,
        e: &Expr,
        depth: u32,
    ) -> Option<(Vec<Dim>, Rational)> {
        match &e.kind {
            ExprKind::Ref(qn) => {
                let elem = self.b.resolve(scope, qn, 0)?;
                let name = qn.segments.last().map(|s| s.value.clone())?;
                Some(self.expanded_unit(scope, elem, name, depth + 1))
            }
            ExprKind::Binary { op, lhs, rhs } => {
                let (ld, ls) = self.power_product_dims(scope, lhs, depth)?;
                match op {
                    BinaryOp::Mul => {
                        let (rd, rs) = self.power_product_dims(scope, rhs, depth)?;
                        Some((dims_combine(&ld, &rd, 1), ls.mul(&rs)))
                    }
                    BinaryOp::Div => {
                        let (rd, rs) = self.power_product_dims(scope, rhs, depth)?;
                        Some((dims_combine(&ld, &rd, -1), scale_ratio(&ls, &rs)))
                    }
                    BinaryOp::Pow | BinaryOp::Caret => {
                        let k = unit_exponent(rhs)?;
                        Some((dims_pow(&ld, (k, 1)), ls.pow_or_approx(k)))
                    }
                    _ => None,
                }
            }
            _ => None,
        }
    }

    /// `x istype T` / `x hastype T` / `x as T` — classification per KFL
    /// `BaseFunctions`: `istype` tests that every value of the operand
    /// conforms to `T` (reaches it through the explicit specialization
    /// closure), `hastype` tests direct typing, `as` filters the
    /// sequence to the conforming values. Number/Boolean/String literals
    /// classify by the `ScalarValues` hierarchy by simple name. The walk
    /// covers *explicit* edges only; implied library bases are not
    /// recorded, so a non-hit against a library-owned type is undecided
    /// (error), never a false `false` — a non-hit against a user-defined
    /// type is decidedly `false` (user types are only reachable through
    /// explicit edges).
    fn classification(
        &mut self,
        scope: usize,
        op: ClassificationOp,
        operand: Option<&Expr>,
        ty: &TargetRef,
    ) -> Result_ {
        let Some(operand) = operand else {
            return Err(EvalError::Unsupported(
                "classification of the implicit subject".into(),
            ));
        };
        let TargetRef::Name(qn) = ty else {
            return Err(EvalError::Unsupported("chained classification type".into()));
        };
        let target = self
            .b
            .resolve(scope, qn, 0)
            .ok_or_else(|| EvalError::Unresolved(qn.to_display_string()))?;
        let items = self.expr(scope, operand)?.items();
        match op {
            ClassificationOp::As => {
                // Three-valued: a decided non-member drops, an *undecided*
                // membership keeps the value — the cast asserts a type, it
                // does not test one, and dropping on unknown would
                // fabricate a definite "not a member".
                let mut out = Vec::new();
                for v in items {
                    if self.value_conforms(&v, target, false)? != Some(false) {
                        out.push(v);
                    }
                }
                Ok(Value::Sequence(out))
            }
            ClassificationOp::IsType | ClassificationOp::HasType => {
                // Three-valued: a decided miss is false regardless of
                // unknowns elsewhere; all-hits is true; otherwise the
                // test is indeterminate, never a fabricated boolean.
                let direct = matches!(op, ClassificationOp::HasType);
                let mut unknown = false;
                for v in &items {
                    match self.value_conforms(v, target, direct)? {
                        Some(false) => return Ok(Value::Boolean(false)),
                        Some(true) => {}
                        None => unknown = true,
                    }
                }
                Ok(if unknown {
                    Value::Indeterminate
                } else {
                    Value::Boolean(true)
                })
            }
            // `x @ M` — every operand element is annotated by metadata
            // conforming to `M`, or (when `M` is a reflection metaclass)
            // is itself an instance of `M`. Annotations are static model
            // facts, so a miss is a definite `false` (the import-filter
            // discipline).
            ClassificationOp::AtType => {
                for v in &items {
                    let (Value::Element(ElementRef(e))
                    | Value::Unbound(ElementRef(e))
                    | Value::UnboundMember(ElementRef(e))) = v
                    else {
                        return Err(EvalError::Type(
                            "the metadata test `@` applies to model elements".into(),
                        ));
                    };
                    match self.b.metadata_conforms(target, *e) {
                        Tri::True => {}
                        Tri::False => return Ok(Value::Boolean(false)),
                        Tri::Unknown => {
                            return Err(EvalError::Unsupported(
                                "metadata test against this target (the verdict \
                                 is undecided)"
                                    .into(),
                            ));
                        }
                    }
                }
                Ok(Value::Boolean(true))
            }
            // `x meta M` filters the metaobjects of `x` to those
            // conforming to metaclass `M`; `x @@ M` tests that every
            // metaobject conforms. A plain element operand stands for
            // its metadata access (`X meta M` ≡ `X.metadata meta M`,
            // the official grammar's only spelling).
            ClassificationOp::Meta | ClassificationOp::MetaAtType => {
                let mut metas = Vec::new();
                for v in items {
                    match v {
                        Value::Instance { .. } => metas.push(v),
                        Value::Element(ElementRef(e))
                        | Value::Unbound(ElementRef(e))
                        | Value::UnboundMember(ElementRef(e)) => {
                            if matches!(self.b.elements[e].ty, "MetadataUsage" | "MetadataFeature")
                            {
                                // An annotation already *is* a metaobject.
                                metas.push(v);
                            } else {
                                metas.extend(self.metaobjects_of(e)?.items());
                            }
                        }
                        _ => {
                            return Err(EvalError::Type(
                                "metadata classification applies to metaobjects".into(),
                            ));
                        }
                    }
                }
                if matches!(op, ClassificationOp::Meta) {
                    let mut out = Vec::new();
                    for v in metas {
                        if self.metaobject_conforms(&v, target)? {
                            out.push(v);
                        }
                    }
                    Ok(Value::Sequence(out))
                } else {
                    for v in &metas {
                        if !self.metaobject_conforms(v, target)? {
                            return Ok(Value::Boolean(false));
                        }
                    }
                    Ok(Value::Boolean(true))
                }
            }
        }
    }

    /// `X.metadata` — KerML metadata access: the metaobjects of the
    /// referenced element. Lambda parameters shadow model names, as in
    /// plain references.
    fn metadata_access(&mut self, scope: usize, target: &QualifiedName) -> Result_ {
        if target.segments.len() == 1 && !target.is_global {
            let name = &target.segments[0].value;
            if let Some((_, v)) = self.env.iter().rev().find(|(n, _)| n == name) {
                let (Value::Element(ElementRef(e))
                | Value::Unbound(ElementRef(e))
                | Value::UnboundMember(ElementRef(e))) = v.clone()
                else {
                    return Err(EvalError::Type(
                        "`.metadata` applies to model elements".into(),
                    ));
                };
                return self.metaobjects_of(e);
            }
        }
        let elem = self
            .b
            .resolve(scope, target, 0)
            .ok_or_else(|| EvalError::Unresolved(target.to_display_string()))?;
        self.metaobjects_of(elem)
    }

    /// The metaobject sequence of an element: one item per metadata
    /// annotation (in declaration order — the annotation element stands
    /// for the metaobject, so chain steps read its bound attribute
    /// values), plus an instance of the element's own reflective
    /// metaclass carrying the element's scalar abstract-syntax
    /// properties as bound fields.
    fn metaobjects_of(&mut self, elem: usize) -> Result_ {
        let mut out: Vec<Value> = self
            .b
            .metadata_of
            .get(&elem)
            .cloned()
            .unwrap_or_default()
            .into_iter()
            .map(|m| Value::Element(ElementRef(m)))
            .collect();
        out.push(self.reflective_metaobject(elem)?);
        Ok(Value::Sequence(out))
    }

    /// The reflective-metaclass instance of an element: an instance of
    /// the standard reflection library's metaclass named like the
    /// element's own metaclass (`SysML::PartDefinition`, KerML fallback),
    /// with the element's serialized scalar properties as bound fields.
    fn reflective_metaobject(&mut self, elem: usize) -> Result_ {
        let ty_name = self.b.elements[elem].ty;
        let mc = self.b.reflection_metaclass(ty_name).ok_or_else(|| {
            EvalError::Unsupported(format!(
                "reflective metaclass `{ty_name}` (the standard library is \
                 not loaded)"
            ))
        })?;
        let props = self.b.elements[elem].props.to_json();
        let mut fields = Vec::new();
        for (k, v) in props {
            let value = match v {
                serde_json::Value::String(s) => Value::String(s),
                serde_json::Value::Bool(b) => Value::Boolean(b),
                serde_json::Value::Number(n) => match n.as_i64() {
                    Some(i) => Value::Integer(i as i128),
                    // A JSON number's decimal spelling is the value
                    // meant; read it exactly rather than through a double.
                    None => match Rational::parse_decimal(&n.to_string()) {
                        Some(r) => Value::from_num(Num::Exact(r)),
                        None => Value::Real(n.as_f64().unwrap_or(f64::NAN)),
                    },
                },
                _ => continue,
            };
            fields.push((k, value));
        }
        Ok(Value::Instance {
            ty: ElementRef(mc),
            ty_name: ty_name.to_string(),
            fields,
        })
    }

    /// Does one metaobject conform to the target metaclass? Annotation
    /// metaobjects classify by the annotation's own (static) typing;
    /// reflective instances by their metaclass element. Hits through the
    /// explicit closure are definite; a miss is a definite `false`
    /// against a reflection metaclass (the reflection hierarchy is
    /// explicit) or a user-defined type, and undecided against any other
    /// library type (conformance may ride on implied bases this walk
    /// cannot see).
    fn metaobject_conforms(&mut self, v: &Value, target: usize) -> Result<bool, EvalError> {
        let classifier = match v {
            Value::Instance { ty, .. } => ty.0,
            Value::Element(ElementRef(e))
            | Value::Unbound(ElementRef(e))
            | Value::UnboundMember(ElementRef(e)) => *e,
            _ => {
                return Err(EvalError::Type(
                    "metadata classification applies to metaobjects".into(),
                ));
            }
        };
        if self.conforms_upward(classifier, target) {
            return Ok(true);
        }
        if self.b.is_reflection_target(target) || target >= self.b.lib_boundary {
            return Ok(false);
        }
        Err(EvalError::Unsupported(
            "metaobject classification against a library type (implied bases \
             are not walked)"
                .into(),
        ))
    }

    /// Does one value conform to (`direct = false`) or carry as its
    /// direct type (`direct = true`) the target element? Open-world
    /// discipline: a model feature's *instance* may be more specific
    /// than its declaration, so for [`Value::Element`] a conformance hit
    /// through the declared closure is a definite `true`, but a miss —
    /// and any `hastype` — is undecided (error), never a false `false`.
    /// Closed values (constructed instances, scalar literals) answer
    /// both ways; a miss against a library-owned type stays undecided
    /// (conformance may ride on implied bases this walk cannot see).
    fn value_conforms(
        &mut self,
        v: &Value,
        target: usize,
        direct: bool,
    ) -> Result<Option<bool>, EvalError> {
        let target_name = self.b.elements[target]
            .props
            .get("declaredName")
            .and_then(|p| p.as_str())
            .unwrap_or("")
            .to_string();
        let scalar = |chain: &[&str]| {
            let hit = if direct {
                chain.first() == Some(&target_name.as_str())
            } else {
                chain.contains(&target_name.as_str())
                    || matches!(target_name.as_str(), "DataValue" | "Anything")
            };
            Ok(Some(hit))
        };
        match v {
            Value::Indeterminate => Ok(None),
            Value::Integer(_) => scalar(&[
                "Integer",
                "Rational",
                "Real",
                "Complex",
                "Number",
                "ScalarValue",
            ]),
            Value::Rational(r) if r.is_integer() => scalar(&[
                "Integer",
                "Rational",
                "Real",
                "Complex",
                "Number",
                "ScalarValue",
            ]),
            Value::Rational(_) => scalar(&["Rational", "Real", "Complex", "Number", "ScalarValue"]),
            Value::Real(_) => scalar(&["Real", "Complex", "Number", "ScalarValue"]),
            Value::Boolean(_) => scalar(&["Boolean", "ScalarValue"]),
            Value::String(_) => scalar(&["String", "ScalarValue"]),
            Value::Element(ElementRef(e))
            | Value::Unbound(ElementRef(e))
            | Value::UnboundMember(ElementRef(e)) => {
                if !direct && self.conforms_upward(*e, target) {
                    return Ok(Some(true));
                }
                // In query mode the operand *is* the declaration, not a
                // possibly-more-specific instance: a miss against a
                // user-defined type is decidedly `false` (user types are
                // only reachable through explicit edges). A library type
                // may still be reached through implied bases this walk
                // cannot see, so that miss stays undecided.
                if self.query && !direct {
                    return if target < self.b.lib_boundary {
                        Err(EvalError::Unsupported(
                            "classification against a library type (implied \
                             bases are not walked)"
                                .into(),
                        ))
                    } else {
                        Ok(Some(false))
                    };
                }
                // The instance may be more specific than its declaration
                // — undecided, never a false `false`.
                Ok(None)
            }
            Value::Instance { ty, .. } => {
                if direct {
                    Ok(Some(ty.0 == target))
                } else if self.conforms_upward(ty.0, target) {
                    Ok(Some(true))
                } else if target < self.b.lib_boundary {
                    // Conformance to a library type may ride implied
                    // bases this walk cannot see.
                    Ok(None)
                } else {
                    Ok(Some(false))
                }
            }
            Value::Quantity(..) | Value::Sequence(_) => Err(EvalError::Unsupported(
                "classification of quantities".into(),
            )),
        }
    }

    /// Is `target` reachable from `e` through the explicit
    /// typing/specialization closure, or a semantic-metadata implied
    /// specialization (an annotated element specializes the metadata's
    /// `baseType` value)?
    fn conforms_upward(&mut self, e: usize, target: usize) -> bool {
        self.b.conforms_upward_semantic(e, target)
    }

    /// Is the invocation target calculation-like: a function/calc-family
    /// element itself, or a feature *typed* by one (a function-typed
    /// parameter — `in calculation : Interpolate` — invoked in a body)?
    fn callee_is_calculation(&mut self, elem: usize) -> bool {
        let calcish = |ty: &str| {
            ty.contains("Calculation")
                || ty.contains("Constraint")
                || ty.contains("Expression")
                || ty == "Function"
                || ty == "Predicate"
        };
        if calcish(self.b.elements[elem].ty) {
            return true;
        }
        self.b
            .direct_typing_elems(elem)
            .into_iter()
            .any(|t| calcish(self.b.elements[t].ty))
    }

    /// Effective input parameters of a calculation element. Calculation
    /// usages commonly declare no parameters of their own and inherit the
    /// signature from their typed calculation definition (`getOutput:
    /// GetOutput`), so bodiless-call validation must walk explicit supertypes
    /// instead of treating the usage as a zero-argument function.
    fn callee_params(&mut self, elem: usize) -> Vec<String> {
        let mut stack = vec![elem];
        let mut seen = HashSet::new();
        while let Some(e) = stack.pop() {
            if !seen.insert(e) {
                continue;
            }
            if let Some(params) = self.b.in_params.get(&e) {
                if !params.is_empty() {
                    return params.clone();
                }
            }
            stack.extend(self.b.explicit_supertype_elems(e));
        }
        Vec::new()
    }

    /// Invoke a user-defined calculation (any element whose body carries a
    /// trailing result expression): bind its `in`/`inout` parameters to the
    /// arguments — positionally, or by name for named arguments — and
    /// evaluate the result expression in the calculation's own scope.
    fn user_calc(
        &mut self,
        scope: usize,
        ty: &TargetRef,
        args: Vec<(Option<String>, Value)>,
    ) -> Result_ {
        // A chained callee (`pkg.calcs.f(…)`) resolves through the chain
        // machinery like any chain member; a plain name resolves in scope.
        let (display, elem) = match ty {
            TargetRef::Name(qn) => {
                let display = qn.to_display_string();
                if qn.segments.len() == 1 && !qn.is_global {
                    let name = &qn.segments[0].value;
                    let bound = self
                        .env
                        .iter()
                        .rev()
                        .find(|(n, _)| n == name)
                        .map(|(_, v)| v.clone());
                    if let Some(value) = bound {
                        return match value {
                            Value::Element(ElementRef(elem))
                            | Value::Unbound(ElementRef(elem))
                            | Value::UnboundMember(ElementRef(elem)) => {
                                self.user_calc_elem(&display, elem, args)
                            }
                            Value::Indeterminate => Ok(Value::Indeterminate),
                            other => Err(EvalError::Type(format!(
                                "function `{display}` is bound to non-callable value {other}"
                            ))),
                        };
                    }
                }
                let Some(elem) = self.b.resolve(scope, qn, 0) else {
                    return Err(EvalError::Unsupported(format!("function `{display}`")));
                };
                (display, elem)
            }
            TargetRef::Chain(links) => {
                let display = links
                    .iter()
                    .map(|l| l.to_display_string())
                    .collect::<Vec<_>>()
                    .join(".");
                let empty = QualifiedName {
                    is_global: false,
                    segments: Vec::new(),
                    span: Span::default(),
                };
                let Some(elem) = self.b.resolve_chain_member(scope, Some(links), &empty) else {
                    return Err(EvalError::Unsupported(format!("function `{display}`")));
                };
                (display, elem)
            }
        };
        self.user_calc_elem(&display, elem, args)
    }

    /// Invoke an already-resolved calculation element. Kept separate from
    /// [`Self::user_calc`] so a function-typed parameter can dispatch to the
    /// concrete element bound in the current calculation frame.
    fn user_calc_elem(
        &mut self,
        display: &str,
        elem: usize,
        args: Vec<(Option<String>, Value)>,
    ) -> Result_ {
        let previous = self.unbound_receiver;
        let elem = match self.receiver_member(elem) {
            Some(hit) => hit,
            None => {
                self.unbound_receiver = None;
                elem
            }
        };
        let value = self.user_calc_body(display, elem, args);
        self.unbound_receiver = previous;
        value
    }

    fn user_calc_body(
        &mut self,
        display: &str,
        elem: usize,
        args: Vec<(Option<String>, Value)>,
    ) -> Result_ {
        if self.b.calculation_requires_execution(elem) {
            return Err(EvalError::Unsupported(
                "calculation body requires statement execution".into(),
            ));
        }
        let has_body = self.b.result_exprs.iter().any(|(o, _, _)| *o == elem)
            || self
                .b
                .return_params
                .get(&elem)
                .is_some_and(|ret| self.b.values.contains_key(ret));
        if !has_body && !self.callee_is_calculation(elem) {
            return Err(EvalError::Unsupported(format!(
                "function `{display}` (no result expression)"
            )));
        }
        // Validate and bind arguments before the abstract/bodiless fallback:
        // an unknown result does not make an invalid invocation well-formed.
        let params = self.callee_params(elem);
        // Parameters belong to this invocation. A missing argument/default
        // must never capture a same-named parameter from the calling frame.
        let caller_env = self.env.clone();
        self.env.retain(|(name, _)| !params.contains(name));
        let mut positional = 0usize;
        let mut bound = HashSet::new();
        for (name, v) in args {
            match name {
                Some(n) => {
                    if !params.contains(&n) {
                        self.env = caller_env;
                        return Err(EvalError::Unresolved(format!(
                            "parameter `{n}` of `{display}`"
                        )));
                    }
                    if !bound.insert(n.clone()) {
                        self.env = caller_env;
                        return Err(EvalError::Type(format!(
                            "parameter `{n}` of `{display}` is bound more than once"
                        )));
                    }
                    self.env.push((n, v));
                }
                None => {
                    let Some(p) = params.get(positional) else {
                        self.env = caller_env;
                        return Err(EvalError::Type(format!(
                            "too many arguments to `{display}`"
                        )));
                    };
                    if !bound.insert(p.clone()) {
                        self.env = caller_env;
                        return Err(EvalError::Type(format!(
                            "parameter `{p}` of `{display}` is bound more than once"
                        )));
                    }
                    self.env.push((p.clone(), v));
                    positional += 1;
                }
            }
        }
        if has_body {
            for name in &params {
                if bound.contains(name) {
                    continue;
                }
                let mut stack = vec![elem];
                let mut seen = HashSet::new();
                let mut parameter = None;
                while let Some(owner) = stack.pop() {
                    if !seen.insert(owner) {
                        continue;
                    }
                    if let Some((_, field)) = self
                        .b
                        .ctor_fields
                        .get(&owner)
                        .and_then(|fields| fields.iter().find(|(n, _)| n == name))
                    {
                        parameter = Some(*field);
                        break;
                    }
                    stack.extend(self.b.explicit_supertype_elems(owner));
                }
                let Some(parameter) = parameter.filter(|p| self.b.values.contains_key(p)) else {
                    self.env = caller_env;
                    return Err(EvalError::Unresolved(format!(
                        "unbound parameter `{name}` of `{display}`"
                    )));
                };
                let value = match self.feature_value(parameter) {
                    Ok(value) => value,
                    Err(error) => {
                        self.env = caller_env;
                        return Err(error);
                    }
                };
                self.env.push((name.clone(), value));
            }
        }
        // A calculation's result is its trailing result expression, or —
        // the `return x = expr;` spelling — its return parameter's value.
        enum CalcBody {
            Result(usize, Expr),
            Return(usize),
        }
        let result = self
            .b
            .result_exprs
            .iter()
            .find(|(o, _, _)| *o == elem)
            .map(|(_, s, e)| (*s, e.clone()));
        let body = match result {
            Some((s, e)) => CalcBody::Result(s, e),
            None => match self.b.return_params.get(&elem) {
                Some(&ret) if self.b.values.contains_key(&ret) => CalcBody::Return(ret),
                _ => {
                    // A *calculation* with no body — abstract, a
                    // declaration shell, or a function-typed parameter
                    // whose actual is unknown — applied to arguments has
                    // an unknown result: indeterminate, not unsupported.
                    // Non-callable targets keep the error (degrading
                    // those would mask a genuine model defect).
                    if self.callee_is_calculation(elem) {
                        self.env = caller_env;
                        return Ok(Value::Indeterminate);
                    }
                    self.env = caller_env;
                    return Err(EvalError::Unsupported(format!(
                        "function `{display}` (no result expression)"
                    )));
                }
            },
        };
        // Call depth is a budget, not a cycle: a recursion that does not
        // terminate reaches it, and so does a legitimately deep chain of
        // distinct calculations.
        if self.call_depth >= MAX_CALL_DEPTH {
            self.env = caller_env;
            return Err(EvalError::Budget(format!(
                "evaluation nested more than {MAX_CALL_DEPTH} calculation calls, at `{display}`"
            )));
        }
        self.call_depth += 1;
        // A library-owned callee evaluates in a library frame: its body
        // keeps the closed element convention for unbound features (see
        // `placeholder` — library sequence semantics count on it).
        let lib_callee = elem < self.b.lib_boundary;
        if lib_callee {
            self.lib_frames += 1;
        }
        let out = match body {
            CalcBody::Result(cscope, result) => self.expr(cscope, &result),
            CalcBody::Return(ret) => self.feature_value(ret),
        };
        if lib_callee {
            self.lib_frames -= 1;
        }
        self.call_depth -= 1;
        self.env = caller_env;
        out
    }

    /// Equality for `==`/`!=`: element values compare by identity only when
    /// both are enum/variant literals; anything else involving a model
    /// element is a comparison with an *unbound feature* — unknown, so it
    /// errors (surfacing as an undecided verdict) rather than yielding a
    /// false `false`.
    fn strict_eq(&self, a: &Value, b: &Value) -> Result<bool, EvalError> {
        let enumish = |e: &ElementRef| {
            let el = &self.b.elements[e.0];
            el.ty == "EnumerationUsage"
                || el
                    .owning_relationship
                    .map(|r| self.b.elements[r].ty == "VariantMembership")
                    .unwrap_or(false)
        };
        match (a, b) {
            (Value::Unbound(_) | Value::UnboundMember(_), _)
            | (_, Value::Unbound(_) | Value::UnboundMember(_)) => {
                Err(EvalError::Type("comparison with an unbound feature".into()))
            }
            (Value::Element(x), Value::Element(y)) => {
                if enumish(x) && enumish(y) {
                    Ok(x == y)
                } else {
                    Err(EvalError::Type("comparison with an unbound feature".into()))
                }
            }
            (Value::Element(_), _) | (_, Value::Element(_)) => {
                Err(EvalError::Type("comparison with an unbound feature".into()))
            }
            (Value::Quantity(x, u), Value::Quantity(y, v)) => {
                if u == v {
                    Ok(value_eq(x, y))
                } else if same_dims(u, v) {
                    match (x.num(), y.num()) {
                        (Some(a), Some(b)) => Ok(a.scale(&u.scale).eq(&b.scale(&v.scale))),
                        _ => Err(EvalError::Type("numeric operands required".into())),
                    }
                } else {
                    Err(EvalError::Type(
                        "comparison of quantities in different units".into(),
                    ))
                }
            }
            (Value::Quantity(..), _) | (_, Value::Quantity(..)) => Err(EvalError::Type(
                "comparison of a quantity with a plain value".into(),
            )),
            // Constructed data values compare structurally.
            (Value::Instance { .. }, Value::Instance { .. }) => Ok(value_eq(a, b)),
            (Value::Instance { .. }, _) | (_, Value::Instance { .. }) => Err(EvalError::Type(
                "comparison of a constructed value with a plain value".into(),
            )),
            _ => Ok(value_eq(a, b)),
        }
    }

    /// Three-valued boolean: `Some(b)` for a decided value, `None` when
    /// the operand is *unknown* (an unbound feature or an indeterminate
    /// result) — anything else is still a type error.
    fn tri_boolean(&mut self, scope: usize, e: &Expr) -> Result<Option<bool>, EvalError> {
        match self.expr(scope, e)? {
            Value::Boolean(b) => Ok(Some(b)),
            Value::Unbound(_) | Value::UnboundMember(_) | Value::Indeterminate => Ok(None),
            other => Err(EvalError::Type(format!("expected a boolean, got {other}"))),
        }
    }

    fn binary(&mut self, scope: usize, op: BinaryOp, lhs: &Expr, rhs: &Expr) -> Result_ {
        use BinaryOp::*;
        // Short-circuit forms first. A decided left side still decides
        // (`false and …` never evaluates the right side); an *unknown*
        // side makes the whole form indeterminate — same evaluation
        // order as before, with the type error replaced by the unknown.
        match op {
            CondAnd => {
                return Ok(match self.tri_boolean(scope, lhs)? {
                    Some(false) => Value::Boolean(false),
                    Some(true) => match self.tri_boolean(scope, rhs)? {
                        Some(b) => Value::Boolean(b),
                        None => Value::Indeterminate,
                    },
                    None => match self.tri_boolean(scope, rhs)? {
                        Some(false) => Value::Boolean(false),
                        Some(true) | None => Value::Indeterminate,
                    },
                });
            }
            CondOr => {
                return Ok(match self.tri_boolean(scope, lhs)? {
                    Some(true) => Value::Boolean(true),
                    Some(false) => match self.tri_boolean(scope, rhs)? {
                        Some(b) => Value::Boolean(b),
                        None => Value::Indeterminate,
                    },
                    None => match self.tri_boolean(scope, rhs)? {
                        Some(true) => Value::Boolean(true),
                        Some(false) | None => Value::Indeterminate,
                    },
                });
            }
            Implies => {
                return Ok(match self.tri_boolean(scope, lhs)? {
                    Some(false) => Value::Boolean(true),
                    Some(true) => match self.tri_boolean(scope, rhs)? {
                        Some(b) => Value::Boolean(b),
                        None => Value::Indeterminate,
                    },
                    None => match self.tri_boolean(scope, rhs)? {
                        Some(true) => Value::Boolean(true),
                        Some(false) | None => Value::Indeterminate,
                    },
                });
            }
            NullCoalescing => {
                let l = self.expr(scope, lhs)?;
                return if l.is_null() {
                    self.expr(scope, rhs)
                } else {
                    Ok(l)
                };
            }
            _ => {}
        }
        let l = self.expr(scope, lhs)?;
        let r = self.expr(scope, rhs)?;
        // An unknown operand makes the result unknown rather than a type
        // error — a parametric formula over an unbound feature degrades
        // to an indeterminate value. Closed `Element` values still
        // type-error below (an enum literal is not a number).
        if matches!(
            l,
            Value::Unbound(_) | Value::UnboundMember(_) | Value::Indeterminate
        ) || matches!(
            r,
            Value::Unbound(_) | Value::UnboundMember(_) | Value::Indeterminate
        ) {
            return Ok(Value::Indeterminate);
        }
        let value = match op {
            AndAmp | Xor | OrBar => match (l, r) {
                (Value::Boolean(a), Value::Boolean(b)) => Ok(Value::Boolean(match op {
                    AndAmp => a && b,
                    OrBar => a || b,
                    _ => a ^ b,
                })),
                _ => Err(EvalError::Type("boolean operands required".into())),
            },
            Eq | Same => Ok(Value::Boolean(self.strict_eq(&l, &r)?)),
            NotEq | NotSame => Ok(Value::Boolean(!self.strict_eq(&l, &r)?)),
            Lt | LtEq | Gt | GtEq => {
                let ord = compare(&l, &r)?;
                Ok(Value::Boolean(match op {
                    Lt => ord.is_lt(),
                    LtEq => ord.is_le(),
                    Gt => ord.is_gt(),
                    _ => ord.is_ge(),
                }))
            }
            Range => match (l, r) {
                (Value::Integer(a), Value::Integer(b)) => {
                    // Checked: the bounds may span the whole `i128` range.
                    let count = if b < a {
                        Some(0)
                    } else {
                        b.checked_sub(a).and_then(|n| n.checked_add(1))
                    };
                    match count {
                        Some(n) if n <= MAX_SEQUENCE as i128 => {
                            Ok(Value::Sequence((a..=b).map(Value::Integer).collect()))
                        }
                        _ => Err(EvalError::Budget(format!(
                            "range `{a}..{b}` has more than {MAX_SEQUENCE} elements"
                        ))),
                    }
                }
                _ => Err(EvalError::Type("`..` needs integer bounds".into())),
            },
            Add | Sub | Mul | Div | Rem | Pow | Caret => arith(op, l, r),
            _ => unreachable!("short-circuit ops handled above"),
        }?;
        self.charged(value)
    }

    /// `target->Fn (args)` / `->Fn {body}` — invocation with the target as
    /// the first argument (the emitter's arrow ≡ invocation equivalence).
    fn arrow(&mut self, scope: usize, target: &Expr, ty: &TargetRef, args: &ArrowArgs) -> Result_ {
        let first = self.expr(scope, target)?;
        match args {
            ArrowArgs::Body(body) => {
                let TargetRef::Name(qn) = ty else {
                    return Err(EvalError::Unsupported("chained function reference".into()));
                };
                let name = qn.segments.last().unwrap().value.clone();
                self.control(scope, &name, first, &Applier::Lambda(body))
            }
            ArrowArgs::List(list) => {
                let mut values = vec![(None, first)];
                for a in list {
                    let name = a.name.as_ref().map(|n| n.to_display_string());
                    values.push((name, self.expr(scope, &a.value)?));
                }
                if values.iter().all(|(n, _)| n.is_none()) {
                    let positional: Vec<Value> = values.iter().map(|(_, v)| v.clone()).collect();
                    match self.intrinsic(ty, &positional) {
                        Err(EvalError::Unsupported(_)) => {}
                        out => return out,
                    }
                }
                self.user_calc(scope, ty, values)
            }
            // `->reduce '+'` and friends: the referenced function applies
            // where a lambda body would.
            ArrowArgs::FunctionRef(fnqn) => {
                let TargetRef::Name(qn) = ty else {
                    return Err(EvalError::Unsupported("chained function reference".into()));
                };
                let name = qn.segments.last().unwrap().value.clone();
                self.control(scope, &name, first, &Applier::FnRef(fnqn))
            }
        }
    }

    fn control_over(&mut self, scope: usize, target: &Expr, body: &Expr, name: &str) -> Result_ {
        let first = self.expr(scope, target)?;
        self.control(scope, name, first, &Applier::Lambda(body))
    }

    /// Control functions with a lambda body over a sequence.
    /// Apply a control function's per-item computation: a `{ … }` lambda
    /// body, or a referenced function (`->reduce '+'`). A per-item result
    /// is a materialized value like any other — a fold over a thousand
    /// items builds a thousand of them — so it leaves through
    /// [`Self::charged`].
    fn apply(&mut self, scope: usize, applier: &Applier<'_>, args: &[Value]) -> Result_ {
        let value = match applier {
            Applier::Lambda(body) => self.apply_lambda(scope, body, args)?,
            Applier::FnRef(qn) => self.apply_fn_ref(scope, qn, args.to_vec())?,
        };
        self.charged(value)
    }

    /// Apply a *referenced* function to arguments: operator spellings
    /// (`'+'`, `'*'`, …) fold through the arithmetic core, KFL intrinsics
    /// dispatch by reserved name (`min`, `max`), anything else invokes as
    /// a user calculation — where a bodiless callee degrades to
    /// indeterminate like any other invocation.
    fn apply_fn_ref(&mut self, scope: usize, qn: &QualifiedName, args: Vec<Value>) -> Result_ {
        if let [l, r] = args.as_slice() {
            let op = match qn.segments.last().unwrap().value.as_str() {
                "+" => Some(BinaryOp::Add),
                "-" => Some(BinaryOp::Sub),
                "*" => Some(BinaryOp::Mul),
                "/" => Some(BinaryOp::Div),
                "%" => Some(BinaryOp::Rem),
                "**" => Some(BinaryOp::Pow),
                "^" => Some(BinaryOp::Caret),
                _ => None,
            };
            if let Some(op) = op {
                return arith(op, l.clone(), r.clone());
            }
        }
        match self.intrinsic(&TargetRef::Name(qn.clone()), &args) {
            Err(EvalError::Unsupported(_)) => {}
            out => return out,
        }
        let named: Vec<(Option<String>, Value)> = args.into_iter().map(|v| (None, v)).collect();
        self.user_calc(scope, &TargetRef::Name(qn.clone()), named)
    }

    /// A control function's own result — the collected, selected or
    /// folded value — through the allocation budget.
    fn control(
        &mut self,
        scope: usize,
        name: &str,
        target: Value,
        applier: &Applier<'_>,
    ) -> Result_ {
        let value = self.control_uncharged(scope, name, target, applier)?;
        self.charged(value)
    }

    fn control_uncharged(
        &mut self,
        scope: usize,
        name: &str,
        target: Value,
        applier: &Applier<'_>,
    ) -> Result_ {
        let items = target.items();
        match name {
            "collect" | "select" | "reject" | "forAll" | "exists" => {
                // Three-valued over unknown body results: a decided item
                // still decides (`forAll` fails on a false, `exists`
                // succeeds on a true), but an *unknown* item must never
                // be read as false — the quantification (or the selected
                // membership) is indeterminate instead.
                let mut out = Vec::new();
                let mut unknown = false;
                for item in &items {
                    let v = self.apply(scope, applier, std::slice::from_ref(item))?;
                    match name {
                        "collect" => out.extend(v.items()),
                        "select" | "reject" => match v {
                            Value::Boolean(keep) => {
                                if keep == (name == "select") {
                                    out.push(item.clone());
                                }
                            }
                            Value::Unbound(_) | Value::UnboundMember(_) | Value::Indeterminate => {
                                unknown = true
                            }
                            _ => {
                                return Err(EvalError::Type(format!(
                                    "{name} body must yield a boolean"
                                )));
                            }
                        },
                        "forAll" => match v {
                            Value::Unbound(_) | Value::UnboundMember(_) | Value::Indeterminate => {
                                unknown = true
                            }
                            v if v != Value::Boolean(true) => {
                                return Ok(Value::Boolean(false));
                            }
                            _ => {}
                        },
                        "exists" => match v {
                            Value::Boolean(true) => return Ok(Value::Boolean(true)),
                            Value::Unbound(_) | Value::UnboundMember(_) | Value::Indeterminate => {
                                unknown = true
                            }
                            _ => {}
                        },
                        _ => unreachable!(),
                    }
                }
                Ok(match name {
                    _ if unknown => Value::Indeterminate,
                    "forAll" => Value::Boolean(true),
                    "exists" => Value::Boolean(false),
                    _ => Value::Sequence(out),
                })
            }
            // ControlFunctions::selectOne = `collection->select {…}#(1)`.
            "selectOne" => {
                for item in &items {
                    match self.apply(scope, applier, std::slice::from_ref(item))? {
                        Value::Boolean(true) => return Ok(item.clone()),
                        Value::Boolean(false) => {}
                        // An unknown predicate makes *which* item is
                        // selected unknown.
                        Value::Unbound(_) | Value::UnboundMember(_) | Value::Indeterminate => {
                            return Ok(Value::Indeterminate);
                        }
                        _ => {
                            return Err(EvalError::Type(
                                "selectOne body must yield a boolean".into(),
                            ));
                        }
                    }
                }
                Ok(Value::null())
            }
            // ControlFunctions::minimize/maximize = the extremum of the
            // *mapped* values (`collection->collect {…}->reduce min/max`).
            "minimize" | "maximize" => {
                let mut mapped = Vec::with_capacity(items.len());
                for item in &items {
                    mapped.extend(
                        self.apply(scope, applier, std::slice::from_ref(item))?
                            .items(),
                    );
                }
                extremum(mapped, name == "maximize")
            }
            "reduce" => {
                let mut it = items.into_iter();
                let Some(mut acc) = it.next() else {
                    return Ok(Value::null());
                };
                for item in it {
                    acc = self.apply(scope, applier, &[acc, item])?;
                }
                Ok(acc)
            }
            other => Err(EvalError::Unsupported(format!(
                "control function `{other}` with a body"
            ))),
        }
    }

    /// Bind a `{ in p1; in p2; result-expr }` lambda's parameters to `args`
    /// and evaluate its result expression.
    fn apply_lambda(&mut self, scope: usize, body: &Expr, args: &[Value]) -> Result_ {
        let ExprKind::Body { members } = &body.kind else {
            // A non-body lambda argument evaluates as a plain expression.
            return self.expr(scope, body);
        };
        Self::check_expression_body(members)?;
        let mut params = Vec::new();
        let mut result = None;
        for m in members {
            match &m.kind {
                MemberKind::Usage(u)
                    if matches!(
                        u.prefix.direction,
                        Some(FeatureDirection::In | FeatureDirection::InOut)
                    ) =>
                {
                    if let Some(n) = &u.declaration.id.name {
                        params.push(n.value.clone());
                    }
                }
                MemberKind::Result(e) => result = Some(e),
                _ => {}
            }
        }
        let result =
            result.ok_or_else(|| EvalError::Unsupported("lambda body without a result".into()))?;
        if params.len() != args.len() {
            return Err(EvalError::Type(format!(
                "lambda expects {} argument(s), got {}",
                params.len(),
                args.len()
            )));
        }
        let depth = self.env.len();
        for (p, v) in params.iter().zip(args) {
            self.env.push((p.clone(), v.clone()));
        }
        let out = self.expr(scope, result);
        self.env.truncate(depth);
        out
    }

    /// Evaluate a `{ …; result-expr }` body expression directly.
    fn body_result(&mut self, scope: usize, members: &[Member]) -> Result_ {
        Self::check_expression_body(members)?;
        for m in members {
            if let MemberKind::Result(e) = &m.kind {
                return self.expr(scope, e);
            }
        }
        Err(EvalError::Unsupported(
            "body expression without a result".into(),
        ))
    }

    fn check_expression_body(members: &[Member]) -> Result<(), EvalError> {
        if members.iter().any(crate::json::member_requires_execution) {
            return Err(EvalError::Unsupported(
                "calculation body requires statement execution".into(),
            ));
        }
        if members
            .iter()
            .any(|m| matches!(&m.kind, MemberKind::Usage(u) if u.prefix.direction.is_none()))
        {
            return Err(EvalError::Unsupported(
                "expression-body local declarations require scoped evaluation".into(),
            ));
        }
        Ok(())
    }

    /// The elements owned by `e` through its owned memberships, as
    /// [`Value::Element`]s — see [`Builder::owned_member_elems`].
    fn owned_members(&self, e: usize, features_only: bool) -> Vec<Value> {
        self.b
            .owned_member_elems(e, features_only)
            .into_iter()
            .map(|i| Value::Element(ElementRef(i)))
            .collect()
    }

    /// One reflection answer over element `e` (empty sequence when the
    /// element has no such name).
    fn reflect_element(&self, what: &str, e: usize) -> Value {
        let props = &self.b.elements[e].props;
        let name = |k: &str| props.get(k).and_then(|v| v.as_str()).map(str::to_string);
        let some = |s: Option<String>| {
            s.map(Value::String)
                .unwrap_or_else(|| Value::Sequence(Vec::new()))
        };
        match what {
            "declaredName" => some(name("declaredName")),
            "shortName" => some(name("declaredShortName")),
            "metaclass" => Value::String(self.b.elements[e].ty.to_string()),
            "qualifiedName" => {
                let mut segs = Vec::new();
                let mut cur = Some(e);
                while let Some(x) = cur {
                    match self.b.id_name(x) {
                        Some(n) => segs.push(sysmlv2_syntax::ast::escape_name(&n)),
                        None => break,
                    }
                    cur = self.b.owner_elem(x);
                }
                if segs.is_empty() {
                    return Value::Sequence(Vec::new());
                }
                segs.reverse();
                Value::String(segs.join("::"))
            }
            "docs" => {
                let bodies: Vec<Value> = self
                    .b
                    .owned_member_elems(e, false)
                    .into_iter()
                    .filter(|&m| self.b.elements[m].ty == "Documentation")
                    .filter_map(|m| {
                        self.b.elements[m]
                            .props
                            .get("body")
                            .and_then(|v| v.as_str())
                            .map(str::to_string)
                    })
                    .map(|b| Value::String(crate::json::doc_display_text(&b)))
                    .collect();
                match bodies.len() {
                    1 => bodies.into_iter().next().unwrap(),
                    _ => Value::Sequence(bodies),
                }
            }
            _ => Value::Sequence(Vec::new()),
        }
    }

    /// Kernel Function Library intrinsics, matched by the invoked name's
    /// last segment. An intrinsic that builds a sequence or a string
    /// (`reverse`, `including`, `ToString`, `Substring`, …) returns it
    /// through the allocation budget; an
    /// [`EvalError::Unsupported`] answer is the "not an intrinsic"
    /// sentinel invocation dispatch falls through on, and stays exactly
    /// that.
    fn intrinsic(&mut self, ty: &TargetRef, args: &[Value]) -> Result_ {
        let value = self.intrinsic_uncharged(ty, args)?;
        self.charged(value)
    }

    fn intrinsic_uncharged(&mut self, ty: &TargetRef, args: &[Value]) -> Result_ {
        let TargetRef::Name(qn) = ty else {
            return Err(EvalError::Unsupported("chained function reference".into()));
        };
        let name = qn.segments.last().unwrap().value.as_str();
        let items = |v: &Value| v.clone().items();
        match (name, args) {
            // Reflection over the model structure (query mode only —
            // `sysmlv2 query` / `ResolvedModel::query` — so these names
            // can never shadow a user calculation in a model file): the
            // KerML derived properties `Namespace::ownedMember` /
            // `Type::ownedFeature` as functions over a model element.
            (
                "ownedMember",
                [
                    Value::Element(ElementRef(e))
                    | Value::Unbound(ElementRef(e))
                    | Value::UnboundMember(ElementRef(e)),
                ],
            ) if self.query => Ok(Value::Sequence(self.owned_members(*e, false))),
            (
                "ownedFeature",
                [
                    Value::Element(ElementRef(e))
                    | Value::Unbound(ElementRef(e))
                    | Value::UnboundMember(ElementRef(e)),
                ],
            ) if self.query => Ok(Value::Sequence(self.owned_members(*e, true))),
            // Element reflection (query mode): names, metaclass and
            // documentation of a model element, as the rendering backend's
            // translated template expressions ask for them.
            (
                "declaredName" | "shortName" | "qualifiedName" | "metaclass" | "docs",
                [
                    Value::Element(ElementRef(e))
                    | Value::Unbound(ElementRef(e))
                    | Value::UnboundMember(ElementRef(e)),
                ],
            ) if self.query => Ok(self.reflect_element(name, *e)),
            (
                "declaredName" | "shortName" | "qualifiedName" | "metaclass" | "docs",
                [Value::Sequence(items)],
            ) if self.query => {
                let mut out = Vec::new();
                for item in items {
                    if let Value::Element(ElementRef(e))
                    | Value::Unbound(ElementRef(e))
                    | Value::UnboundMember(ElementRef(e)) = item
                    {
                        out.extend(self.reflect_element(name, *e).items());
                    }
                }
                Ok(Value::Sequence(out))
            }
            // Fold through `arith` so quantities work: same-dimension
            // items sum (the plain-zero identity coerces), products
            // compose dimensions.
            ("sum", [s]) => items(s)
                .into_iter()
                .try_fold(Value::Integer(0), |acc, v| arith(BinaryOp::Add, acc, v)),
            ("product", [s]) => items(s)
                .into_iter()
                .try_fold(Value::Integer(1), |acc, v| arith(BinaryOp::Mul, acc, v)),
            // A bare unbound feature is a placeholder for an *unknown*
            // sequence: its cardinality comes from the declared
            // multiplicity, never from the placeholder itself. An exact
            // multiplicity answers; a lower/upper bound still settles
            // emptiness; anything else is honestly undecided. Sequences
            // *containing* placeholders keep their literal arity, and
            // library frames never mint Unbound in the first place.
            ("size", [Value::Unbound(ElementRef(e)) | Value::UnboundMember(ElementRef(e))]) => {
                match self.unbound_cardinality(*e) {
                    Some((lo, hi)) if lo == hi && lo.is_finite() => Ok(Value::Integer(lo as i128)),
                    // Indeterminate, not an error — the cardinality is
                    // simply unknown, and downstream arithmetic degrades
                    // with it (this answer is final either way: never
                    // `Unsupported`, the fall-through-to-user-calc
                    // sentinel in invocation dispatch).
                    _ => Ok(Value::Indeterminate),
                }
            }
            ("isEmpty", [Value::Unbound(ElementRef(e)) | Value::UnboundMember(ElementRef(e))]) => {
                match self.unbound_cardinality(*e) {
                    Some((_, 0.0)) => Ok(Value::Boolean(true)),
                    Some((lo, _)) if lo >= 1.0 => Ok(Value::Boolean(false)),
                    _ => Ok(Value::Indeterminate),
                }
            }
            ("notEmpty", [Value::Unbound(ElementRef(e)) | Value::UnboundMember(ElementRef(e))]) => {
                match self.unbound_cardinality(*e) {
                    Some((_, 0.0)) => Ok(Value::Boolean(false)),
                    Some((lo, _)) if lo >= 1.0 => Ok(Value::Boolean(true)),
                    _ => Ok(Value::Indeterminate),
                }
            }
            // Cardinality/emptiness of an indeterminate value is itself
            // indeterminate.
            ("size" | "isEmpty" | "notEmpty", [Value::Indeterminate]) => Ok(Value::Indeterminate),
            ("size", [s]) => Ok(Value::Integer(items(s).len() as i128)),
            ("isEmpty", [s]) => Ok(Value::Boolean(items(s).is_empty())),
            ("notEmpty", [s]) => Ok(Value::Boolean(!items(s).is_empty())),
            ("includes" | "excludes", [s, x]) => {
                let x_unknown = value_is_unknown(x);
                let mut unknown = x_unknown;
                let mut found = false;
                for v in items(s) {
                    if value_is_unknown(&v) || x_unknown {
                        unknown = true;
                    } else if value_eq(&v, x) {
                        found = true;
                        break;
                    }
                }
                Ok(if found {
                    Value::Boolean(name == "includes")
                } else if unknown {
                    Value::Indeterminate
                } else {
                    Value::Boolean(name == "excludes")
                })
            }
            ("head", [s]) => Ok(items(s).first().cloned().unwrap_or_else(Value::null)),
            ("last", [s]) => Ok(items(s).last().cloned().unwrap_or_else(Value::null)),
            ("tail", [s]) => {
                let mut i = items(s);
                if !i.is_empty() {
                    i.remove(0);
                }
                Ok(Value::Sequence(i))
            }
            ("reverse", [s]) => {
                let mut i = items(s);
                i.reverse();
                Ok(Value::Sequence(i))
            }
            ("union", [a, b]) => {
                let mut i = items(a);
                for v in items(b) {
                    if !i.iter().any(|x| value_eq(x, &v)) {
                        i.push(v);
                    }
                }
                Ok(Value::Sequence(i))
            }
            ("max", [s]) => extremum(items(s), true),
            ("min", [s]) => extremum(items(s), false),
            ("max", [a, b]) => extremum(vec![a.clone(), b.clone()], true),
            ("min", [a, b]) => extremum(vec![a.clone(), b.clone()], false),
            ("abs", [v]) => match v {
                Value::Quantity(n, u) => match n.num() {
                    Some(x) => Ok(Value::Quantity(
                        Box::new(Value::from_num(x.abs())),
                        u.clone(),
                    )),
                    None => Err(EvalError::Type("abs needs a number".into())),
                },
                v => match v.num() {
                    Some(x) => Ok(Value::from_num(x.abs())),
                    None => Err(EvalError::Type("abs needs a number".into())),
                },
            },
            // sqrt is `^(1/2)` — on a quantity it also halves the unit
            // exponents. Exact when the root exists (`sqrt(0.25)` is
            // `0.5`), otherwise a double.
            ("sqrt", [v @ Value::Quantity(..)]) => arith(
                BinaryOp::Pow,
                v.clone(),
                Value::Rational(Rational::new(1, 2).expect("non-zero denominator")),
            ),
            ("sqrt", [v]) => match v.num() {
                Some(n) if n.is_negative() => {
                    Err(EvalError::Type("sqrt of a negative number".into()))
                }
                Some(n) => Ok(Value::from_num(n.root(2))),
                None => Err(EvalError::Type("sqrt needs a number".into())),
            },
            ("ln", [v]) => match v.as_f64() {
                Some(f) if f > 0.0 => Ok(Value::Real(f.ln())),
                Some(_) => Err(EvalError::Type("ln of a non-positive number".into())),
                None => Err(EvalError::Type("ln needs a number".into())),
            },
            ("exp", [v]) => num1(v, f64::exp),
            // TrigFunctions (radians).
            ("sin", [v]) => num1(v, f64::sin),
            ("cos", [v]) => num1(v, f64::cos),
            ("tan", [v]) => num1(v, f64::tan),
            // RationalFunctions::rat/numer/denom — exact division and the
            // reduced fraction's parts (a double counts through its exact
            // dyadic value).
            ("rat", [a, b]) => arith(BinaryOp::Div, a.clone(), b.clone()),
            ("numer", [v]) => rational_part(v, true),
            ("denom", [v]) => rational_part(v, false),
            // ComplexFunctions::re/im on real values.
            ("re", [v]) => match v.as_f64() {
                Some(_) => Ok(v.clone()),
                None => Err(EvalError::Type("re needs a number".into())),
            },
            ("im", [v]) => match v.as_f64() {
                Some(_) => Ok(Value::Integer(0)),
                None => Err(EvalError::Type("im needs a number".into())),
            },
            // NumericalFunctions::isZero/isUnit.
            ("isZero", [v]) => match v.num() {
                Some(n) => Ok(Value::Boolean(n.is_zero())),
                None => Err(EvalError::Type("isZero needs a number".into())),
            },
            ("isUnit", [v]) => match v.num() {
                Some(n) => Ok(Value::Boolean(n.is_one())),
                None => Err(EvalError::Type("isUnit needs a number".into())),
            },
            ("log", [v]) => match v.as_f64() {
                Some(f) if f > 0.0 => Ok(Value::Real(f.log10())),
                Some(_) => Err(EvalError::Type("log of a non-positive number".into())),
                None => Err(EvalError::Type("log needs a number".into())),
            },
            ("floor", [v]) => match v.num().and_then(|n| n.floor()) {
                Some(n) => Ok(Value::from_num(n)),
                None => Err(EvalError::Type("floor needs a finite number".into())),
            },
            ("round", [v]) => match v.num().and_then(|n| n.round()) {
                Some(n) => Ok(Value::from_num(n)),
                None => Err(EvalError::Type("round needs a finite number".into())),
            },
            ("ToString", [v]) => Ok(Value::String(match v {
                Value::String(s) => s.clone(),
                other => other.to_string(),
            })),
            ("ToInteger", [Value::String(s)]) => s
                .trim()
                .parse::<i128>()
                .map(Value::Integer)
                .map_err(|_| EvalError::Type(format!("cannot parse `{s}` as Integer"))),
            // A decimal or fraction spelling converts exactly, so
            // `ToString` output reads back; anything else the double
            // parser accepts (`inf`) is approximate.
            ("ToReal", [Value::String(s)]) => Rational::parse(s)
                .map(|r| Value::from_num(Num::Exact(r)))
                .or_else(|| s.trim().parse::<f64>().ok().map(Value::Real))
                .ok_or_else(|| EvalError::Type(format!("cannot parse `{s}` as Real"))),
            ("Length", [Value::String(s)]) => Ok(Value::Integer(s.chars().count() as i128)),
            ("Substring", [Value::String(s), Value::Integer(lo), Value::Integer(hi)]) => {
                // KerML string indexing is 1-based and inclusive.
                let chars: Vec<char> = s.chars().collect();
                let (lo, hi) = (*lo as usize, *hi as usize);
                if lo >= 1 && hi <= chars.len() && lo <= hi + 1 {
                    Ok(Value::String(chars[lo - 1..hi].iter().collect()))
                } else {
                    Err(EvalError::Type("Substring bounds out of range".into()))
                }
            }
            _ => Err(EvalError::Unsupported(format!(
                "function `{}`",
                qn.to_display_string()
            ))),
        }
    }
}

/// Scale a scalar or vector quantity magnitude during same-dimension unit
/// conversion. Components that already carry their own unit are coordinates
/// with an explicit measurement reference and remain verbatim.
fn scale_magnitude(v: Value, factor: &Rational) -> Result<Value, EvalError> {
    match v {
        Value::Integer(_) | Value::Rational(_) | Value::Real(_) => {
            let n = v.num().expect("numeric arm");
            Ok(Value::from_num(n.scale(factor)))
        }
        Value::Sequence(items) => items
            .into_iter()
            .map(|v| match v {
                Value::Quantity(..) => Ok(v),
                v => scale_magnitude(v, factor),
            })
            .collect::<Result<Vec<_>, _>>()
            .map(Value::Sequence),
        Value::Unbound(_) | Value::UnboundMember(_) | Value::Indeterminate => {
            Ok(Value::Indeterminate)
        }
        other => Err(EvalError::Type(format!(
            "a quantity needs a numeric magnitude, got {other}"
        ))),
    }
}

fn is_zero(v: &Value) -> bool {
    v.num().is_some_and(|n| n.is_zero())
}

/// `numer`/`denom` of a number's reduced fraction.
fn rational_part(v: &Value, numer: bool) -> Result<Value, EvalError> {
    let name = if numer { "numer" } else { "denom" };
    let Some(n) = v.num() else {
        return Err(EvalError::Type(format!("{name} needs a number")));
    };
    let Some(r) = n.exact() else {
        return Err(EvalError::Type(format!("{name} needs a finite number")));
    };
    let (num, den) = r.to_string_parts();
    let part = Rational::parse_decimal(if numer { &num } else { &den }).expect("decimal digits");
    Ok(Value::from_num(Num::Exact(part)))
}

/// Whether equality involving this value is undecidable because some part is
/// an unbound or indeterminate value.
fn value_is_unknown(v: &Value) -> bool {
    match v {
        Value::Unbound(_) | Value::UnboundMember(_) | Value::Indeterminate => true,
        Value::Quantity(n, _) => value_is_unknown(n),
        Value::Instance { fields, .. } => fields.iter().any(|(_, v)| value_is_unknown(v)),
        Value::Sequence(items) => items.iter().any(value_is_unknown),
        _ => false,
    }
}

fn value_eq(a: &Value, b: &Value) -> bool {
    match (a, b) {
        (
            Value::Integer(_) | Value::Rational(_) | Value::Real(_),
            Value::Integer(_) | Value::Rational(_) | Value::Real(_),
        ) => match (a.num(), b.num()) {
            (Some(x), Some(y)) => x.eq(&y),
            _ => false,
        },
        (Value::Quantity(x, u), Value::Quantity(y, v)) => {
            if u == v {
                value_eq(x, y)
            } else if same_dims(u, v) {
                match (x.num(), y.num()) {
                    (Some(a), Some(b)) => a.scale(&u.scale).eq(&b.scale(&v.scale)),
                    _ => false,
                }
            } else {
                false
            }
        }
        (
            Value::Instance {
                ty: t1, fields: f1, ..
            },
            Value::Instance {
                ty: t2, fields: f2, ..
            },
        ) => {
            t1 == t2
                && f1.len() == f2.len()
                && f1
                    .iter()
                    .zip(f2)
                    .all(|((n1, v1), (n2, v2))| n1 == n2 && value_eq(v1, v2))
        }
        _ => a == b,
    }
}

fn compare(a: &Value, b: &Value) -> Result<std::cmp::Ordering, EvalError> {
    match (a, b) {
        (Value::String(x), Value::String(y)) => Ok(x.cmp(y)),
        (Value::Quantity(x, u), Value::Quantity(y, v)) => {
            if u == v {
                compare(x, y)
            } else if same_dims(u, v) {
                // Convertible: compare reference magnitudes.
                match (x.num(), y.num()) {
                    (Some(a), Some(b)) => a
                        .scale(&u.scale)
                        .cmp(&b.scale(&v.scale))
                        .ok_or_else(|| EvalError::Type("NaN comparison".into())),
                    _ => Err(EvalError::Type("numeric operands required".into())),
                }
            } else {
                Err(EvalError::Type(format!(
                    "cannot compare quantities in `{}` and `{}`",
                    u.display, v.display
                )))
            }
        }
        (Value::Quantity(..), _) | (_, Value::Quantity(..)) => Err(EvalError::Type(
            "cannot compare a quantity with a plain value".into(),
        )),
        _ => match (a.num(), b.num()) {
            (Some(x), Some(y)) => x
                .cmp(&y)
                .ok_or_else(|| EvalError::Type("NaN comparison".into())),
            _ => Err(EvalError::Type(format!("cannot compare {a} and {b}"))),
        },
    }
}

fn arith(op: BinaryOp, l: Value, r: Value) -> Result<Value, EvalError> {
    use BinaryOp::*;
    // KerML scalars *are* one-element sequences — an operand that
    // arrives as a singleton (a `collect` result, say) is the value.
    let unwrap = |v: Value| match v {
        Value::Sequence(items) if items.len() == 1 => items.into_iter().next().unwrap(),
        v => v,
    };
    let (l, r) = (unwrap(l), unwrap(r));
    // An unknown operand makes the result unknown (see `binary` — folds
    // like `sum`/`product` reach arithmetic through here directly).
    if matches!(
        l,
        Value::Unbound(_) | Value::UnboundMember(_) | Value::Indeterminate
    ) || matches!(
        r,
        Value::Unbound(_) | Value::UnboundMember(_) | Value::Indeterminate
    ) {
        return Ok(Value::Indeterminate);
    }
    if let (Add, Value::String(a), Value::String(b)) = (op, &l, &r) {
        if a.len() + b.len() > MAX_STRING {
            return Err(EvalError::Budget(format!(
                "string of {} bytes exceeds the {MAX_STRING}-byte limit",
                a.len() + b.len()
            )));
        }
        return Ok(Value::String(format!("{a}{b}")));
    }
    // Quantities: same-dimension additive ops (converting across scales
    // — minutes and seconds interoperate), scalar scaling, exponent-map
    // combination for `*`, `/`, and `**`. Combined results fold their
    // scales into the number and take the reference spelling, so the
    // printed magnitude is always true to the printed unit; dimensions
    // that cancel completely leave a plain number.
    let quantity_or_plain = |n: Value, dims: Vec<Dim>, scale: Rational| {
        let unit = Unit::from_dims(dims);
        let n = if scale.is_one() {
            n
        } else {
            match n.num() {
                Some(f) => Value::from_num(f.scale(&scale)),
                None => return Err(EvalError::Type("numeric operands required".into())),
            }
        };
        if unit.dims.is_empty() {
            Ok(n)
        } else {
            Ok(Value::Quantity(Box::new(n), unit))
        }
    };
    match (op, &l, &r) {
        (Add | Sub, Value::Quantity(a, u), Value::Quantity(b, v)) => {
            return if u == v {
                let n = arith(op, (**a).clone(), (**b).clone())?;
                Ok(Value::Quantity(Box::new(n), u.clone()))
            } else if same_dims(u, v) {
                // Convert the right operand into the left's unit.
                let (Some(a), Some(b)) = (a.num(), b.num()) else {
                    return Err(EvalError::Type("numeric operands required".into()));
                };
                let b = b.scale(&scale_ratio(&v.scale, &u.scale));
                let n = if matches!(op, Add) {
                    a.add(&b)
                } else {
                    a.sub(&b)
                };
                Ok(Value::Quantity(Box::new(bounded(n)?), u.clone()))
            } else {
                Err(EvalError::Type(format!(
                    "cannot combine quantities in `{}` and `{}`",
                    u.display, v.display
                )))
            };
        }
        (Mul, Value::Quantity(a, u), Value::Quantity(b, v)) => {
            let n = arith(Mul, (**a).clone(), (**b).clone())?;
            return quantity_or_plain(n, dims_combine(&u.dims, &v.dims, 1), u.scale.mul(&v.scale));
        }
        (Div, Value::Quantity(a, u), Value::Quantity(b, v)) => {
            let n = arith(Div, (**a).clone(), (**b).clone())?;
            return quantity_or_plain(
                n,
                dims_combine(&u.dims, &v.dims, -1),
                scale_ratio(&u.scale, &v.scale),
            );
        }
        (Mul, Value::Quantity(a, u), s) | (Mul, s, Value::Quantity(a, u))
            if matches!(s, Value::Integer(_) | Value::Rational(_) | Value::Real(_)) =>
        {
            let n = arith(Mul, (**a).clone(), s.clone())?;
            return Ok(Value::Quantity(Box::new(n), u.clone()));
        }
        (Div, Value::Quantity(a, u), s)
            if matches!(s, Value::Integer(_) | Value::Rational(_) | Value::Real(_)) =>
        {
            let n = arith(Div, (**a).clone(), s.clone())?;
            return Ok(Value::Quantity(Box::new(n), u.clone()));
        }
        // A scalar over a quantity is a reciprocal-unit quantity
        // (`2/r_leo`, failure rates in `1/h`).
        (Div, s, Value::Quantity(a, u))
            if matches!(s, Value::Integer(_) | Value::Rational(_) | Value::Real(_)) =>
        {
            let n = arith(Div, s.clone(), (**a).clone())?;
            return quantity_or_plain(
                n,
                dims_pow(&u.dims, (-1, 1)),
                scale_ratio(&Rational::one(), &u.scale),
            );
        }
        // A quantity raised to a numeric power scales its exponents
        // (`x^2`, and after rational division `x^(1/2)` is a root).
        (Pow | Caret, Value::Quantity(a, u), s)
            if matches!(s, Value::Integer(_) | Value::Rational(_) | Value::Real(_)) =>
        {
            let Some(exp) = small_ratio(s) else {
                return Err(EvalError::Unsupported(
                    "a unit exponent beyond simple fractions".into(),
                ));
            };
            let n = arith(op, (**a).clone(), s.clone())?;
            let scale = u.scale.pow_ratio_or_approx(exp);
            return quantity_or_plain(n, dims_pow(&u.dims, exp), scale);
        }
        // A plain *zero* is the additive identity of every dimension
        // (`mass + sum(subcomponents.totalMass)` over no subcomponents is
        // `mass + 0`), so additive ops adopt the quantity's unit. Any
        // other plain number stays an error.
        (Add | Sub, Value::Quantity(..), z) if is_zero(z) => return Ok(l),
        (Add, z, Value::Quantity(..)) if is_zero(z) => return Ok(r),
        (Sub, z, Value::Quantity(a, u)) if is_zero(z) => {
            let n = arith(Sub, Value::Integer(0), (**a).clone())?;
            return Ok(Value::Quantity(Box::new(n), u.clone()));
        }
        (_, Value::Quantity(..), _) | (_, _, Value::Quantity(..)) => {
            return Err(EvalError::Type(
                "cannot mix a quantity and a plain number".into(),
            ));
        }
        _ => {}
    }
    // Plain numbers: exact unless an operand is an approximate double.
    // KFL `IntegerFunctions::'/'` returns Rational — true division, not
    // truncation (`7/2` is `3.5`, `x^(1/2)` is a square root); integer
    // results that outgrow `i128` promote to exact big rationals instead
    // of wrapping.
    let (Some(a), Some(b)) = (l.num(), r.num()) else {
        return Err(EvalError::Type("numeric operands required".into()));
    };
    bounded(match op {
        Add => a.add(&b),
        Sub => a.sub(&b),
        Mul => a.mul(&b),
        Div => a.div(&b)?,
        Rem => a.rem(&b)?,
        Pow | Caret => a.pow(&b),
        _ => unreachable!(),
    })
}

/// An arithmetic result as a value, refused past
/// [`crate::rational::MAX_BITS`]: exact integers no longer wrap, so a fold
/// such as `product(1..1000000)` would otherwise grow without bound one
/// multiplication at a time, each a single step.
fn bounded(n: Num) -> Result<Value, EvalError> {
    if let Num::Exact(r) = &n {
        let bits = r.bits();
        if bits > crate::rational::MAX_BITS {
            return Err(EvalError::Budget(format!(
                "a number of {bits} bits exceeds the {}-bit limit",
                crate::rational::MAX_BITS
            )));
        }
    }
    Ok(Value::from_num(n))
}

fn extremum(items: Vec<Value>, want_max: bool) -> Result<Value, EvalError> {
    let mut best: Option<Value> = None;
    for v in items {
        best = Some(match best {
            None => v,
            Some(b) => {
                let ord = compare(&v, &b)?;
                if ord.is_gt() == want_max && !ord.is_eq() {
                    v
                } else {
                    b
                }
            }
        });
    }
    Ok(best.unwrap_or_else(Value::null))
}

/// A transcendental function: always an approximate double.
fn num1(v: &Value, f: fn(f64) -> f64) -> Result<Value, EvalError> {
    v.as_f64()
        .map(|x| Value::Real(f(x)))
        .ok_or_else(|| EvalError::Type("numeric argument required".into()))
}

pub(crate) fn prepare_unit(b: &mut Builder, elem: usize) {
    let scope = b.owner_scope_of(elem).unwrap_or(0);
    let names: Vec<_> = ["declaredName", "declaredShortName"]
        .into_iter()
        .filter_map(|key| b.elements[elem].props.get(key)?.as_str().map(str::to_owned))
        .collect();
    let mut evaluator = Evaluator {
        b,
        env: Vec::new(),
        in_progress: HashSet::new(),
        overrides: HashMap::new(),
        unbound_receiver: None,
        lib_frames: 0,
        call_depth: 0,
        steps: 0,
        allocated: 0,
        query: false,
    };
    for name in names {
        evaluator.expanded_unit(scope, elem, name, 0);
    }
}

#[cfg(test)]
mod memo_tests {
    use super::*;
    #[test]
    fn unit_memo_replays_imports_and_bypasses_bound_or_recursive_contexts() {
        let mut model = crate::model::Model::new();
        model.add_source("units.sysml", "package B { attribute m; attribute s; } package U { private import B::*; attribute <'m/s'> speed; }");
        let mut r = ResolvedModel::build(&model);
        let elem = r.resolve_qualified("U::speed").unwrap().0;
        let scope = r.b.owner_scope_of(elem).unwrap();
        let mut ev = Evaluator {
            b: &mut r.b,
            env: Vec::new(),
            in_progress: HashSet::new(),
            overrides: HashMap::new(),
            unbound_receiver: None,
            lib_frames: 0,
            call_depth: 0,
            steps: 0,
            allocated: 0,
            query: false,
        };
        ev.b.used_imports.clear();
        // A recursion cutoff must never poison a later complete reduction.
        let shallow = ev.expanded_unit(scope, elem, "m/s".into(), 8);
        assert_eq!(ev.b.semantic_memo.units.iter().count(), 0);
        let full = ev.expanded_unit(scope, elem, "m/s".into(), 0);
        assert_ne!(shallow, full);
        let imports = ev.b.used_imports.clone();
        assert!(
            !imports.is_empty(),
            "spelled components use the wildcard import"
        );
        // Recompute while the imports are already marked, then replay into an
        // empty evidence set: recording only a set difference would lose them.
        ev.b.semantic_memo.units = Default::default();
        assert_eq!(ev.expanded_unit(scope, elem, "m/s".into(), 0), full);
        ev.b.used_imports.clear();
        assert_eq!(ev.expanded_unit(scope, elem, "m/s".into(), 0), full);
        assert_eq!(ev.b.used_imports, imports);
        ev.b.semantic_memo.units = Default::default();
        ev.overrides.insert(elem, Value::Integer(3));
        ev.expanded_unit(scope, elem, "m/s".into(), 0);
        ev.overrides.clear();
        ev.in_progress.insert((scope, elem));
        ev.expanded_unit(scope, elem, "m/s".into(), 0);
        ev.in_progress.clear();
        ev.query = true;
        ev.expanded_unit(scope, elem, "m/s".into(), 0);
        ev.query = false;
        ev.call_depth = 1;
        ev.expanded_unit(scope, elem, "m/s".into(), 0);
        ev.call_depth = 0;
        ev.env.push(("x".into(), Value::Integer(1)));
        ev.expanded_unit(scope, elem, "m/s".into(), 0);
        assert_eq!(ev.b.semantic_memo.units.iter().count(), 0);
    }
}
