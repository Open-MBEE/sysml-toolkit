//! Interval domains and forward evaluation over [`Term`].
//!
//! The propagation backend's value model: every free variable holds a
//! *domain* — a closed real interval, an integer interval, a 3-valued
//! boolean, or an enum-literal set — and terms evaluate to domains that
//! **contain every value the term can take** when each variable ranges
//! over its domain. That containment is the soundness invariant all of
//! interval propagation rests on: real endpoints are exact rationals (so
//! the propagatable operations — `+ − × ÷` — never round at all), integer
//! endpoints saturate, and anything the evaluator cannot bound tightly
//! widens (never narrows). The one place a real endpoint is ever moved is
//! the size cap in [`Ival::new`], which widens an endpoint whose exact
//! fraction has grown past a bit budget to a nearby double — outward, so
//! the enclosure stays sound and a bound spelled by a decimal literal
//! (`0.8`, `1.1`) stays exactly that literal.
//!
//! Empty domains are first-class: an empty operand makes every result
//! empty, and (in propagation) a variable contracted to empty proves the
//! asserted constraint set unsatisfiable.

use std::cmp::Ordering;

use sysmlv2_model::rational::Rational;

use crate::term::{EnumSort, Op, Sort, Term};

// ---------------------------------------------------------------- reals

/// A real endpoint: an exact rational, or an infinity. Derived ordering
/// is the numeric order (`NegInf < Fin(_) < PosInf`, rationals by value).
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum Ext {
    NegInf,
    Fin(Rational),
    PosInf,
}

/// Bit budget for one exact endpoint. Fixpoint iteration over exact
/// fractions can grow numerators and denominators without bound long
/// before the progress epsilon stops it; past this size an endpoint is
/// widened to a nearby double, which is exact again and small.
const MAX_ENDPOINT_BITS: u64 = 1024;

impl Ext {
    pub fn zero() -> Ext {
        Ext::Fin(Rational::zero())
    }

    /// The exact value of a double: infinities map to the infinite
    /// endpoints; `None` for NaN, which carries no ordering information.
    pub fn from_f64(f: f64) -> Option<Ext> {
        if f.is_nan() {
            None
        } else if f == f64::INFINITY {
            Some(Ext::PosInf)
        } else if f == f64::NEG_INFINITY {
            Some(Ext::NegInf)
        } else {
            Rational::from_f64(f).map(Ext::Fin)
        }
    }

    pub fn is_zero(&self) -> bool {
        matches!(self, Ext::Fin(r) if r.is_zero())
    }

    fn is_finite(&self) -> bool {
        matches!(self, Ext::Fin(_))
    }

    /// Sign relative to zero.
    fn sign(&self) -> Ordering {
        match self {
            Ext::NegInf => Ordering::Less,
            Ext::PosInf => Ordering::Greater,
            Ext::Fin(r) => {
                if r.is_negative() {
                    Ordering::Less
                } else if r.is_zero() {
                    Ordering::Equal
                } else {
                    Ordering::Greater
                }
            }
        }
    }

    fn inf_with_sign(s: Ordering) -> Ext {
        match s {
            Ordering::Less => Ext::NegInf,
            Ordering::Greater => Ext::PosInf,
            Ordering::Equal => Ext::zero(),
        }
    }

    pub fn neg(&self) -> Ext {
        match self {
            Ext::NegInf => Ext::PosInf,
            Ext::PosInf => Ext::NegInf,
            Ext::Fin(r) => Ext::Fin(r.neg()),
        }
    }

    /// Exact sum. Interval arithmetic never adds opposite infinities
    /// (lower endpoints are `NegInf`/finite, upper ones finite/`PosInf`,
    /// and empties are handled before any arithmetic); should it ever
    /// happen, the result is the *lower* infinity, which only widens.
    pub fn add(&self, o: &Ext) -> Ext {
        match (self, o) {
            (Ext::Fin(a), Ext::Fin(b)) => Ext::Fin(a.add(b)),
            (Ext::NegInf, _) | (_, Ext::NegInf) => Ext::NegInf,
            _ => Ext::PosInf,
        }
    }

    pub fn sub(&self, o: &Ext) -> Ext {
        self.add(&o.neg())
    }

    /// Exact product. An exactly-zero factor makes the product exactly
    /// zero even against an infinite factor (the finite factor *is* zero,
    /// so every product is zero).
    pub fn mul(&self, o: &Ext) -> Ext {
        if self.is_zero() || o.is_zero() {
            return Ext::zero();
        }
        match (self, o) {
            (Ext::Fin(a), Ext::Fin(b)) => Ext::Fin(a.mul(b)),
            _ => {
                let s = if self.sign() == o.sign() {
                    Ordering::Greater
                } else {
                    Ordering::Less
                };
                Ext::inf_with_sign(s)
            }
        }
    }

    /// Exact quotient for a nonzero divisor: a zero dividend or an
    /// infinite divisor gives an exact zero, an infinite dividend gives
    /// the signed infinity.
    pub fn div(&self, o: &Ext) -> Ext {
        debug_assert!(
            !o.is_zero(),
            "interval division by an exactly-zero endpoint"
        );
        if self.is_zero() || !o.is_finite() {
            return Ext::zero();
        }
        match (self, o) {
            (Ext::Fin(a), Ext::Fin(b)) => Ext::Fin(a.div(b).expect("non-zero divisor")),
            _ => {
                let s = if self.sign() == o.sign() {
                    Ordering::Greater
                } else {
                    Ordering::Less
                };
                Ext::inf_with_sign(s)
            }
        }
    }

    fn min(self, o: Ext) -> Ext {
        if o < self { o } else { self }
    }

    fn max(self, o: Ext) -> Ext {
        if o > self { o } else { self }
    }
}

/// Widen an oversized lower endpoint down to a nearby double (exact
/// again, and small); anything within budget passes through unchanged.
fn cap_lo(e: Ext) -> Ext {
    match &e {
        Ext::Fin(r) if r.bits() > MAX_ENDPOINT_BITS => {
            let f = r.to_f64();
            if f == f64::NEG_INFINITY {
                return Ext::NegInf;
            }
            // `f` is the nearest double, possibly above the value: the
            // double below it is certainly not above.
            Ext::from_f64(f.next_down()).unwrap_or(Ext::NegInf)
        }
        _ => e,
    }
}

/// [`cap_lo`] for an upper endpoint, widening upward.
fn cap_hi(e: Ext) -> Ext {
    match &e {
        Ext::Fin(r) if r.bits() > MAX_ENDPOINT_BITS => {
            let f = r.to_f64();
            if f == f64::INFINITY {
                return Ext::PosInf;
            }
            Ext::from_f64(f.next_up()).unwrap_or(Ext::PosInf)
        }
        _ => e,
    }
}

/// A closed real interval `[lo, hi]` with exact endpoints (which may be
/// ±∞). Empty is canonical `[+∞, −∞]`.
#[derive(Clone, Debug, PartialEq)]
pub(crate) struct Ival {
    pub lo: Ext,
    pub hi: Ext,
}

impl Ival {
    /// All of ℝ.
    pub fn top() -> Ival {
        Ival {
            lo: Ext::NegInf,
            hi: Ext::PosInf,
        }
    }

    /// The empty interval.
    pub fn empty() -> Ival {
        Ival {
            lo: Ext::PosInf,
            hi: Ext::NegInf,
        }
    }

    /// `[lo, hi]`, empty when `lo > hi`. Oversized endpoints are widened
    /// outward to a nearby double (see [`MAX_ENDPOINT_BITS`]).
    pub fn new(lo: Ext, hi: Ext) -> Ival {
        let lo = cap_lo(lo);
        let hi = cap_hi(hi);
        if lo <= hi {
            Ival { lo, hi }
        } else {
            Ival::empty()
        }
    }

    /// The exact value of two doubles as an interval; a NaN endpoint
    /// carries no ordering information, so the only sound domain is ⊤
    /// (canonicalizing to empty would turn an arithmetic artifact into a
    /// false unsat proof).
    #[cfg(test)]
    pub fn from_f64(lo: f64, hi: f64) -> Ival {
        match (Ext::from_f64(lo), Ext::from_f64(hi)) {
            (Some(lo), Some(hi)) => Ival::new(lo, hi),
            _ => Ival::top(),
        }
    }

    pub fn point(x: Rational) -> Ival {
        Ival::new(Ext::Fin(x.clone()), Ext::Fin(x))
    }

    pub fn is_empty(&self) -> bool {
        self.lo > self.hi
    }

    pub fn contains(&self, x: &Ext) -> bool {
        self.lo <= *x && *x <= self.hi
    }

    pub fn contains_rational(&self, x: &Rational) -> bool {
        match (&self.lo, &self.hi) {
            (Ext::PosInf, _) | (_, Ext::NegInf) => false,
            _ => {
                let above_lo = match &self.lo {
                    Ext::NegInf => true,
                    Ext::Fin(l) => l <= x,
                    Ext::PosInf => false,
                };
                let below_hi = match &self.hi {
                    Ext::PosInf => true,
                    Ext::Fin(h) => x <= h,
                    Ext::NegInf => false,
                };
                above_lo && below_hi
            }
        }
    }

    pub fn contains_zero(&self) -> bool {
        self.contains(&Ext::zero())
    }

    pub fn intersect(&self, o: &Ival) -> Ival {
        Ival::new(
            self.lo.clone().max(o.lo.clone()),
            self.hi.clone().min(o.hi.clone()),
        )
    }

    pub fn hull(&self, o: &Ival) -> Ival {
        if self.is_empty() {
            return o.clone();
        }
        if o.is_empty() {
            return self.clone();
        }
        Ival::new(
            self.lo.clone().min(o.lo.clone()),
            self.hi.clone().max(o.hi.clone()),
        )
    }

    pub fn add(&self, o: &Ival) -> Ival {
        if self.is_empty() || o.is_empty() {
            return Ival::empty();
        }
        Ival::new(self.lo.add(&o.lo), self.hi.add(&o.hi))
    }

    pub fn sub(&self, o: &Ival) -> Ival {
        if self.is_empty() || o.is_empty() {
            return Ival::empty();
        }
        Ival::new(self.lo.sub(&o.hi), self.hi.sub(&o.lo))
    }

    pub fn neg(&self) -> Ival {
        if self.is_empty() {
            return Ival::empty();
        }
        Ival::new(self.hi.neg(), self.lo.neg())
    }

    /// Exact product: the hull of the four endpoint products.
    pub fn mul(&self, o: &Ival) -> Ival {
        if self.is_empty() || o.is_empty() {
            return Ival::empty();
        }
        let products = [
            self.lo.mul(&o.lo),
            self.lo.mul(&o.hi),
            self.hi.mul(&o.lo),
            self.hi.mul(&o.hi),
        ];
        let lo = products.iter().cloned().fold(Ext::PosInf, Ext::min);
        let hi = products.into_iter().fold(Ext::NegInf, Ext::max);
        Ival::new(lo, hi)
    }

    /// Real division. A divisor interval containing 0 widens to all of ℝ
    /// — sound, never empty-by-accident (SMT total division makes `x/0`
    /// an unconstrained value).
    pub fn div(&self, o: &Ival) -> Ival {
        if self.is_empty() || o.is_empty() {
            return Ival::empty();
        }
        if o.lo.sign() == Ordering::Greater || o.hi.sign() == Ordering::Less {
            let quotients = [
                self.lo.div(&o.lo),
                self.lo.div(&o.hi),
                self.hi.div(&o.lo),
                self.hi.div(&o.hi),
            ];
            let lo = quotients.iter().cloned().fold(Ext::PosInf, Ext::min);
            let hi = quotients.into_iter().fold(Ext::NegInf, Ext::max);
            return Ival::new(lo, hi);
        }
        Ival::top()
    }

    // Certainly-true / certainly-false comparisons.
    pub fn lt(&self, o: &Ival) -> Tri {
        if self.is_empty() || o.is_empty() {
            return Tri::Empty;
        }
        if self.hi < o.lo {
            Tri::True
        } else if self.lo >= o.hi {
            Tri::False
        } else {
            Tri::Both
        }
    }

    pub fn le(&self, o: &Ival) -> Tri {
        if self.is_empty() || o.is_empty() {
            return Tri::Empty;
        }
        if self.hi <= o.lo {
            Tri::True
        } else if self.lo > o.hi {
            Tri::False
        } else {
            Tri::Both
        }
    }

    pub fn eq(&self, o: &Ival) -> Tri {
        if self.is_empty() || o.is_empty() {
            return Tri::Empty;
        }
        if self.hi < o.lo || o.hi < self.lo {
            Tri::False
        } else if self.lo == self.hi && o.lo == o.hi && self.lo == o.lo {
            Tri::True
        } else {
            Tri::Both
        }
    }
}

// ------------------------------------------------------------- integers

/// A closed integer interval over saturating `i128`. Empty is canonical
/// `[MAX, MIN]`; the saturated endpoints `MIN`/`MAX` read as unbounded.
#[derive(Clone, Copy, Debug, PartialEq)]
pub(crate) struct IntIval {
    pub lo: i128,
    pub hi: i128,
}

impl IntIval {
    pub const TOP: IntIval = IntIval {
        lo: i128::MIN,
        hi: i128::MAX,
    };
    pub const EMPTY: IntIval = IntIval {
        lo: i128::MAX,
        hi: i128::MIN,
    };

    pub fn new(lo: i128, hi: i128) -> IntIval {
        if lo <= hi {
            IntIval { lo, hi }
        } else {
            IntIval::EMPTY
        }
    }

    pub fn point(x: i128) -> IntIval {
        IntIval::new(x, x)
    }

    pub fn is_empty(self) -> bool {
        self.lo > self.hi
    }

    pub fn contains(self, x: i128) -> bool {
        self.lo <= x && x <= self.hi
    }

    pub fn intersect(self, o: IntIval) -> IntIval {
        IntIval::new(self.lo.max(o.lo), self.hi.min(o.hi))
    }

    pub fn hull(self, o: IntIval) -> IntIval {
        if self.is_empty() {
            return o;
        }
        if o.is_empty() {
            return self;
        }
        IntIval::new(self.lo.min(o.lo), self.hi.max(o.hi))
    }

    pub fn add(self, o: IntIval) -> IntIval {
        if self.is_empty() || o.is_empty() {
            return IntIval::EMPTY;
        }
        IntIval::new(self.lo.saturating_add(o.lo), self.hi.saturating_add(o.hi))
    }

    pub fn sub(self, o: IntIval) -> IntIval {
        if self.is_empty() || o.is_empty() {
            return IntIval::EMPTY;
        }
        IntIval::new(self.lo.saturating_sub(o.hi), self.hi.saturating_sub(o.lo))
    }

    pub fn neg(self) -> IntIval {
        if self.is_empty() {
            return IntIval::EMPTY;
        }
        IntIval::new(self.hi.saturating_neg(), self.lo.saturating_neg())
    }

    pub fn mul(self, o: IntIval) -> IntIval {
        if self.is_empty() || o.is_empty() {
            return IntIval::EMPTY;
        }
        let c = [
            self.lo.saturating_mul(o.lo),
            self.lo.saturating_mul(o.hi),
            self.hi.saturating_mul(o.lo),
            self.hi.saturating_mul(o.hi),
        ];
        IntIval::new(*c.iter().min().unwrap(), *c.iter().max().unwrap())
    }

    /// Truncated remainder (Rust `%`: sign follows the dividend) — a
    /// sound bound from the divisor's largest magnitude and the
    /// dividend's sign range.
    pub fn trem(self, o: IntIval) -> IntIval {
        if self.is_empty() || o.is_empty() {
            return IntIval::EMPTY;
        }
        if o.contains(0) {
            // `x % 0` is an SMT total-function free value, so a divisor
            // domain that may be 0 bounds nothing — not just the
            // exactly-{0} divisor.
            return IntIval::TOP;
        }
        let m = o.lo.saturating_abs().max(o.hi.saturating_abs()) - 1;
        let lo = if self.lo < 0 { -m } else { 0 };
        let hi = if self.hi > 0 { m } else { 0 };
        IntIval::new(lo, hi)
    }

    /// The enclosing real interval: exact, with the saturated endpoints
    /// reading as unbounded.
    pub fn to_ival(self) -> Ival {
        if self.is_empty() {
            return Ival::empty();
        }
        let lo = if self.lo == i128::MIN {
            Ext::NegInf
        } else {
            Ext::Fin(Rational::from_integer(self.lo))
        };
        let hi = if self.hi == i128::MAX {
            Ext::PosInf
        } else {
            Ext::Fin(Rational::from_integer(self.hi))
        };
        Ival::new(lo, hi)
    }
}

// -------------------------------------------------- booleans and enums

/// A boolean domain: the subsets of `{true, false}`.
#[derive(Clone, Copy, Debug, PartialEq)]
pub(crate) enum Tri {
    Empty,
    True,
    False,
    Both,
}

impl Tri {
    pub fn point(b: bool) -> Tri {
        if b { Tri::True } else { Tri::False }
    }

    pub fn is_empty(self) -> bool {
        self == Tri::Empty
    }

    pub fn may_true(self) -> bool {
        matches!(self, Tri::True | Tri::Both)
    }

    pub fn may_false(self) -> bool {
        matches!(self, Tri::False | Tri::Both)
    }

    fn join(may_t: bool, may_f: bool) -> Tri {
        match (may_t, may_f) {
            (true, true) => Tri::Both,
            (true, false) => Tri::True,
            (false, true) => Tri::False,
            (false, false) => Tri::Empty,
        }
    }

    pub fn not(self) -> Tri {
        Tri::join(self.may_false(), self.may_true())
    }

    pub fn and(self, o: Tri) -> Tri {
        if self.is_empty() || o.is_empty() {
            return Tri::Empty;
        }
        Tri::join(
            self.may_true() && o.may_true(),
            self.may_false() || o.may_false(),
        )
    }

    pub fn or(self, o: Tri) -> Tri {
        if self.is_empty() || o.is_empty() {
            return Tri::Empty;
        }
        Tri::join(
            self.may_true() || o.may_true(),
            self.may_false() && o.may_false(),
        )
    }

    pub fn xor(self, o: Tri) -> Tri {
        if self.is_empty() || o.is_empty() {
            return Tri::Empty;
        }
        Tri::join(
            (self.may_true() && o.may_false()) || (self.may_false() && o.may_true()),
            (self.may_true() && o.may_true()) || (self.may_false() && o.may_false()),
        )
    }

    pub fn implies(self, o: Tri) -> Tri {
        self.not().or(o)
    }

    pub fn eq(self, o: Tri) -> Tri {
        self.xor(o).not()
    }

    pub fn intersect(self, o: Tri) -> Tri {
        if self.is_empty() || o.is_empty() {
            return Tri::Empty;
        }
        Tri::join(
            self.may_true() && o.may_true(),
            self.may_false() && o.may_false(),
        )
    }

    pub fn hull(self, o: Tri) -> Tri {
        if self.is_empty() {
            return o;
        }
        if o.is_empty() {
            return self;
        }
        Tri::join(
            self.may_true() || o.may_true(),
            self.may_false() || o.may_false(),
        )
    }
}

/// A set of enum-literal positions: a bit vector with one bit per
/// literal, unbounded in width. Trailing zero words are trimmed, so two
/// sets with the same members compare equal whatever width they were
/// built at, and a missing word reads as zero.
#[derive(Clone, Debug, PartialEq)]
pub(crate) struct EnumSet {
    words: Vec<u64>,
}

impl EnumSet {
    const WORD: usize = u64::BITS as usize;

    fn trimmed(mut words: Vec<u64>) -> EnumSet {
        while words.last() == Some(&0) {
            words.pop();
        }
        EnumSet { words }
    }

    /// All `n` literals.
    pub fn all(n: usize) -> EnumSet {
        let mut words = vec![u64::MAX; n / Self::WORD];
        if !n.is_multiple_of(Self::WORD) {
            words.push((1u64 << (n % Self::WORD)) - 1);
        }
        EnumSet::trimmed(words)
    }

    /// The single literal at position `i`.
    pub fn point(i: usize) -> EnumSet {
        let mut words = vec![0; i / Self::WORD + 1];
        words[i / Self::WORD] = 1 << (i % Self::WORD);
        EnumSet { words }
    }

    pub fn is_empty(&self) -> bool {
        self.words.is_empty()
    }

    pub fn contains(&self, i: usize) -> bool {
        self.words
            .get(i / Self::WORD)
            .is_some_and(|w| w & (1 << (i % Self::WORD)) != 0)
    }

    pub fn intersect(&self, o: &EnumSet) -> EnumSet {
        EnumSet::trimmed(
            self.words
                .iter()
                .zip(&o.words)
                .map(|(a, b)| a & b)
                .collect(),
        )
    }

    pub fn hull(&self, o: &EnumSet) -> EnumSet {
        let (long, short) = if self.words.len() >= o.words.len() {
            (self, o)
        } else {
            (o, self)
        };
        let mut words = long.words.clone();
        for (w, s) in words.iter_mut().zip(&short.words) {
            *w |= s;
        }
        EnumSet { words }
    }

    /// The members of `self` that are not in `o`.
    pub fn minus(&self, o: &EnumSet) -> EnumSet {
        EnumSet::trimmed(
            self.words
                .iter()
                .enumerate()
                .map(|(k, a)| a & !o.words.get(k).copied().unwrap_or(0))
                .collect(),
        )
    }

    pub fn is_point(&self) -> bool {
        self.words.iter().map(|w| w.count_ones()).sum::<u32>() == 1
    }

    pub fn eq(&self, o: &EnumSet) -> Tri {
        if self.is_empty() || o.is_empty() {
            return Tri::Empty;
        }
        if self.intersect(o).is_empty() {
            Tri::False
        } else if self.is_point() && o.is_point() && self == o {
            Tri::True
        } else {
            Tri::Both
        }
    }
}

// -------------------------------------------------------------- domains

/// The domain of a term or variable. `Str` is opaque: string variables
/// carry no interval structure, so every string fact stays `Both`.
#[derive(Clone, Debug, PartialEq)]
pub(crate) enum Dom {
    R(Ival),
    I(IntIval),
    B(Tri),
    /// Enum sort index (into the translation's enum table) + literal set.
    E(usize, EnumSet),
    Str,
}

impl Dom {
    pub fn is_empty(&self) -> bool {
        match self {
            Dom::R(v) => v.is_empty(),
            Dom::I(v) => v.is_empty(),
            Dom::B(v) => v.is_empty(),
            Dom::E(_, v) => v.is_empty(),
            Dom::Str => false,
        }
    }

    /// The enclosing real interval of a numeric domain.
    fn as_ival(&self) -> Option<Ival> {
        match self {
            Dom::R(v) => Some(v.clone()),
            Dom::I(v) => Some(v.to_ival()),
            _ => None,
        }
    }

    fn as_tri(&self) -> Option<Tri> {
        match self {
            Dom::B(t) => Some(*t),
            _ => None,
        }
    }

    pub fn hull(self, o: Dom) -> Dom {
        match (self, o) {
            (Dom::R(a), Dom::R(b)) => Dom::R(a.hull(&b)),
            (Dom::I(a), Dom::I(b)) => Dom::I(a.hull(b)),
            (Dom::B(a), Dom::B(b)) => Dom::B(a.hull(b)),
            (Dom::E(s, a), Dom::E(t, b)) if s == t => Dom::E(s, a.hull(&b)),
            (Dom::Str, Dom::Str) => Dom::Str,
            // Mixed numeric kinds hull as reals; anything else has no
            // common structure — ⊤ of the real line is the widest thing
            // we can say (such terms are sort errors upstream anyway).
            (a, b) => match (a.as_ival(), b.as_ival()) {
                (Some(x), Some(y)) => Dom::R(x.hull(&y)),
                _ => Dom::R(Ival::top()),
            },
        }
    }
}

/// Forward (bottom-up) evaluation of a term over variable domains: the
/// result contains every value the term can take with each variable in
/// its domain. Unknown shapes widen to ⊤ of their kind — never narrow.
pub(crate) fn eval_term(t: &Term, doms: &[Dom]) -> Dom {
    match t {
        Term::BoolLit(b) => Dom::B(Tri::point(*b)),
        Term::IntLit(i) => Dom::I(IntIval::point(*i)),
        // Exact: the literal's own value, a point.
        Term::RealLit(r) => Dom::R(Ival::point(r.clone())),
        Term::StrLit(_) => Dom::Str,
        Term::Var(i) => doms[*i].clone(),
        Term::EnumLit(sort, pos) => Dom::E(*sort, EnumSet::point(*pos)),
        Term::App(op, args) => {
            // Every operand is evaluated exactly once: left-deep chains
            // (quantifier expansions, sequence folds) would otherwise
            // cost 2^depth evaluations.
            let mut kids: Vec<Option<Dom>> =
                args.iter().map(|a| Some(eval_term(a, doms))).collect();
            if let Some(k) = kids
                .iter()
                .position(|k| k.as_ref().is_some_and(Dom::is_empty))
            {
                // An empty operand poisons the whole application; keep
                // the kind of the first empty operand — callers only ask
                // `is_empty`.
                return kids[k].take().expect("operand evaluated above");
            }
            let mut a = |i: usize| kids[i].take().expect("each operand is consumed once");
            let tri = |d: Dom| d.as_tri().unwrap_or(Tri::Both);
            let num = |d: Dom| d.as_ival().unwrap_or_else(Ival::top);
            match op {
                Op::Not => Dom::B(tri(a(0)).not()),
                Op::And => Dom::B(tri(a(0)).and(tri(a(1)))),
                Op::Or => Dom::B(tri(a(0)).or(tri(a(1)))),
                Op::Xor => Dom::B(tri(a(0)).xor(tri(a(1)))),
                Op::Implies => Dom::B(tri(a(0)).implies(tri(a(1)))),
                Op::Eq => Dom::B(match (a(0), a(1)) {
                    (Dom::B(x), Dom::B(y)) => x.eq(y),
                    (Dom::E(s, x), Dom::E(t, y)) if s == t => x.eq(&y),
                    (Dom::Str, _) | (_, Dom::Str) => Tri::Both,
                    (x, y) => match (x.as_ival(), y.as_ival()) {
                        (Some(u), Some(v)) => u.eq(&v),
                        _ => Tri::Both,
                    },
                }),
                Op::Lt => Dom::B(num(a(0)).lt(&num(a(1)))),
                Op::Le => Dom::B(num(a(0)).le(&num(a(1)))),
                Op::Gt => Dom::B(num(a(1)).lt(&num(a(0)))),
                Op::Ge => Dom::B(num(a(1)).le(&num(a(0)))),
                Op::Add | Op::Sub | Op::Mul => match (a(0), a(1)) {
                    // Integer structure survives integer arithmetic.
                    (Dom::I(x), Dom::I(y)) => Dom::I(match op {
                        Op::Add => x.add(y),
                        Op::Sub => x.sub(y),
                        _ => x.mul(y),
                    }),
                    (x, y) => {
                        let (u, v) = (num(x), num(y));
                        Dom::R(match op {
                            Op::Add => u.add(&v),
                            Op::Sub => u.sub(&v),
                            _ => u.mul(&v),
                        })
                    }
                },
                // SMT division is always real-valued (operands coerced).
                Op::Div => Dom::R(num(a(0)).div(&num(a(1)))),
                Op::TRem => match (a(0), a(1)) {
                    (Dom::I(x), Dom::I(y)) => Dom::I(x.trem(y)),
                    _ => Dom::I(IntIval::TOP),
                },
                Op::Neg => match a(0) {
                    Dom::I(x) => Dom::I(x.neg()),
                    x => Dom::R(num(x).neg()),
                },
                Op::Ite => match tri(a(0)) {
                    Tri::True => a(1),
                    Tri::False => a(2),
                    Tri::Empty => Dom::B(Tri::Empty),
                    Tri::Both => a(1).hull(a(2)),
                },
            }
        }
    }
}

// ------------------------------------------------ backward contraction

/// The largest integer interval inside a real interval: endpoints
/// rounded *inward* to integers (`ceil`/`floor`), saturating beyond the
/// machine range; an infinite endpoint stays saturated.
fn ival_to_int(w: &Ival) -> IntIval {
    if w.is_empty() {
        return IntIval::EMPTY;
    }
    let lo = match &w.lo {
        Ext::NegInf => i128::MIN,
        Ext::PosInf => i128::MAX,
        Ext::Fin(r) => saturating_i128(&r.ceil()),
    };
    let hi = match &w.hi {
        Ext::PosInf => i128::MAX,
        Ext::NegInf => i128::MIN,
        Ext::Fin(r) => saturating_i128(&r.floor()),
    };
    IntIval::new(lo, hi)
}

/// An integral rational as a machine integer, saturating to the end of
/// the range it overflows.
fn saturating_i128(r: &Rational) -> i128 {
    match r.to_i128() {
        Some(i) => i,
        None if r.is_negative() => i128::MIN,
        None => i128::MAX,
    }
}

impl Dom {
    /// Intersect this domain with a demanded (`want`) domain of the same or
    /// a compatible numeric kind. A real want against an integer domain
    /// rounds inward; a kind mismatch (a sort error upstream) narrows
    /// nothing — the result is always a *subset* of `self`, so applying it
    /// can only tighten.
    pub(crate) fn narrow(self, want: &Dom) -> Dom {
        match self {
            Dom::R(a) => match want.as_ival() {
                Some(w) => Dom::R(a.intersect(&w)),
                None => Dom::R(a),
            },
            Dom::I(a) => match want {
                Dom::I(w) => Dom::I(a.intersect(*w)),
                Dom::R(w) => Dom::I(a.intersect(ival_to_int(w))),
                _ => Dom::I(a),
            },
            Dom::B(a) => match want {
                Dom::B(w) => Dom::B(a.intersect(*w)),
                _ => Dom::B(a),
            },
            Dom::E(s, a) => match want {
                Dom::E(t, w) if *t == s => Dom::E(s, a.intersect(w)),
                _ => Dom::E(s, a),
            },
            Dom::Str => Dom::Str,
        }
    }
}

/// The effect of one backward-contraction step.
#[derive(Clone, Copy, PartialEq, Debug)]
pub(crate) enum Refine {
    /// A domain was emptied or a literal contradicted its demand: the
    /// asserted term is unsatisfiable in the current domains.
    Bottom,
    /// At least one domain tightened (by more than the epsilon, for reals).
    Changed,
    /// Nothing tightened.
    Unchanged,
}

fn meet(a: Refine, b: Refine) -> Refine {
    match (a, b) {
        (Refine::Bottom, _) | (_, Refine::Bottom) => Refine::Bottom,
        (Refine::Changed, _) | (_, Refine::Changed) => Refine::Changed,
        _ => Refine::Unchanged,
    }
}

fn as_ival_or_top(d: &Dom) -> Ival {
    d.as_ival().unwrap_or_else(Ival::top)
}

fn as_tri_or_both(d: &Dom) -> Tri {
    d.as_tri().unwrap_or(Tri::Both)
}

/// Is `new` (a subset of `old`) tighter than `old` by enough to be worth
/// applying? Discrete domains progress in finite steps, so any change
/// counts; real endpoints must move by more than a relative epsilon
/// (measured on their double approximations), which (with the driver's
/// iteration cap) guarantees the fixpoint terminates rather than
/// crawling by ever-smaller fractions forever.
fn meaningful(old: &Dom, new: &Dom, eps: f64) -> bool {
    match (old, new) {
        (Dom::R(a), Dom::R(b)) => {
            // An infinite endpoint that became finite is progress by any
            // measure; the relative test below only compares finite
            // endpoints (`∞ − ∞` carries no information).
            if (!a.lo.is_finite() && b.lo.is_finite()) || (!a.hi.is_finite() && b.hi.is_finite()) {
                return true;
            }
            // The scale comes from the finite endpoints alone: an infinite
            // endpoint must not inflate the tolerance to the double range,
            // which would freeze the finite side of a half-line forever.
            let finite_mag = |e: &Ext| match e {
                Ext::Fin(r) => r.to_f64().abs().min(f64::MAX),
                _ => 0.0,
            };
            let scale = 1.0 + finite_mag(&a.lo).max(finite_mag(&a.hi));
            let tol = eps * scale;
            let moved = |from: &Ext, to: &Ext| match (from, to) {
                (Ext::Fin(x), Ext::Fin(y)) => (y.to_f64() - x.to_f64()).abs() > tol,
                _ => false,
            };
            moved(&a.lo, &b.lo) || moved(&a.hi, &b.hi)
        }
        _ => true,
    }
}

/// HC4-style backward pass: contract the domains so that the leaves of `t`
/// keep only assignments under which `t` can take a value in `want`. The
/// soundness invariant — every satisfying assignment survives — holds
/// because every step either intersects a domain with a sound bound or
/// leaves it alone; nothing ever widens. Returns [`Refine::Bottom`] when a
/// domain empties or a literal contradicts `want` (a local unsat proof).
pub(crate) fn refine_term(t: &Term, want: Dom, doms: &mut [Dom], eps: f64) -> Refine {
    if want.is_empty() {
        return Refine::Bottom;
    }
    match t {
        Term::Var(i) => {
            let old = doms[*i].clone();
            let new = old.clone().narrow(&want);
            if new == old {
                Refine::Unchanged
            } else if new.is_empty() {
                doms[*i] = new;
                Refine::Bottom
            } else if meaningful(&old, &new, eps) {
                doms[*i] = new;
                Refine::Changed
            } else {
                Refine::Unchanged
            }
        }
        Term::BoolLit(b) => {
            let t = as_tri_or_both(&want);
            let ok = if *b { t.may_true() } else { t.may_false() };
            if ok {
                Refine::Unchanged
            } else {
                Refine::Bottom
            }
        }
        Term::IntLit(i) => {
            // Against an integer demand the check is exact; otherwise fall
            // back to the enclosing real interval (also exact).
            let ok = match &want {
                Dom::I(iv) => iv.contains(*i),
                _ => as_ival_or_top(&want).contains_rational(&Rational::from_integer(*i)),
            };
            if ok {
                Refine::Unchanged
            } else {
                Refine::Bottom
            }
        }
        Term::RealLit(r) => {
            if as_ival_or_top(&want).contains_rational(r) {
                Refine::Unchanged
            } else {
                Refine::Bottom
            }
        }
        Term::EnumLit(s, pos) => match &want {
            Dom::E(t, set) if t == s && !set.contains(*pos) => Refine::Bottom,
            _ => Refine::Unchanged,
        },
        Term::StrLit(_) => Refine::Unchanged,
        Term::App(op, args) => refine_app(*op, args, want, doms, eps),
    }
}

/// The `App` case of [`refine_term`], split out to keep leaf handling
/// readable. `a0`/`a1`/`a2` name the operands; forward child domains are
/// recomputed as needed (the trees are small).
fn refine_app(op: Op, args: &[Term], want: Dom, doms: &mut [Dom], eps: f64) -> Refine {
    let a0 = &args[0];
    match op {
        Op::Not => refine_term(a0, Dom::B(as_tri_or_both(&want).not()), doms, eps),
        Op::And => match as_tri_or_both(&want) {
            Tri::True => meet(
                refine_term(a0, Dom::B(Tri::True), doms, eps),
                refine_term(&args[1], Dom::B(Tri::True), doms, eps),
            ),
            Tri::False => {
                // The conjunction is false: whichever operand is pinned
                // true forces the other false.
                let f0 = as_tri_or_both(&eval_term(a0, doms));
                let f1 = as_tri_or_both(&eval_term(&args[1], doms));
                let mut acc = Refine::Unchanged;
                if !f1.may_false() {
                    acc = meet(acc, refine_term(a0, Dom::B(Tri::False), doms, eps));
                }
                if !f0.may_false() {
                    acc = meet(acc, refine_term(&args[1], Dom::B(Tri::False), doms, eps));
                }
                acc
            }
            _ => Refine::Unchanged,
        },
        Op::Or => match as_tri_or_both(&want) {
            Tri::False => meet(
                refine_term(a0, Dom::B(Tri::False), doms, eps),
                refine_term(&args[1], Dom::B(Tri::False), doms, eps),
            ),
            Tri::True => {
                let f0 = as_tri_or_both(&eval_term(a0, doms));
                let f1 = as_tri_or_both(&eval_term(&args[1], doms));
                let mut acc = Refine::Unchanged;
                if !f1.may_true() {
                    acc = meet(acc, refine_term(a0, Dom::B(Tri::True), doms, eps));
                }
                if !f0.may_true() {
                    acc = meet(acc, refine_term(&args[1], Dom::B(Tri::True), doms, eps));
                }
                acc
            }
            _ => Refine::Unchanged,
        },
        Op::Implies => match as_tri_or_both(&want) {
            Tri::True => {
                let f0 = as_tri_or_both(&eval_term(a0, doms));
                let f1 = as_tri_or_both(&eval_term(&args[1], doms));
                let mut acc = Refine::Unchanged;
                if !f0.may_false() {
                    acc = meet(acc, refine_term(&args[1], Dom::B(Tri::True), doms, eps));
                }
                if !f1.may_true() {
                    acc = meet(acc, refine_term(a0, Dom::B(Tri::False), doms, eps));
                }
                acc
            }
            // a ⇒ b false ⟺ a ∧ ¬b.
            Tri::False => meet(
                refine_term(a0, Dom::B(Tri::True), doms, eps),
                refine_term(&args[1], Dom::B(Tri::False), doms, eps),
            ),
            _ => Refine::Unchanged,
        },
        Op::Xor => {
            // `xor` true ⟺ operands differ; false ⟺ they agree.
            let want_diff = match as_tri_or_both(&want) {
                Tri::True => true,
                Tri::False => false,
                _ => return Refine::Unchanged,
            };
            let f0 = as_tri_or_both(&eval_term(a0, doms));
            let f1 = as_tri_or_both(&eval_term(&args[1], doms));
            let force = |known: Tri| match known {
                Tri::True => Some(Tri::point(!want_diff)),
                Tri::False => Some(Tri::point(want_diff)),
                _ => None,
            };
            let mut acc = Refine::Unchanged;
            if let Some(w) = force(f1) {
                acc = meet(acc, refine_term(a0, Dom::B(w), doms, eps));
            }
            if let Some(w) = force(f0) {
                acc = meet(acc, refine_term(&args[1], Dom::B(w), doms, eps));
            }
            acc
        }
        Op::Eq => match as_tri_or_both(&want) {
            Tri::True => {
                // Each side is confined to the other's domain.
                let c0 = eval_term(a0, doms);
                let c1 = eval_term(&args[1], doms);
                meet(
                    refine_term(a0, c1, doms, eps),
                    refine_term(&args[1], c0, doms, eps),
                )
            }
            Tri::False => {
                // Only excludable when the other side is a definite point
                // (booleans; a single enum literal).
                let c0 = eval_term(a0, doms);
                let c1 = eval_term(&args[1], doms);
                let mut acc = Refine::Unchanged;
                if let Some(w) = exclude(&c1, &c0) {
                    acc = meet(acc, refine_term(a0, w, doms, eps));
                }
                if let Some(w) = exclude(&c0, &c1) {
                    acc = meet(acc, refine_term(&args[1], w, doms, eps));
                }
                acc
            }
            _ => Refine::Unchanged,
        },
        Op::Lt | Op::Le => {
            let x = as_ival_or_top(&eval_term(a0, doms));
            let y = as_ival_or_top(&eval_term(&args[1], doms));
            match as_tri_or_both(&want) {
                // x ≤ y: closed-interval bounds over-approximate `<`.
                Tri::True => meet(
                    refine_term(a0, Dom::R(Ival::new(Ext::NegInf, y.hi)), doms, eps),
                    refine_term(&args[1], Dom::R(Ival::new(x.lo, Ext::PosInf)), doms, eps),
                ),
                // ¬(x < y) ⟺ x ≥ y.
                Tri::False => meet(
                    refine_term(a0, Dom::R(Ival::new(y.lo, Ext::PosInf)), doms, eps),
                    refine_term(&args[1], Dom::R(Ival::new(Ext::NegInf, x.hi)), doms, eps),
                ),
                _ => Refine::Unchanged,
            }
        }
        Op::Gt | Op::Ge => {
            let x = as_ival_or_top(&eval_term(a0, doms));
            let y = as_ival_or_top(&eval_term(&args[1], doms));
            match as_tri_or_both(&want) {
                Tri::True => meet(
                    refine_term(a0, Dom::R(Ival::new(y.lo, Ext::PosInf)), doms, eps),
                    refine_term(&args[1], Dom::R(Ival::new(Ext::NegInf, x.hi)), doms, eps),
                ),
                Tri::False => meet(
                    refine_term(a0, Dom::R(Ival::new(Ext::NegInf, y.hi)), doms, eps),
                    refine_term(&args[1], Dom::R(Ival::new(x.lo, Ext::PosInf)), doms, eps),
                ),
                _ => Refine::Unchanged,
            }
        }
        // z = x + y  ⟹  x ∈ z − y,  y ∈ z − x.
        Op::Add => {
            let w = as_ival_or_top(&want);
            let x = as_ival_or_top(&eval_term(a0, doms));
            let y = as_ival_or_top(&eval_term(&args[1], doms));
            meet(
                refine_term(a0, Dom::R(w.sub(&y)), doms, eps),
                refine_term(&args[1], Dom::R(w.sub(&x)), doms, eps),
            )
        }
        // z = x − y  ⟹  x ∈ z + y,  y ∈ x − z.
        Op::Sub => {
            let w = as_ival_or_top(&want);
            let x = as_ival_or_top(&eval_term(a0, doms));
            let y = as_ival_or_top(&eval_term(&args[1], doms));
            meet(
                refine_term(a0, Dom::R(w.add(&y)), doms, eps),
                refine_term(&args[1], Dom::R(x.sub(&w)), doms, eps),
            )
        }
        // z = x·y  ⟹  x ∈ z/y,  y ∈ z/x  (division through zero widens to
        // ⊤, so it never over-narrows).
        Op::Mul => {
            let w = as_ival_or_top(&want);
            let x = as_ival_or_top(&eval_term(a0, doms));
            let y = as_ival_or_top(&eval_term(&args[1], doms));
            meet(
                refine_term(a0, Dom::R(w.div(&y)), doms, eps),
                refine_term(&args[1], Dom::R(w.div(&x)), doms, eps),
            )
        }
        // z = x/y  ⟹  x ∈ z·y,  y ∈ x/z — but only where the divisor
        // is nonzero. SMT division is total: `x/0` is a free value that
        // can lie in any `want`, so a divisor domain containing 0
        // constrains neither the dividend (skip its contraction) nor its
        // own zero (keep 0 in the demand) — the forward pass's widening,
        // mirrored.
        Op::Div => {
            let w = as_ival_or_top(&want);
            let x = as_ival_or_top(&eval_term(a0, doms));
            let y = as_ival_or_top(&eval_term(&args[1], doms));
            let acc = if y.contains_zero() {
                Refine::Unchanged
            } else {
                refine_term(a0, Dom::R(w.mul(&y)), doms, eps)
            };
            let yd = if y.contains_zero() {
                x.div(&w).hull(&Ival::point(Rational::zero()))
            } else {
                x.div(&w)
            };
            meet(acc, refine_term(&args[1], Dom::R(yd), doms, eps))
        }
        Op::Neg => refine_term(a0, Dom::R(as_ival_or_top(&want).neg()), doms, eps),
        // No useful inverse for truncated remainder.
        Op::TRem => Refine::Unchanged,
        Op::Ite => match as_tri_or_both(&eval_term(a0, doms)) {
            Tri::Empty => Refine::Bottom,
            Tri::True => refine_term(&args[1], want, doms, eps),
            Tri::False => refine_term(&args[2], want, doms, eps),
            Tri::Both => {
                // The condition is undecided: if a branch cannot meet
                // `want`, the condition must select the other.
                let then_ok = !eval_term(&args[1], doms).narrow(&want).is_empty();
                let else_ok = !eval_term(&args[2], doms).narrow(&want).is_empty();
                match (then_ok, else_ok) {
                    (false, false) => Refine::Bottom,
                    (false, true) => meet(
                        refine_term(a0, Dom::B(Tri::False), doms, eps),
                        refine_term(&args[2], want, doms, eps),
                    ),
                    (true, false) => meet(
                        refine_term(a0, Dom::B(Tri::True), doms, eps),
                        refine_term(&args[1], want, doms, eps),
                    ),
                    (true, true) => Refine::Unchanged,
                }
            }
        },
    }
}

/// The domain a `!=` (or `==`-is-false) partner must avoid, when the known
/// side is a definite point: the negation of a boolean, or the partner's
/// own forward domain (`partner`) with exactly that one literal removed.
/// Numeric point-exclusion has no interval representation, so it returns
/// `None` (no contraction).
fn exclude(known: &Dom, partner: &Dom) -> Option<Dom> {
    match (known, partner) {
        (Dom::B(Tri::True), _) => Some(Dom::B(Tri::False)),
        (Dom::B(Tri::False), _) => Some(Dom::B(Tri::True)),
        (Dom::E(s, set), Dom::E(t, rest)) if s == t && set.is_point() => {
            Some(Dom::E(*s, rest.minus(set)))
        }
        _ => None,
    }
}

/// Iterate the asserted `facts` (each demanded `true`) to a fixpoint over
/// `doms`, contracting shared variables across constraints. Terminates at
/// the first quiescent pass or after `max_iters` (SysMD caps at 100).
/// Returns the contracted domains and whether the asserted set was proved
/// unsatisfiable (a domain emptied or a literal contradicted).
pub(crate) fn drive(mut doms: Vec<Dom>, facts: &[Term], max_iters: usize) -> (Vec<Dom>, bool) {
    const EPS: f64 = 1e-9;
    let mut unsat = doms.iter().any(|d| d.is_empty());
    let mut pass = 0;
    while !unsat && pass < max_iters {
        let mut changed = false;
        for t in facts {
            match refine_term(t, Dom::B(Tri::True), &mut doms, EPS) {
                Refine::Bottom => {
                    unsat = true;
                    break;
                }
                Refine::Changed => changed = true,
                Refine::Unchanged => {}
            }
        }
        if doms.iter().any(|d| d.is_empty()) {
            unsat = true;
        }
        if !changed {
            break;
        }
        pass += 1;
    }
    (doms, unsat)
}

// -------------------------------------------------- domains ↔ the model

/// The initial (widest) domain of a variable of the given sort: ⊤ of its
/// kind. `enum_sizes` maps an enum sort index to its literal count.
pub(crate) fn init_dom(sort: Sort, enum_sizes: &[usize]) -> Dom {
    match sort {
        Sort::Bool => Dom::B(Tri::Both),
        Sort::Int => Dom::I(IntIval::TOP),
        Sort::Real => Dom::R(Ival::top()),
        Sort::Str => Dom::Str,
        Sort::Enum(i) => Dom::E(i, EnumSet::all(enum_sizes[i])),
    }
}

/// Render a real endpoint: exact (a terminating decimal or a reduced
/// fraction) or, with `approx`, a non-terminating fraction as a marked
/// approximate decimal for glanceable surfaces.
fn fmt_ext(x: &Ext, approx: bool) -> String {
    match x {
        Ext::PosInf => "+∞".into(),
        Ext::NegInf => "−∞".into(),
        Ext::Fin(r) if approx => r.to_approx_string(),
        Ext::Fin(r) => r.to_string(),
    }
}

fn fmt_i(x: i128) -> String {
    if x == i128::MAX {
        "+∞".into()
    } else if x == i128::MIN {
        "−∞".into()
    } else {
        x.to_string()
    }
}

/// Render a domain as a closed range or set, for `--ranges` output
/// (`approx = false`, exact endpoints) and for editor hints (`approx =
/// true`, non-terminating endpoints as approximate decimals). Enum
/// literals use their model-facing names.
pub(crate) fn fmt_dom(d: &Dom, enums: &[EnumSort], approx: bool) -> String {
    match d {
        Dom::R(v) if v.is_empty() => "∅".into(),
        Dom::R(v) => format!("[{}, {}]", fmt_ext(&v.lo, approx), fmt_ext(&v.hi, approx)),
        Dom::I(v) if v.is_empty() => "∅".into(),
        Dom::I(v) => format!("[{}, {}]", fmt_i(v.lo), fmt_i(v.hi)),
        Dom::B(Tri::True) => "{true}".into(),
        Dom::B(Tri::False) => "{false}".into(),
        Dom::B(Tri::Both) => "{true, false}".into(),
        Dom::B(Tri::Empty) => "∅".into(),
        Dom::E(_, set) if set.is_empty() => "∅".into(),
        Dom::E(s, set) => {
            let names: Vec<&str> = enums[*s]
                .displays
                .iter()
                .enumerate()
                .filter(|(i, _)| set.contains(*i))
                .map(|(_, n)| n.as_str())
                .collect();
            format!("{{{}}}", names.join(", "))
        }
        Dom::Str => "string".into(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn iv(lo: f64, hi: f64) -> Ival {
        Ival::from_f64(lo, hi)
    }

    fn pt(x: f64) -> Ival {
        Ival::from_f64(x, x)
    }

    trait ContainsF64 {
        fn contains_rational_f64(&self, x: f64) -> bool;
    }
    impl ContainsF64 for Ival {
        fn contains_rational_f64(&self, x: f64) -> bool {
            Ext::from_f64(x).is_some_and(|e| self.contains(&e))
        }
    }

    fn dec(s: &str) -> Rational {
        Rational::parse_decimal(s).unwrap()
    }

    // -- interval arithmetic ------------------------------------------------

    #[test]
    fn real_ops_basics() {
        let a = iv(1.0, 2.0);
        let b = iv(-3.0, 4.0);
        assert!(a.add(&b).contains_rational_f64(-2.0) && a.add(&b).contains_rational_f64(6.0));
        assert!(a.sub(&b).contains_rational_f64(-3.0) && a.sub(&b).contains_rational_f64(5.0));
        assert!(a.mul(&b).contains_rational_f64(-6.0) && a.mul(&b).contains_rational_f64(8.0));
        assert_eq!(Ival::empty().add(&a), Ival::empty());
        assert!(a.div(&pt(0.0)) == Ival::top());
        assert!(b.div(&a).contains_rational_f64(4.0) && b.div(&a).contains_rational_f64(-3.0));
        // Divisor straddling zero widens to ⊤, never errs.
        assert_eq!(a.div(&b), Ival::top());
    }

    #[test]
    fn arithmetic_is_exact() {
        // No rounding anywhere: decimal literals combine to decimal
        // results, and inverses recover the operands exactly.
        let tenth = Ival::point(dec("0.1"));
        let fifth = Ival::point(dec("0.2"));
        assert_eq!(tenth.add(&fifth), Ival::point(dec("0.3")));
        assert_eq!(
            Ival::point(dec("1.1")).mul(&Ival::point(dec("100"))),
            Ival::point(dec("110"))
        );
        let third = Ival::point(dec("1")).div(&Ival::point(dec("3")));
        assert_eq!(third, Ival::point(Rational::new(1, 3).unwrap()));
        assert_eq!(third.mul(&Ival::point(dec("3"))), Ival::point(dec("1")));
        let x = iv(0.8, 1.1);
        assert_eq!(x.add(&fifth).sub(&fifth), x);
    }

    #[test]
    fn zero_times_unbounded_is_zero() {
        assert_eq!(pt(0.0).mul(&Ival::top()), pt(0.0));
    }

    #[test]
    fn infinite_endpoints_behave() {
        let half_line = Ival::new(Ext::Fin(dec("10")), Ext::PosInf);
        assert_eq!(
            half_line.add(&half_line),
            Ival::new(Ext::Fin(dec("20")), Ext::PosInf)
        );
        // ∞ − ∞ never fabricates an empty interval.
        let d = half_line.sub(&half_line);
        assert!(!d.is_empty() && d.contains_zero(), "{d:?}");
        assert_eq!(
            half_line.neg(),
            Ival::new(Ext::NegInf, Ext::Fin(dec("-10")))
        );
        assert_eq!(
            half_line.mul(&Ival::new(Ext::Fin(dec("2")), Ext::PosInf)),
            Ival::new(Ext::Fin(dec("20")), Ext::PosInf)
        );
        // [1, +∞] / [2, +∞] = [0, +∞]: a finite over an infinite is 0.
        assert_eq!(
            Ival::new(Ext::Fin(dec("1")), Ext::PosInf)
                .div(&Ival::new(Ext::Fin(dec("2")), Ext::PosInf)),
            Ival::new(Ext::zero(), Ext::PosInf)
        );
        // NaN reaching the constructor widens instead of emptying.
        assert_eq!(Ival::from_f64(f64::NAN, f64::NAN), Ival::top());
        assert_eq!(
            Ival::from_f64(f64::NEG_INFINITY, f64::INFINITY),
            Ival::top()
        );
    }

    #[test]
    fn oversized_endpoints_widen_outward() {
        // An endpoint whose exact fraction outgrows the bit budget is
        // replaced by a nearby double, on the widening side.
        let big = Rational::from_integer(3).pow(2000).unwrap();
        let tiny = big.recip().unwrap(); // 3^-2000: far more than 1024 bits
        let one_plus = Rational::one().add(&tiny);
        let i = Ival::new(Ext::Fin(one_plus.clone()), Ext::Fin(one_plus.clone()));
        assert!(!i.is_empty());
        assert!(i.contains_rational(&one_plus));
        let (Ext::Fin(lo), Ext::Fin(hi)) = (&i.lo, &i.hi) else {
            panic!("{i:?}");
        };
        assert!(lo.bits() <= 64 && hi.bits() <= 64, "{i:?}");
        assert!(*lo < one_plus && one_plus < *hi);
        // Within budget nothing moves: a decimal literal bound stays
        // exactly itself.
        assert_eq!(Ival::point(dec("0.8")).lo, Ext::Fin(dec("0.8")));
    }

    #[test]
    fn comparisons_certainty() {
        let a = iv(1.0, 2.0);
        let b = iv(3.0, 4.0);
        assert_eq!(a.lt(&b), Tri::True);
        assert_eq!(b.lt(&a), Tri::False);
        assert_eq!(a.lt(&iv(1.5, 5.0)), Tri::Both);
        assert_eq!(a.le(&iv(2.0, 5.0)), Tri::True);
        assert_eq!(pt(2.0).eq(&pt(2.0)), Tri::True);
        assert_eq!(a.eq(&b), Tri::False);
        assert_eq!(a.eq(&iv(2.0, 3.0)), Tri::Both);
        // Exact comparison across decimal and dyadic spellings.
        assert_eq!(
            Ival::point(dec("0.3")).eq(&Ival::point(dec("0.1")).add(&Ival::point(dec("0.2")))),
            Tri::True
        );
    }

    #[test]
    fn int_ops_saturate() {
        let t = IntIval::TOP;
        assert!(!t.add(IntIval::point(1)).is_empty());
        assert!(!t.mul(t).is_empty());
        let a = IntIval::new(-5, 7);
        assert_eq!(a.trem(IntIval::new(3, 3)), IntIval::new(-2, 2));
        assert_eq!(
            IntIval::new(0, 7).trem(IntIval::new(3, 3)),
            IntIval::new(0, 2)
        );
        // Saturated integer endpoints read as unbounded reals, and
        // inward rounding brings them back.
        assert_eq!(IntIval::TOP.to_ival(), Ival::top());
        assert_eq!(ival_to_int(&Ival::top()), IntIval::TOP);
        assert_eq!(
            ival_to_int(&Ival::new(Ext::Fin(dec("0.5")), Ext::Fin(dec("3.5")))),
            IntIval::new(1, 3)
        );
        assert_eq!(
            ival_to_int(&Ival::new(Ext::Fin(dec("-1e50")), Ext::Fin(dec("1e50")))),
            IntIval::TOP
        );
    }

    #[test]
    fn trem_zero_containing_divisor_bounds_nothing() {
        let x = IntIval::new(-100, 100);
        // `x % 0` is an SMT free value; any divisor domain admitting 0
        // must widen to ⊤, not just the exactly-{0} one.
        assert_eq!(x.trem(IntIval::point(0)), IntIval::TOP);
        assert_eq!(x.trem(IntIval::new(0, 5)), IntIval::TOP);
        assert_eq!(x.trem(IntIval::new(-3, 3)), IntIval::TOP);
        // A divisor excluding 0 still bounds.
        assert_eq!(x.trem(IntIval::new(2, 5)), IntIval::new(-4, 4));
    }

    #[test]
    fn tri_logic() {
        use Tri::*;
        assert_eq!(True.and(Both), Both);
        assert_eq!(False.and(Both), False);
        assert_eq!(True.or(Both), True);
        assert_eq!(Both.not(), Both);
        assert_eq!(False.implies(Empty), Empty);
        assert_eq!(True.xor(True), False);
        assert_eq!(Both.intersect(True), True);
        assert_eq!(True.intersect(False), Empty);
    }

    #[test]
    fn enum_sets() {
        let all = EnumSet::all(3);
        let a = EnumSet::point(0);
        let b = EnumSet::point(2);
        assert_eq!(a.eq(&b), Tri::False);
        assert_eq!(a.eq(&a), Tri::True);
        assert_eq!(a.eq(&all), Tri::Both);
        let ab = a.hull(&b);
        assert!(ab.contains(0) && ab.contains(2) && !ab.contains(1));
        assert_eq!(all.minus(&a), EnumSet::point(1).hull(&b));
        assert!(all.minus(&all).is_empty());
    }

    #[test]
    fn enum_sets_are_not_bounded_at_128_literals() {
        // Positions past 128 are distinct members, never aliases of the
        // low positions: literal 129 and literal 1 must not compare
        // equal, and removing one leaves the other.
        let all = EnumSet::all(130);
        assert!(all.contains(0) && all.contains(127) && all.contains(129));
        assert!(!all.contains(130) && !all.contains(64 * 3));
        let hi = EnumSet::point(129);
        let lo = EnumSet::point(1);
        assert_ne!(hi, lo);
        assert_eq!(hi.eq(&lo), Tri::False);
        assert_eq!(hi.eq(&hi), Tri::True);
        assert_eq!(all.intersect(&hi), hi);
        let rest = all.minus(&hi);
        assert!(rest.contains(1) && rest.contains(128) && !rest.contains(129));
        assert!(rest.intersect(&hi).is_empty());
        assert!(!rest.is_point() && all.minus(&rest).is_point());
        // Word-boundary widths.
        assert!(EnumSet::all(64).contains(63) && !EnumSet::all(64).contains(64));
        assert!(EnumSet::all(65).contains(64));
        assert!(EnumSet::all(0).is_empty());
    }

    #[test]
    fn real_literals_are_exact_points() {
        for f in [0.0, 1.0, -2.5, 3.15, 0.001, 1e10, -1e-10, 12345.6789] {
            let r = Rational::from_f64(f).unwrap();
            assert_eq!(
                eval_term(&Term::RealLit(r.clone()), &[]),
                Dom::R(Ival::point(r))
            );
        }
        let tenth = dec("0.1");
        assert_eq!(
            eval_term(&Term::RealLit(tenth.clone()), &[]),
            Dom::R(Ival::point(tenth))
        );
    }

    // -- propagation exactness ---------------------------------------------

    #[test]
    fn literal_bounds_propagate_exactly() {
        // x ≥ 0.8 ∧ x ≤ 1.1 over a real variable: the narrowed domain is
        // spelled exactly as the literals, not as their double
        // neighbours.
        let x = Term::Var(0);
        let facts = vec![
            Term::App(Op::Ge, vec![x.clone(), Term::RealLit(dec("0.8"))]),
            Term::App(Op::Le, vec![x.clone(), Term::RealLit(dec("1.1"))]),
        ];
        let (doms, unsat) = drive(vec![Dom::R(Ival::top())], &facts, 100);
        assert!(!unsat);
        assert_eq!(fmt_dom(&doms[0], &[], false), "[0.8, 1.1]");
        assert_eq!(fmt_dom(&doms[0], &[], true), "[0.8, 1.1]");
        // Bounds derived through arithmetic stay exact too: y = x + 0.2.
        let y = Term::Var(1);
        let facts = vec![
            Term::App(Op::Ge, vec![x.clone(), Term::RealLit(dec("0.8"))]),
            Term::App(Op::Le, vec![x.clone(), Term::RealLit(dec("1.1"))]),
            Term::App(
                Op::Eq,
                vec![
                    y,
                    Term::App(Op::Add, vec![x.clone(), Term::RealLit(dec("0.2"))]),
                ],
            ),
        ];
        let (doms, unsat) = drive(vec![Dom::R(Ival::top()), Dom::R(Ival::top())], &facts, 100);
        assert!(!unsat);
        assert_eq!(fmt_dom(&doms[1], &[], false), "[1, 1.3]");
        // A non-terminating bound prints as a fraction exactly and as a
        // marked decimal for hints.
        let facts = vec![Term::App(
            Op::Ge,
            vec![
                x.clone(),
                Term::App(
                    Op::Div,
                    vec![Term::RealLit(dec("1")), Term::RealLit(dec("3"))],
                ),
            ],
        )];
        let (doms, _) = drive(vec![Dom::R(Ival::top())], &facts, 100);
        assert_eq!(fmt_dom(&doms[0], &[], false), "[1/3, +∞]");
        assert_eq!(fmt_dom(&doms[0], &[], true), "[≈0.3333333333333333, +∞]");
        // Equality against an exact sum is decided exactly: 0.1 + 0.2
        // is 0.3, so demanding both is satisfiable.
        let facts = vec![
            Term::App(
                Op::Eq,
                vec![
                    x.clone(),
                    Term::App(
                        Op::Add,
                        vec![Term::RealLit(dec("0.1")), Term::RealLit(dec("0.2"))],
                    ),
                ],
            ),
            Term::App(Op::Eq, vec![x, Term::RealLit(dec("0.3"))]),
        ];
        let (doms, unsat) = drive(vec![Dom::R(Ival::top())], &facts, 100);
        assert!(!unsat, "{doms:?}");
        assert_eq!(fmt_dom(&doms[0], &[], false), "[0.3, 0.3]");
    }

    #[test]
    fn half_line_tightens_again() {
        // The finite side of a half-line keeps moving: the progress
        // tolerance is scaled from finite endpoints only, so
        // [10, +∞] → [12, +∞] counts as progress (and so does the
        // mirror image on the upper side).
        let x = Term::Var(0);
        let ge = |k: &str| Term::App(Op::Ge, vec![x.clone(), Term::RealLit(dec(k))]);
        let le = |k: &str| Term::App(Op::Le, vec![x.clone(), Term::RealLit(dec(k))]);
        let (doms, unsat) = drive(vec![Dom::R(Ival::top())], &[ge("10"), ge("12")], 100);
        assert!(!unsat);
        assert_eq!(fmt_dom(&doms[0], &[], false), "[12, +∞]");
        let (doms, unsat) = drive(vec![Dom::R(Ival::top())], &[le("10"), le("8")], 100);
        assert!(!unsat);
        assert_eq!(fmt_dom(&doms[0], &[], false), "[−∞, 8]");
        // A large second bound on a half-line already open at zero, then
        // a weaker third one that the tightened domain settles.
        let facts = [ge("0"), ge("1000"), ge("500")];
        let (doms, unsat) = drive(vec![Dom::R(Ival::top())], &facts, 100);
        assert!(!unsat);
        assert_eq!(fmt_dom(&doms[0], &[], false), "[1000, +∞]");
        assert_eq!(eval_term(&facts[2], &doms), Dom::B(Tri::True));
    }

    #[test]
    fn deep_chains_evaluate_each_operand_once() {
        // A left-deep chain of depth 30 (the shape of a `sum` fold or a
        // quantifier expansion) evaluates in linear time; doubling the
        // work per level would take 2^30 operand evaluations.
        let mut chain = Term::Var(0);
        for i in 1..=30 {
            chain = Term::App(Op::Add, vec![chain, Term::Var(i)]);
        }
        let mut doms: Vec<Dom> = (0..=30)
            .map(|i| Dom::R(iv(f64::from(i), f64::from(i) + 1.0)))
            .collect();
        let start = std::time::Instant::now();
        let whole = eval_term(&chain, &doms);
        // Σ [i, i+1] for i in 0..=30.
        assert_eq!(fmt_dom(&whole, &[], false), "[465, 496]");
        doms.push(Dom::R(Ival::top()));
        let facts = vec![Term::App(Op::Eq, vec![Term::Var(31), chain])];
        let (doms, unsat) = drive(doms, &facts, 100);
        assert!(!unsat);
        assert_eq!(fmt_dom(&doms[31], &[], false), "[465, 496]");
        assert!(
            start.elapsed() < std::time::Duration::from_secs(1),
            "deep chain took {:?}",
            start.elapsed()
        );
    }

    #[test]
    fn fixpoint_terminates_on_crawling_contractions() {
        // x = x / 2 contracts by halves forever; the progress epsilon and
        // the pass cap stop it, and the endpoints stay within budget.
        let x = Term::Var(0);
        let facts = vec![
            Term::App(Op::Ge, vec![x.clone(), Term::RealLit(dec("0"))]),
            Term::App(Op::Le, vec![x.clone(), Term::RealLit(dec("1"))]),
            Term::App(
                Op::Eq,
                vec![
                    x.clone(),
                    Term::App(Op::Div, vec![x, Term::RealLit(dec("2"))]),
                ],
            ),
        ];
        let (doms, unsat) = drive(vec![Dom::R(Ival::top())], &facts, 100);
        assert!(!unsat);
        let Dom::R(d) = &doms[0] else {
            panic!("{doms:?}")
        };
        assert!(d.contains_zero());
        if let Ext::Fin(hi) = &d.hi {
            assert!(hi.bits() <= MAX_ENDPOINT_BITS + 64, "{d:?}");
        }
    }

    // -- containment property tests ------------------------------------------
    //
    // The soundness invariant, sampled: for random terms and random
    // points inside random variable intervals, the point evaluation
    // (domains = points) lies inside the interval evaluation.

    /// Deterministic LCG — the crate stays dependency-free.
    struct Lcg(u64);
    impl Lcg {
        fn next(&mut self) -> u64 {
            self.0 = self
                .0
                .wrapping_mul(6364136223846793005)
                .wrapping_add(1442695040888963407);
            self.0 >> 11
        }
        fn f64_in(&mut self, lo: f64, hi: f64) -> f64 {
            lo + (self.next() as f64 / (1u64 << 53) as f64) * (hi - lo)
        }
        fn pick(&mut self, n: usize) -> usize {
            (self.next() % n as u64) as usize
        }
    }

    /// A random numeric term over `nvars` real variables.
    fn random_term(r: &mut Lcg, depth: usize, nvars: usize) -> Term {
        if depth == 0 || r.pick(3) == 0 {
            return match r.pick(2) {
                0 => Term::Var(r.pick(nvars)),
                _ => Term::RealLit(
                    Rational::from_f64((r.f64_in(-8.0, 8.0) * 4.0).round() / 4.0).unwrap(),
                ),
            };
        }
        let op = [Op::Add, Op::Sub, Op::Mul, Op::Div, Op::Neg][r.pick(5)];
        if op == Op::Neg {
            return Term::App(op, vec![random_term(r, depth - 1, nvars)]);
        }
        Term::App(
            op,
            vec![
                random_term(r, depth - 1, nvars),
                random_term(r, depth - 1, nvars),
            ],
        )
    }

    #[test]
    fn containment_random_numeric_terms() {
        let mut r = Lcg(0xC0FFEE);
        for _ in 0..2000 {
            let t = random_term(&mut r, 4, 3);
            // Random variable intervals and a point inside each.
            let mut doms = Vec::new();
            let mut pts = Vec::new();
            for _ in 0..3 {
                let a = r.f64_in(-10.0, 10.0);
                let b = r.f64_in(-10.0, 10.0);
                let (lo, hi) = if a <= b { (a, b) } else { (b, a) };
                doms.push(Dom::R(iv(lo, hi)));
                pts.push(Dom::R(pt(r.f64_in(lo, hi))));
            }
            let whole = eval_term(&t, &doms);
            let point = eval_term(&t, &pts);
            let (Dom::R(w), Dom::R(p)) = (whole, point) else {
                panic!("numeric term evaluated to non-real domains");
            };
            // The point evaluation is itself an interval (division may
            // widen it); containment is interval inclusion.
            assert!(
                w.lo <= p.lo && p.hi <= w.hi,
                "containment violated for {t:?}: point {p:?} not in {w:?}"
            );
        }
    }

    #[test]
    fn containment_comparisons_and_logic() {
        let mut r = Lcg(0xBEEF);
        for _ in 0..2000 {
            let l = random_term(&mut r, 3, 2);
            let rt = random_term(&mut r, 3, 2);
            let cmp = [Op::Lt, Op::Le, Op::Gt, Op::Ge, Op::Eq][r.pick(5)];
            let t = Term::App(cmp, vec![l, rt]);
            let mut doms = Vec::new();
            let mut pts = Vec::new();
            for _ in 0..2 {
                let a = r.f64_in(-6.0, 6.0);
                let b = r.f64_in(-6.0, 6.0);
                let (lo, hi) = if a <= b { (a, b) } else { (b, a) };
                doms.push(Dom::R(iv(lo, hi)));
                pts.push(Dom::R(pt(r.f64_in(lo, hi))));
            }
            let (Dom::B(w), Dom::B(p)) = (eval_term(&t, &doms), eval_term(&t, &pts)) else {
                panic!("comparison evaluated to non-boolean domains");
            };
            // Every verdict the point admits, the whole must admit.
            let ok = (!p.may_true() || w.may_true()) && (!p.may_false() || w.may_false());
            assert!(
                ok,
                "verdict containment violated: point {p:?} vs whole {w:?}"
            );
        }
    }

    /// A quarter-integer in `[−8, 8]`: exact both as a rational and as a
    /// double, so a sampled coordinate is never blurred by conversion.
    fn quarter(r: &mut Lcg) -> Rational {
        Rational::from_f64((r.f64_in(-8.0, 8.0) * 4.0).round() / 4.0).expect("a finite sample")
    }

    #[test]
    fn the_fixpoint_keeps_every_satisfying_point() {
        // The propagation invariant, sampled: the domains the fixpoint
        // derives contain *every* assignment satisfying the facts, so a
        // point known to satisfy them must survive. Narrowing one away
        // would fabricate a refutation — the one way this backend can be
        // unsound. (The other property suites cover the forward pass
        // alone; this one drives the backward pass and the fixpoint.)
        const NVARS: usize = 3;
        let mut r = Lcg(0x05EE_D5A7);
        let mut exercised = 0usize;
        for _ in 0..2000 {
            let point: Vec<Rational> = (0..NVARS).map(|_| quarter(&mut r)).collect();
            let pts: Vec<Dom> = point
                .iter()
                .map(|x| Dom::R(Ival::point(x.clone())))
                .collect();
            // Facts that hold at the sampled point by construction: a
            // bound placed clear of the term's value there. Evaluating at
            // a point may still widen (division), so the bound is taken
            // from the widened end — anything it admits, the true value
            // admits too.
            let mut facts = Vec::new();
            for _ in 0..=r.pick(4) {
                let t = random_term(&mut r, 3, NVARS);
                let Dom::R(at) = eval_term(&t, &pts) else {
                    continue;
                };
                let slack = quarter(&mut r).abs();
                let prefer_lower = r.pick(2) == 0;
                let bound = match (&at.lo, &at.hi) {
                    (Ext::Fin(lo), Ext::Fin(hi)) => {
                        if prefer_lower {
                            Some((Op::Ge, lo.sub(&slack)))
                        } else {
                            Some((Op::Le, hi.add(&slack)))
                        }
                    }
                    (Ext::Fin(lo), _) => Some((Op::Ge, lo.sub(&slack))),
                    (_, Ext::Fin(hi)) => Some((Op::Le, hi.add(&slack))),
                    // The term is unbounded at the point (a division by
                    // zero): no bound can be asserted from it.
                    _ => None,
                };
                if let Some((op, k)) = bound {
                    facts.push(Term::App(op, vec![t, Term::RealLit(k)]));
                }
            }
            if facts.is_empty() {
                continue;
            }
            exercised += 1;
            let init: Vec<Dom> = (0..NVARS).map(|_| Dom::R(Ival::top())).collect();
            let (doms, unsat) = drive(init, &facts, 100);
            assert!(
                !unsat,
                "a system satisfied by {point:?} was refuted: {facts:?}"
            );
            for (i, x) in point.iter().enumerate() {
                let Dom::R(d) = &doms[i] else {
                    panic!("a real variable ended in {:?}", doms[i]);
                };
                assert!(
                    d.contains_rational(x),
                    "{x} was narrowed out of {d:?} by {facts:?}"
                );
            }
        }
        assert!(
            exercised > 1000,
            "too few systems reached the fixpoint: {exercised}"
        );
    }
}
