//! Interval domains and forward evaluation over [`Term`].
//!
//! The propagation backend's value model: every free variable holds a
//! *domain* — a closed real interval, an integer interval, a 3-valued
//! boolean, or an enum-literal set — and terms evaluate to domains that
//! **contain every value the term can take** when each variable ranges
//! over its domain. That containment is the soundness invariant all of
//! interval propagation rests on: real endpoints round *outward* at every inexact
//! operation, integer endpoints saturate, and anything the evaluator
//! cannot bound tightly widens (never narrows).
//!
//! Empty domains are first-class: an empty operand makes every result
//! empty, and (in propagation) a variable contracted to empty proves the
//! asserted constraint set unsatisfiable.

use crate::term::{EnumSort, Op, Sort, Term};

/// Round toward −∞ / +∞ by one ulp — applied to every real endpoint
/// that may have rounded, so intervals only ever widen. A *lower*
/// endpoint that overflowed to `+∞` clamps to `f64::MAX` instead
/// (mirrored in [`up`]): letting the degenerate point `[+∞, +∞]` form
/// would make a later `∞ − ∞` produce NaN — which would read as EMPTY,
/// a fabricated unsat proof. Clamping only ever moves a lower bound
/// down (an upper bound up), so it stays sound.
fn dn(x: f64) -> f64 {
    if x == f64::INFINITY {
        f64::MAX
    } else if x.is_finite() {
        x.next_down()
    } else {
        x
    }
}
fn up(x: f64) -> f64 {
    if x == f64::NEG_INFINITY {
        -f64::MAX
    } else if x.is_finite() {
        x.next_up()
    } else {
        x
    }
}

// ---------------------------------------------------------------- reals

/// A closed real interval `[lo, hi]` (endpoints may be ±∞; never NaN).
/// Empty is canonical `[+∞, −∞]`.
#[derive(Clone, Copy, Debug, PartialEq)]
pub(crate) struct Ival {
    pub lo: f64,
    pub hi: f64,
}

impl Ival {
    pub const TOP: Ival = Ival {
        lo: f64::NEG_INFINITY,
        hi: f64::INFINITY,
    };
    pub const EMPTY: Ival = Ival {
        lo: f64::INFINITY,
        hi: f64::NEG_INFINITY,
    };

    pub fn new(lo: f64, hi: f64) -> Ival {
        if lo.is_nan() || hi.is_nan() {
            // NaN carries no ordering information: the only sound domain
            // is ⊤ — canonicalizing to EMPTY would turn an arithmetic
            // artifact into a false unsat proof.
            return Ival::TOP;
        }
        if lo <= hi {
            Ival { lo, hi }
        } else {
            Ival::EMPTY
        }
    }

    pub fn point(x: f64) -> Ival {
        Ival::new(x, x)
    }

    pub fn is_empty(self) -> bool {
        self.lo > self.hi
    }

    pub fn contains(self, x: f64) -> bool {
        self.lo <= x && x <= self.hi
    }

    pub fn intersect(self, o: Ival) -> Ival {
        Ival::new(self.lo.max(o.lo), self.hi.min(o.hi))
    }

    pub fn hull(self, o: Ival) -> Ival {
        if self.is_empty() {
            return o;
        }
        if o.is_empty() {
            return self;
        }
        Ival::new(self.lo.min(o.lo), self.hi.max(o.hi))
    }

    pub fn add(self, o: Ival) -> Ival {
        if self.is_empty() || o.is_empty() {
            return Ival::EMPTY;
        }
        Ival::new(dn(self.lo + o.lo), up(self.hi + o.hi))
    }

    pub fn sub(self, o: Ival) -> Ival {
        if self.is_empty() || o.is_empty() {
            return Ival::EMPTY;
        }
        Ival::new(dn(self.lo - o.hi), up(self.hi - o.lo))
    }

    pub fn neg(self) -> Ival {
        if self.is_empty() {
            return Ival::EMPTY;
        }
        Ival::new(-self.hi, -self.lo)
    }

    pub fn mul(self, o: Ival) -> Ival {
        if self.is_empty() || o.is_empty() {
            return Ival::EMPTY;
        }
        // min/max over the four endpoint products, each rounded outward
        // individually. `0 × ∞` reads as an exact 0 (the finite factor
        // is exactly zero, so every product is zero) — and a zero
        // product from a zero factor stays exact, so multiplying by a
        // literal 0 keeps a point interval.
        let pd = |a: f64, b: f64| {
            if a == 0.0 || b == 0.0 { 0.0 } else { dn(a * b) }
        };
        let pu = |a: f64, b: f64| {
            if a == 0.0 || b == 0.0 { 0.0 } else { up(a * b) }
        };
        let lo = [
            pd(self.lo, o.lo),
            pd(self.lo, o.hi),
            pd(self.hi, o.lo),
            pd(self.hi, o.hi),
        ]
        .into_iter()
        .fold(f64::INFINITY, f64::min);
        let hi = [
            pu(self.lo, o.lo),
            pu(self.lo, o.hi),
            pu(self.hi, o.lo),
            pu(self.hi, o.hi),
        ]
        .into_iter()
        .fold(f64::NEG_INFINITY, f64::max);
        Ival::new(lo, hi)
    }

    /// Real division. A divisor interval containing 0 widens to the hull
    /// of the two half-line quotients (possibly all of ℝ) — sound, never
    /// empty-by-accident.
    pub fn div(self, o: Ival) -> Ival {
        if self.is_empty() || o.is_empty() {
            return Ival::EMPTY;
        }
        if o.lo > 0.0 || o.hi < 0.0 {
            // Endpoint quotients rounded outward individually; an
            // exactly-zero dividend endpoint (or an infinite divisor)
            // gives an exact 0.
            let qd = |a: f64, b: f64| {
                if a == 0.0 || b.is_infinite() {
                    0.0
                } else {
                    dn(a / b)
                }
            };
            let qu = |a: f64, b: f64| {
                if a == 0.0 || b.is_infinite() {
                    0.0
                } else {
                    up(a / b)
                }
            };
            let lo = [
                qd(self.lo, o.lo),
                qd(self.lo, o.hi),
                qd(self.hi, o.lo),
                qd(self.hi, o.hi),
            ]
            .into_iter()
            .fold(f64::INFINITY, f64::min);
            let hi = [
                qu(self.lo, o.lo),
                qu(self.lo, o.hi),
                qu(self.hi, o.lo),
                qu(self.hi, o.hi),
            ]
            .into_iter()
            .fold(f64::NEG_INFINITY, f64::max);
            return Ival::new(lo, hi);
        }
        if self.contains(0.0) || (o.lo == 0.0 && o.hi == 0.0) {
            // 0/0 possible, or divisor is exactly {0}: no information
            // (SMT total division makes x/0 an unconstrained value).
            return Ival::TOP;
        }
        // Divisor straddles 0: hull of the strictly-positive and
        // strictly-negative parts — unbounded on both sides.
        Ival::TOP
    }

    // Certainly-true / certainly-false comparisons.
    pub fn lt(self, o: Ival) -> Tri {
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

    pub fn le(self, o: Ival) -> Tri {
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

    pub fn eq(self, o: Ival) -> Tri {
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
/// `[MAX, MIN]`.
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

    /// The enclosing real interval. A small integer (`|i| < 2^53`) casts to
    /// `f64` exactly and its endpoint stays sharp — the common case of a
    /// literal bound like `10`; only a cast that actually loses precision
    /// rounds outward, keeping the enclosure sound.
    pub fn to_ival(self) -> Ival {
        if self.is_empty() {
            return Ival::EMPTY;
        }
        let round_out = |i: i128, out: fn(f64) -> f64| {
            let f = i as f64;
            if f as i128 == i { f } else { out(f) }
        };
        Ival::new(round_out(self.lo, dn), round_out(self.hi, up))
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

/// A set of enum-literal positions (bitset; enum sorts are small).
#[derive(Clone, Copy, Debug, PartialEq)]
pub(crate) struct EnumSet {
    pub bits: u128,
}

impl EnumSet {
    /// All `n` literals. Sorts wider than 128 literals do not occur (the
    /// translator interns real model enums); saturate to full-set = ⊤.
    pub fn all(n: usize) -> EnumSet {
        if n >= 128 {
            EnumSet { bits: u128::MAX }
        } else {
            EnumSet {
                bits: (1u128 << n) - 1,
            }
        }
    }

    pub fn point(i: usize) -> EnumSet {
        EnumSet {
            bits: 1u128 << (i % 128),
        }
    }

    pub fn is_empty(self) -> bool {
        self.bits == 0
    }

    pub fn contains(self, i: usize) -> bool {
        i < 128 && self.bits & (1u128 << i) != 0
    }

    pub fn intersect(self, o: EnumSet) -> EnumSet {
        EnumSet {
            bits: self.bits & o.bits,
        }
    }

    pub fn hull(self, o: EnumSet) -> EnumSet {
        EnumSet {
            bits: self.bits | o.bits,
        }
    }

    pub fn is_point(self) -> bool {
        self.bits.count_ones() == 1
    }

    pub fn eq(self, o: EnumSet) -> Tri {
        if self.is_empty() || o.is_empty() {
            return Tri::Empty;
        }
        if self.intersect(o).is_empty() {
            Tri::False
        } else if self.is_point() && o.is_point() && self.bits == o.bits {
            Tri::True
        } else {
            Tri::Both
        }
    }
}

// -------------------------------------------------------------- domains

/// The domain of a term or variable. `Str` is opaque: string variables
/// carry no interval structure, so every string fact stays `Both`.
#[derive(Clone, Copy, Debug, PartialEq)]
pub(crate) enum Dom {
    R(Ival),
    I(IntIval),
    B(Tri),
    /// Enum sort index (into the translation's enum table) + literal set.
    E(usize, EnumSet),
    Str,
}

impl Dom {
    pub fn is_empty(self) -> bool {
        match self {
            Dom::R(v) => v.is_empty(),
            Dom::I(v) => v.is_empty(),
            Dom::B(v) => v.is_empty(),
            Dom::E(_, v) => v.is_empty(),
            Dom::Str => false,
        }
    }

    /// The enclosing real interval of a numeric domain.
    fn as_ival(self) -> Option<Ival> {
        match self {
            Dom::R(v) => Some(v),
            Dom::I(v) => Some(v.to_ival()),
            _ => None,
        }
    }

    fn as_tri(self) -> Option<Tri> {
        match self {
            Dom::B(t) => Some(t),
            _ => None,
        }
    }

    pub fn hull(self, o: Dom) -> Dom {
        match (self, o) {
            (Dom::R(a), Dom::R(b)) => Dom::R(a.hull(b)),
            (Dom::I(a), Dom::I(b)) => Dom::I(a.hull(b)),
            (Dom::B(a), Dom::B(b)) => Dom::B(a.hull(b)),
            (Dom::E(s, a), Dom::E(t, b)) if s == t => Dom::E(s, a.hull(b)),
            (Dom::Str, Dom::Str) => Dom::Str,
            // Mixed numeric kinds hull as reals; anything else has no
            // common structure — ⊤ of the real line is the widest thing
            // we can say (such terms are sort errors upstream anyway).
            (a, b) => match (a.as_ival(), b.as_ival()) {
                (Some(x), Some(y)) => Dom::R(x.hull(y)),
                _ => Dom::R(Ival::TOP),
            },
        }
    }
}

/// Parse a [`Term::RealLit`] rendering back to its value. The renderer
/// (`real_from_f64`) writes the f64's exact binary expansion — `num.0`,
/// `(/ num.0 den.0)` with `den` a power of two, possibly inside
/// `(- …)` — so numerator and denominator are exact in f64 and the
/// division reproduces the original value exactly.
fn real_lit(s: &str) -> Option<f64> {
    let s = s.trim();
    if let Some(body) = s.strip_prefix("(- ").and_then(|r| r.strip_suffix(')')) {
        return real_lit(body).map(|v| -v);
    }
    if let Some(body) = s.strip_prefix("(/ ").and_then(|r| r.strip_suffix(')')) {
        let (n, d) = body.split_once(' ')?;
        return Some(n.trim().parse::<f64>().ok()? / d.trim().parse::<f64>().ok()?);
    }
    s.parse::<f64>().ok()
}

/// Forward (bottom-up) evaluation of a term over variable domains: the
/// result contains every value the term can take with each variable in
/// its domain. Unknown shapes widen to ⊤ of their kind — never narrow.
pub(crate) fn eval_term(t: &Term, doms: &[Dom]) -> Dom {
    match t {
        Term::BoolLit(b) => Dom::B(Tri::point(*b)),
        Term::IntLit(i) => Dom::I(IntIval::point(*i)),
        Term::RealLit(s) => match real_lit(s) {
            Some(v) => Dom::R(Ival::point(v)),
            None => Dom::R(Ival::TOP),
        },
        Term::StrLit(_) => Dom::Str,
        Term::Var(i) => doms[*i],
        Term::EnumLit(sort, pos) => Dom::E(*sort, EnumSet::point(*pos)),
        Term::App(op, args) => {
            if let Some(d) = args
                .iter()
                .map(|a| eval_term(a, doms))
                .find(|d| d.is_empty())
            {
                // An empty operand poisons the whole application; keep
                // the kind of the first empty operand — callers only ask
                // `is_empty`.
                return d;
            }
            let a = |i: usize| eval_term(&args[i], doms);
            let tri = |d: Dom| d.as_tri().unwrap_or(Tri::Both);
            let num = |d: Dom| d.as_ival().unwrap_or(Ival::TOP);
            match op {
                Op::Not => Dom::B(tri(a(0)).not()),
                Op::And => Dom::B(tri(a(0)).and(tri(a(1)))),
                Op::Or => Dom::B(tri(a(0)).or(tri(a(1)))),
                Op::Xor => Dom::B(tri(a(0)).xor(tri(a(1)))),
                Op::Implies => Dom::B(tri(a(0)).implies(tri(a(1)))),
                Op::Eq => Dom::B(match (a(0), a(1)) {
                    (Dom::B(x), Dom::B(y)) => x.eq(y),
                    (Dom::E(s, x), Dom::E(t, y)) if s == t => x.eq(y),
                    (Dom::Str, _) | (_, Dom::Str) => Tri::Both,
                    (x, y) => match (x.as_ival(), y.as_ival()) {
                        (Some(u), Some(v)) => u.eq(v),
                        _ => Tri::Both,
                    },
                }),
                Op::Lt => Dom::B(num(a(0)).lt(num(a(1)))),
                Op::Le => Dom::B(num(a(0)).le(num(a(1)))),
                Op::Gt => Dom::B(num(a(1)).lt(num(a(0)))),
                Op::Ge => Dom::B(num(a(1)).le(num(a(0)))),
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
                            Op::Add => u.add(v),
                            Op::Sub => u.sub(v),
                            _ => u.mul(v),
                        })
                    }
                },
                // SMT division is always real-valued (operands coerced).
                Op::Div => Dom::R(num(a(0)).div(num(a(1)))),
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

/// The largest real interval enclosing an integer domain: endpoints of a
/// real interval rounded *inward* to integers (`ceil`/`floor`, saturating
/// — an infinite endpoint stays saturated, never NaN).
fn ival_to_int(w: Ival) -> IntIval {
    if w.is_empty() {
        return IntIval::EMPTY;
    }
    // f64 → i128 `as` saturates (and maps ±∞ to MIN/MAX), so ceil/floor of
    // an infinite endpoint lands on the saturated integer.
    IntIval::new(w.lo.ceil() as i128, w.hi.floor() as i128)
}

impl Dom {
    /// Intersect this domain with a demanded (`want`) domain of the same or
    /// a compatible numeric kind. A real want against an integer domain
    /// rounds inward; a kind mismatch (a sort error upstream) narrows
    /// nothing — the result is always a *subset* of `self`, so applying it
    /// can only tighten.
    pub(crate) fn narrow(self, want: Dom) -> Dom {
        match self {
            Dom::R(a) => match want.as_ival() {
                Some(w) => Dom::R(a.intersect(w)),
                None => self,
            },
            Dom::I(a) => match want {
                Dom::I(w) => Dom::I(a.intersect(w)),
                Dom::R(w) => Dom::I(a.intersect(ival_to_int(w))),
                _ => self,
            },
            Dom::B(a) => match want {
                Dom::B(w) => Dom::B(a.intersect(w)),
                _ => self,
            },
            Dom::E(s, a) => match want {
                Dom::E(t, w) if t == s => Dom::E(s, a.intersect(w)),
                _ => self,
            },
            Dom::Str => self,
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

fn as_ival_or_top(d: Dom) -> Ival {
    d.as_ival().unwrap_or(Ival::TOP)
}

fn as_tri_or_both(d: Dom) -> Tri {
    d.as_tri().unwrap_or(Tri::Both)
}

/// Is `new` (a subset of `old`) tighter than `old` by enough to be worth
/// applying? Discrete domains progress in finite steps, so any change
/// counts; real endpoints must move by more than a relative epsilon, which
/// (with the driver's iteration cap) guarantees the fixpoint terminates
/// rather than crawling by ulps forever.
fn meaningful(old: Dom, new: Dom, eps: f64) -> bool {
    match (old, new) {
        (Dom::R(a), Dom::R(b)) => {
            let scale = 1.0 + a.lo.abs().min(f64::MAX).max(a.hi.abs().min(f64::MAX));
            let tol = eps * scale;
            (b.lo - a.lo) > tol || (a.hi - b.hi) > tol
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
            let old = doms[*i];
            let new = old.narrow(want);
            if new == old {
                Refine::Unchanged
            } else if new.is_empty() {
                doms[*i] = new;
                Refine::Bottom
            } else if meaningful(old, new, eps) {
                doms[*i] = new;
                Refine::Changed
            } else {
                Refine::Unchanged
            }
        }
        Term::BoolLit(b) => {
            let t = as_tri_or_both(want);
            let ok = if *b { t.may_true() } else { t.may_false() };
            if ok {
                Refine::Unchanged
            } else {
                Refine::Bottom
            }
        }
        Term::IntLit(i) => {
            // Against an integer demand the check is exact; otherwise fall
            // back to the enclosing real interval.
            let ok = match want {
                Dom::I(iv) => iv.contains(*i),
                _ => as_ival_or_top(want).contains(*i as f64),
            };
            if ok {
                Refine::Unchanged
            } else {
                Refine::Bottom
            }
        }
        Term::RealLit(s) => match real_lit(s) {
            Some(v) if !as_ival_or_top(want).contains(v) => Refine::Bottom,
            _ => Refine::Unchanged,
        },
        Term::EnumLit(s, pos) => match want {
            Dom::E(t, set) if t == *s && !set.contains(*pos) => Refine::Bottom,
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
        Op::Not => refine_term(a0, Dom::B(as_tri_or_both(want).not()), doms, eps),
        Op::And => match as_tri_or_both(want) {
            Tri::True => meet(
                refine_term(a0, Dom::B(Tri::True), doms, eps),
                refine_term(&args[1], Dom::B(Tri::True), doms, eps),
            ),
            Tri::False => {
                // The conjunction is false: whichever operand is pinned
                // true forces the other false.
                let f0 = as_tri_or_both(eval_term(a0, doms));
                let f1 = as_tri_or_both(eval_term(&args[1], doms));
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
        Op::Or => match as_tri_or_both(want) {
            Tri::False => meet(
                refine_term(a0, Dom::B(Tri::False), doms, eps),
                refine_term(&args[1], Dom::B(Tri::False), doms, eps),
            ),
            Tri::True => {
                let f0 = as_tri_or_both(eval_term(a0, doms));
                let f1 = as_tri_or_both(eval_term(&args[1], doms));
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
        Op::Implies => match as_tri_or_both(want) {
            Tri::True => {
                let f0 = as_tri_or_both(eval_term(a0, doms));
                let f1 = as_tri_or_both(eval_term(&args[1], doms));
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
            let want_diff = match as_tri_or_both(want) {
                Tri::True => true,
                Tri::False => false,
                _ => return Refine::Unchanged,
            };
            let f0 = as_tri_or_both(eval_term(a0, doms));
            let f1 = as_tri_or_both(eval_term(&args[1], doms));
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
        Op::Eq => match as_tri_or_both(want) {
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
                if let Some(w) = exclude(c1) {
                    acc = meet(acc, refine_term(a0, w, doms, eps));
                }
                if let Some(w) = exclude(c0) {
                    acc = meet(acc, refine_term(&args[1], w, doms, eps));
                }
                acc
            }
            _ => Refine::Unchanged,
        },
        Op::Lt | Op::Le => {
            let x = as_ival_or_top(eval_term(a0, doms));
            let y = as_ival_or_top(eval_term(&args[1], doms));
            match as_tri_or_both(want) {
                // x ≤ y: closed-interval bounds over-approximate `<`.
                Tri::True => meet(
                    refine_term(a0, Dom::R(Ival::new(f64::NEG_INFINITY, y.hi)), doms, eps),
                    refine_term(&args[1], Dom::R(Ival::new(x.lo, f64::INFINITY)), doms, eps),
                ),
                // ¬(x < y) ⟺ x ≥ y.
                Tri::False => meet(
                    refine_term(a0, Dom::R(Ival::new(y.lo, f64::INFINITY)), doms, eps),
                    refine_term(
                        &args[1],
                        Dom::R(Ival::new(f64::NEG_INFINITY, x.hi)),
                        doms,
                        eps,
                    ),
                ),
                _ => Refine::Unchanged,
            }
        }
        Op::Gt | Op::Ge => {
            let x = as_ival_or_top(eval_term(a0, doms));
            let y = as_ival_or_top(eval_term(&args[1], doms));
            match as_tri_or_both(want) {
                Tri::True => meet(
                    refine_term(a0, Dom::R(Ival::new(y.lo, f64::INFINITY)), doms, eps),
                    refine_term(
                        &args[1],
                        Dom::R(Ival::new(f64::NEG_INFINITY, x.hi)),
                        doms,
                        eps,
                    ),
                ),
                Tri::False => meet(
                    refine_term(a0, Dom::R(Ival::new(f64::NEG_INFINITY, y.hi)), doms, eps),
                    refine_term(&args[1], Dom::R(Ival::new(x.lo, f64::INFINITY)), doms, eps),
                ),
                _ => Refine::Unchanged,
            }
        }
        // z = x + y  ⟹  x ∈ z − y,  y ∈ z − x.
        Op::Add => {
            let w = as_ival_or_top(want);
            let x = as_ival_or_top(eval_term(a0, doms));
            let y = as_ival_or_top(eval_term(&args[1], doms));
            meet(
                refine_term(a0, Dom::R(w.sub(y)), doms, eps),
                refine_term(&args[1], Dom::R(w.sub(x)), doms, eps),
            )
        }
        // z = x − y  ⟹  x ∈ z + y,  y ∈ x − z.
        Op::Sub => {
            let w = as_ival_or_top(want);
            let x = as_ival_or_top(eval_term(a0, doms));
            let y = as_ival_or_top(eval_term(&args[1], doms));
            meet(
                refine_term(a0, Dom::R(w.add(y)), doms, eps),
                refine_term(&args[1], Dom::R(x.sub(w)), doms, eps),
            )
        }
        // z = x·y  ⟹  x ∈ z/y,  y ∈ z/x  (division through zero widens to
        // ⊤, so it never over-narrows).
        Op::Mul => {
            let w = as_ival_or_top(want);
            let x = as_ival_or_top(eval_term(a0, doms));
            let y = as_ival_or_top(eval_term(&args[1], doms));
            meet(
                refine_term(a0, Dom::R(w.div(y)), doms, eps),
                refine_term(&args[1], Dom::R(w.div(x)), doms, eps),
            )
        }
        // z = x/y  ⟹  x ∈ z·y,  y ∈ x/z — but only where the divisor
        // is nonzero. SMT division is total: `x/0` is a free value that
        // can lie in any `want`, so a divisor domain containing 0
        // constrains neither the dividend (skip its contraction) nor its
        // own zero (keep 0 in the demand) — the forward pass's widening,
        // mirrored.
        Op::Div => {
            let w = as_ival_or_top(want);
            let x = as_ival_or_top(eval_term(a0, doms));
            let y = as_ival_or_top(eval_term(&args[1], doms));
            let acc = if y.contains(0.0) {
                Refine::Unchanged
            } else {
                refine_term(a0, Dom::R(w.mul(y)), doms, eps)
            };
            let yd = if y.contains(0.0) {
                x.div(w).hull(Ival::point(0.0))
            } else {
                x.div(w)
            };
            meet(acc, refine_term(&args[1], Dom::R(yd), doms, eps))
        }
        Op::Neg => refine_term(a0, Dom::R(as_ival_or_top(want).neg()), doms, eps),
        // No useful inverse for truncated remainder.
        Op::TRem => Refine::Unchanged,
        Op::Ite => match as_tri_or_both(eval_term(a0, doms)) {
            Tri::Empty => Refine::Bottom,
            Tri::True => refine_term(&args[1], want, doms, eps),
            Tri::False => refine_term(&args[2], want, doms, eps),
            Tri::Both => {
                // The condition is undecided: if a branch cannot meet
                // `want`, the condition must select the other.
                let then_ok = !eval_term(&args[1], doms).narrow(want).is_empty();
                let else_ok = !eval_term(&args[2], doms).narrow(want).is_empty();
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
/// side is a definite point: the negation of a boolean, or an enum with
/// exactly that one literal removed. Numeric point-exclusion has no
/// interval representation, so it returns `None` (no contraction).
fn exclude(known: Dom) -> Option<Dom> {
    match known {
        Dom::B(Tri::True) => Some(Dom::B(Tri::False)),
        Dom::B(Tri::False) => Some(Dom::B(Tri::True)),
        Dom::E(s, set) if set.is_point() => Some(Dom::E(s, EnumSet { bits: !set.bits })),
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
        Sort::Real => Dom::R(Ival::TOP),
        Sort::Str => Dom::Str,
        Sort::Enum(i) => Dom::E(i, EnumSet::all(enum_sizes[i])),
    }
}

fn fmt_f(x: f64) -> String {
    if x == f64::INFINITY {
        "+∞".into()
    } else if x == f64::NEG_INFINITY {
        "−∞".into()
    } else {
        format!("{x}")
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

/// Render a domain as a half-open/closed range or set, for `--ranges`
/// output. Enum literals use their model-facing names.
pub(crate) fn fmt_dom(d: Dom, enums: &[EnumSort]) -> String {
    match d {
        Dom::R(v) if v.is_empty() => "∅".into(),
        Dom::R(v) => format!("[{}, {}]", fmt_f(v.lo), fmt_f(v.hi)),
        Dom::I(v) if v.is_empty() => "∅".into(),
        Dom::I(v) => format!("[{}, {}]", fmt_i(v.lo), fmt_i(v.hi)),
        Dom::B(Tri::True) => "{true}".into(),
        Dom::B(Tri::False) => "{false}".into(),
        Dom::B(Tri::Both) => "{true, false}".into(),
        Dom::B(Tri::Empty) => "∅".into(),
        Dom::E(_, set) if set.is_empty() => "∅".into(),
        Dom::E(s, set) => {
            let names: Vec<&str> = enums[s]
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

    // -- interval arithmetic ------------------------------------------------

    #[test]
    fn real_ops_basics() {
        let a = Ival::new(1.0, 2.0);
        let b = Ival::new(-3.0, 4.0);
        assert!(a.add(b).contains(-2.0) && a.add(b).contains(6.0));
        assert!(a.sub(b).contains(-3.0) && a.sub(b).contains(5.0));
        assert!(a.mul(b).contains(-6.0) && a.mul(b).contains(8.0));
        assert_eq!(Ival::EMPTY.add(a), Ival::EMPTY);
        assert!(a.div(Ival::point(0.0)) == Ival::TOP);
        assert!(b.div(a).contains(4.0) && b.div(a).contains(-3.0));
        // Divisor straddling zero widens to ⊤, never errs.
        assert_eq!(a.div(b), Ival::TOP);
    }

    #[test]
    fn zero_times_unbounded_is_zero() {
        assert_eq!(Ival::point(0.0).mul(Ival::TOP), Ival::point(0.0));
    }

    #[test]
    fn comparisons_certainty() {
        let a = Ival::new(1.0, 2.0);
        let b = Ival::new(3.0, 4.0);
        assert_eq!(a.lt(b), Tri::True);
        assert_eq!(b.lt(a), Tri::False);
        assert_eq!(a.lt(Ival::new(1.5, 5.0)), Tri::Both);
        assert_eq!(a.le(Ival::new(2.0, 5.0)), Tri::True);
        assert_eq!(Ival::point(2.0).eq(Ival::point(2.0)), Tri::True);
        assert_eq!(a.eq(b), Tri::False);
        assert_eq!(a.eq(Ival::new(2.0, 3.0)), Tri::Both);
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
    fn overflow_clamps_instead_of_fabricating_empty() {
        // An overflowed lower endpoint clamps to MAX rather than minting
        // the degenerate point [+∞, +∞]…
        let big = Ival::new(1e308, f64::INFINITY);
        let s = big.add(big);
        assert!(s.lo.is_finite() && s.hi == f64::INFINITY, "{s:?}");
        // …so ∞ − ∞ (NaN → EMPTY, a false unsat proof) can't arise.
        let d = s.sub(s);
        assert!(!d.is_empty() && d.contains(0.0), "{d:?}");
        // Same through multiplication overflow.
        let p = Ival::point(1e200).mul(Ival::point(1e200));
        assert!(p.lo.is_finite() && p.hi == f64::INFINITY, "{p:?}");
        // And NaN reaching the constructor widens instead of emptying.
        assert_eq!(Ival::new(f64::NAN, f64::NAN), Ival::TOP);
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
        assert_eq!(a.eq(b), Tri::False);
        assert_eq!(a.eq(a), Tri::True);
        assert_eq!(a.eq(all), Tri::Both);
        assert!(a.hull(b).contains(0) && a.hull(b).contains(2) && !a.hull(b).contains(1));
    }

    #[test]
    fn real_lit_round_trip() {
        for f in [0.0, 1.0, -2.5, 3.15, 0.001, 1e10, -1e-10, 12345.6789] {
            let s = crate::term::real_from_f64(f).unwrap();
            assert_eq!(real_lit(&s), Some(f), "{s}");
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
                    crate::term::real_from_f64((r.f64_in(-8.0, 8.0) * 4.0).round() / 4.0).unwrap(),
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
                doms.push(Dom::R(Ival::new(lo, hi)));
                pts.push(Dom::R(Ival::point(r.f64_in(lo, hi))));
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
                doms.push(Dom::R(Ival::new(lo, hi)));
                pts.push(Dom::R(Ival::point(r.f64_in(lo, hi))));
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
}
