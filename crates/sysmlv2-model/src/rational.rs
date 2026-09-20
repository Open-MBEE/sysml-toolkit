//! Exact rational numbers for expression evaluation.
//!
//! A [`Rational`] is a fraction in lowest terms with a positive
//! denominator. Values whose numerator and denominator fit 128 bits stay
//! inline; an operation that overflows moves to heap-allocated big
//! integers, and a result that fits again returns inline. Every
//! arithmetic result is exact regardless of magnitude, so `0.1 + 0.2` is
//! `3/10` and `100 * 1.1` is `110`.
//!
//! Text forms: a terminating decimal prints exactly (`0.3`, `110`);
//! anything else prints as a reduced fraction (`1/3`). Both spellings are
//! valid KerML expressions.

use std::cmp::Ordering;
use std::fmt;
use std::hash::{Hash, Hasher};

use num_bigint::BigInt;
use num_integer::Integer as _;
use num_rational::{BigRational, Ratio};
use num_traits::{CheckedAdd, CheckedDiv, CheckedMul, CheckedSub, One, Signed, ToPrimitive, Zero};

type Small = Ratio<i128>;

/// An exact rational number in lowest terms.
#[derive(Clone)]
pub struct Rational(Repr);

#[derive(Clone)]
enum Repr {
    /// Reduced, positive denominator, neither component `i128::MIN`.
    Small(Small),
    /// Reduced, positive denominator, does not fit [`Repr::Small`].
    Big(Box<BigRational>),
}

/// The largest bit size a power may produce, and the size beyond which
/// the evaluator refuses an exact result: about 315,000 decimal digits.
/// Past it a power reports `None` and callers degrade to an approximate
/// result instead of allocating without bound.
pub const MAX_BITS: u64 = 1 << 20;
/// Largest exponent magnitude accepted by [`Rational::parse_decimal`].
const MAX_DECIMAL_EXPONENT: i64 = 100_000;

fn fits_small(n: i128, d: i128) -> bool {
    n != i128::MIN && d != i128::MIN
}

impl Rational {
    /// The integer `i` as a rational.
    #[must_use]
    pub fn from_integer(i: i128) -> Rational {
        if i == i128::MIN {
            return Self::from_big(BigRational::from_integer(BigInt::from(i)));
        }
        Rational(Repr::Small(Small::new_raw(i, 1)))
    }

    /// `num / den`, reduced; `None` when `den` is zero.
    #[must_use]
    pub fn new(num: i128, den: i128) -> Option<Rational> {
        if den == 0 {
            return None;
        }
        if !fits_small(num, den) {
            return Some(Self::from_big(BigRational::new(num.into(), den.into())));
        }
        Some(Self::small(Small::new(num, den)))
    }

    /// Zero.
    #[must_use]
    pub fn zero() -> Rational {
        Self::from_integer(0)
    }

    /// One.
    #[must_use]
    pub fn one() -> Rational {
        Self::from_integer(1)
    }

    fn small(r: Small) -> Rational {
        if fits_small(*r.numer(), *r.denom()) {
            Rational(Repr::Small(r))
        } else {
            Self::from_big(BigRational::new_raw(
                BigInt::from(*r.numer()),
                BigInt::from(*r.denom()),
            ))
        }
    }

    /// A reduced big rational, demoted to the inline form when it fits.
    fn from_big(b: BigRational) -> Rational {
        if let (Some(n), Some(d)) = (b.numer().to_i128(), b.denom().to_i128()) {
            if fits_small(n, d) {
                return Rational(Repr::Small(Small::new_raw(n, d)));
            }
        }
        Rational(Repr::Big(Box::new(b)))
    }

    /// The exact big-integer form of an integer.
    #[must_use]
    pub fn from_bigint(i: BigInt) -> Rational {
        Self::from_big(BigRational::from_integer(i))
    }

    fn to_big(&self) -> BigRational {
        match &self.0 {
            Repr::Small(r) => {
                BigRational::new_raw(BigInt::from(*r.numer()), BigInt::from(*r.denom()))
            }
            Repr::Big(b) => (**b).clone(),
        }
    }

    /// Parse a decimal spelling exactly: an optional sign, digits with an
    /// optional fraction (`12`, `1.5`, `.5`, `5.`), and an optional
    /// decimal exponent (`1e-3`, `2.957353E-05`). No intermediate
    /// double is involved. `None` for any other text, and for exponents
    /// whose magnitude exceeds 100000.
    #[must_use]
    pub fn parse_decimal(s: &str) -> Option<Rational> {
        let s = s.trim();
        let (neg, s) = match s.strip_prefix('-') {
            Some(rest) => (true, rest),
            None => (false, s.strip_prefix('+').unwrap_or(s)),
        };
        let (mantissa, exp) = match s.find(['e', 'E']) {
            Some(i) => (&s[..i], s[i + 1..].parse::<i64>().ok()?),
            None => (s, 0i64),
        };
        let (int_part, frac_part) = match mantissa.split_once('.') {
            Some((a, b)) => (a, b),
            None => (mantissa, ""),
        };
        if int_part.is_empty() && frac_part.is_empty() {
            return None;
        }
        if !int_part.bytes().all(|b| b.is_ascii_digit())
            || !frac_part.bytes().all(|b| b.is_ascii_digit())
        {
            return None;
        }
        let scale = exp.checked_sub(frac_part.len() as i64)?;
        if scale.abs() > MAX_DECIMAL_EXPONENT {
            return None;
        }
        let mut digits = String::with_capacity(int_part.len() + frac_part.len());
        digits.push_str(int_part);
        digits.push_str(frac_part);
        let digits = digits.trim_start_matches('0');
        if digits.is_empty() {
            return Some(Rational::zero());
        }
        // Inline fast path: up to 38 significant digits and a power of
        // ten that fits `i128` (10^38 does).
        if digits.len() <= 38 && scale.unsigned_abs() <= 38 {
            if let Ok(m) = digits.parse::<i128>() {
                let p = 10i128.pow(scale.unsigned_abs() as u32);
                let r = if scale >= 0 {
                    m.checked_mul(p).map(|n| Small::new_raw(n, 1))
                } else {
                    Some(Small::new(m, p))
                };
                if let Some(r) = r {
                    let r = Self::small(r);
                    return Some(if neg { r.neg() } else { r });
                }
            }
        }
        let m = BigInt::parse_bytes(digits.as_bytes(), 10)?;
        let p = BigInt::from(10u32).pow(scale.unsigned_abs() as u32);
        let b = if scale >= 0 {
            BigRational::from_integer(m * p)
        } else {
            BigRational::new(m, p)
        };
        let r = Self::from_big(b);
        Some(if neg { r.neg() } else { r })
    }

    /// Parse either spelling this type prints: a decimal (`0.3`, `110`,
    /// `2.957353E-05`) or a fraction of two decimals (`1/3`, `-500000/3183`).
    /// `None` for any other text or a zero denominator. The inverse of
    /// [`fmt::Display`], so a printed value reads back exactly.
    #[must_use]
    pub fn parse(s: &str) -> Option<Rational> {
        match s.trim().split_once('/') {
            None => Self::parse_decimal(s),
            Some((n, d)) => Self::parse_decimal(n)?.div(&Self::parse_decimal(d)?),
        }
    }

    /// `self ** k`, exact when the result is representable, otherwise the
    /// exact value of the nearest double power, and one only when even
    /// that is not finite. For unit scales, which must always compose.
    #[must_use]
    pub fn pow_or_approx(&self, k: i32) -> Rational {
        self.pow(k)
            .or_else(|| Rational::from_f64(self.to_f64().powi(k)))
            .unwrap_or_else(Rational::one)
    }

    /// `self ** (p/q)`: exact when the root exists, otherwise the exact
    /// value of the nearest double power, and one only when even that is
    /// not finite. For unit scales, which must always compose.
    #[must_use]
    pub fn pow_ratio_or_approx(&self, (p, q): (i32, i32)) -> Rational {
        Rational::new(p as i128, q as i128)
            .and_then(|e| self.pow_rational(&e))
            .or_else(|| Rational::from_f64(self.to_f64().powf(p as f64 / q as f64)))
            .unwrap_or_else(Rational::one)
    }

    /// The exact value of a finite double (every finite double is a
    /// dyadic rational); `None` for infinities and NaN.
    pub fn from_f64(f: f64) -> Option<Rational> {
        if !f.is_finite() {
            return None;
        }
        // Fast path: integral doubles of moderate size.
        if f.fract() == 0.0 && f.abs() < 1e30 {
            return Some(Self::from_integer(f as i128));
        }
        BigRational::from_float(f).map(Self::from_big)
    }

    /// The nearest double (correctly rounded); `±inf` beyond the double
    /// range.
    #[must_use]
    pub fn to_f64(&self) -> f64 {
        let f = match &self.0 {
            Repr::Small(r) => r.to_f64(),
            Repr::Big(b) => b.to_f64(),
        };
        f.unwrap_or_else(|| {
            if self.is_negative() {
                f64::NEG_INFINITY
            } else {
                f64::INFINITY
            }
        })
    }

    /// The tightest pair of doubles `(lo, hi)` with `lo <= self <= hi`:
    /// a point when the value is a double, otherwise two adjacent
    /// doubles. Values beyond the double range enclose against the
    /// largest finite double and the matching infinity.
    #[must_use]
    pub fn to_f64_enclosure(&self) -> (f64, f64) {
        let f = self.to_f64();
        if f == f64::INFINITY {
            return (f64::MAX, f64::INFINITY);
        }
        if f == f64::NEG_INFINITY {
            return (f64::NEG_INFINITY, f64::MIN);
        }
        match Rational::from_f64(f).map(|exact| exact.cmp(self)) {
            Some(Ordering::Equal) | None => (f, f),
            Some(Ordering::Less) => (f, f.next_up()),
            Some(Ordering::Greater) => (f.next_down(), f),
        }
    }

    /// Whether the denominator is 1.
    #[must_use]
    pub fn is_integer(&self) -> bool {
        match &self.0 {
            Repr::Small(r) => *r.denom() == 1,
            Repr::Big(b) => b.is_integer(),
        }
    }

    /// The value as an `i128` when it is an integer in range.
    #[must_use]
    pub fn to_i128(&self) -> Option<i128> {
        match &self.0 {
            Repr::Small(r) if *r.denom() == 1 => Some(*r.numer()),
            _ => None,
        }
    }

    /// The value as a big integer when it is an integer.
    #[must_use]
    pub fn to_bigint(&self) -> Option<BigInt> {
        match &self.0 {
            Repr::Small(r) if *r.denom() == 1 => Some(BigInt::from(*r.numer())),
            Repr::Big(b) if b.is_integer() => Some(b.numer().clone()),
            _ => None,
        }
    }

    /// Numerator and denominator as `i128` when both fit.
    #[must_use]
    pub fn to_i128_parts(&self) -> Option<(i128, i128)> {
        match &self.0 {
            Repr::Small(r) => Some((*r.numer(), *r.denom())),
            Repr::Big(_) => None,
        }
    }

    /// Numerator and denominator as `i32` when both fit.
    #[must_use]
    pub fn to_i32_parts(&self) -> Option<(i32, i32)> {
        let (n, d) = self.to_i128_parts()?;
        Some((i32::try_from(n).ok()?, i32::try_from(d).ok()?))
    }

    /// Numerator and denominator as decimal strings (denominator positive).
    #[must_use]
    pub fn to_string_parts(&self) -> (String, String) {
        match &self.0 {
            Repr::Small(r) => (r.numer().to_string(), r.denom().to_string()),
            Repr::Big(b) => (b.numer().to_string(), b.denom().to_string()),
        }
    }

    #[must_use]
    pub fn is_zero(&self) -> bool {
        match &self.0 {
            Repr::Small(r) => r.numer().is_zero(),
            Repr::Big(b) => b.is_zero(),
        }
    }

    #[must_use]
    pub fn is_negative(&self) -> bool {
        match &self.0 {
            Repr::Small(r) => r.numer().is_negative(),
            Repr::Big(b) => b.is_negative(),
        }
    }

    #[must_use]
    pub fn is_positive(&self) -> bool {
        match &self.0 {
            Repr::Small(r) => r.numer().is_positive(),
            Repr::Big(b) => b.is_positive(),
        }
    }

    #[must_use]
    pub fn is_one(&self) -> bool {
        match &self.0 {
            Repr::Small(r) => r.is_one(),
            Repr::Big(b) => b.is_one(),
        }
    }

    fn binary(
        &self,
        o: &Rational,
        small: impl Fn(&Small, &Small) -> Option<Small>,
        big: impl Fn(&BigRational, &BigRational) -> BigRational,
    ) -> Rational {
        if let (Repr::Small(a), Repr::Small(b)) = (&self.0, &o.0) {
            if let Some(r) = small(a, b) {
                return Self::small(r);
            }
        }
        Self::from_big(big(&self.to_big(), &o.to_big()))
    }

    #[must_use]
    pub fn add(&self, o: &Rational) -> Rational {
        self.binary(o, |a, b| a.checked_add(b), |a, b| a + b)
    }

    #[must_use]
    pub fn sub(&self, o: &Rational) -> Rational {
        self.binary(o, |a, b| a.checked_sub(b), |a, b| a - b)
    }

    #[must_use]
    pub fn mul(&self, o: &Rational) -> Rational {
        self.binary(o, |a, b| a.checked_mul(b), |a, b| a * b)
    }

    /// `self / o`; `None` when `o` is zero.
    #[must_use]
    pub fn div(&self, o: &Rational) -> Option<Rational> {
        if o.is_zero() {
            return None;
        }
        Some(self.binary(o, |a, b| a.checked_div(b), |a, b| a / b))
    }

    /// Truncated remainder `self - o * trunc(self / o)`; `None` when `o`
    /// is zero.
    #[must_use]
    pub fn rem(&self, o: &Rational) -> Option<Rational> {
        let q = self.div(o)?.trunc();
        Some(self.sub(&o.mul(&q)))
    }

    #[must_use]
    pub fn neg(&self) -> Rational {
        match &self.0 {
            Repr::Small(r) => Rational(Repr::Small(Small::new_raw(-r.numer(), *r.denom()))),
            Repr::Big(b) => Self::from_big(-(**b).clone()),
        }
    }

    #[must_use]
    pub fn abs(&self) -> Rational {
        if self.is_negative() {
            self.neg()
        } else {
            self.clone()
        }
    }

    /// `1 / self`; `None` for zero.
    #[must_use]
    pub fn recip(&self) -> Option<Rational> {
        Rational::one().div(self)
    }

    #[must_use]
    pub fn trunc(&self) -> Rational {
        match &self.0 {
            Repr::Small(r) => Self::small(r.trunc()),
            Repr::Big(b) => Self::from_big(b.trunc()),
        }
    }

    #[must_use]
    pub fn floor(&self) -> Rational {
        match &self.0 {
            Repr::Small(r) => Self::small(r.floor()),
            Repr::Big(b) => Self::from_big(b.floor()),
        }
    }

    #[must_use]
    pub fn ceil(&self) -> Rational {
        match &self.0 {
            Repr::Small(r) => Self::small(r.ceil()),
            Repr::Big(b) => Self::from_big(b.ceil()),
        }
    }

    /// Round half away from zero.
    #[must_use]
    pub fn round(&self) -> Rational {
        match &self.0 {
            Repr::Small(r) => Self::small(r.round()),
            Repr::Big(b) => Self::from_big(b.round()),
        }
    }

    /// Bits needed for the larger of numerator and denominator: the size
    /// a value occupies, for budgets.
    #[must_use]
    pub fn bits(&self) -> u64 {
        match &self.0 {
            Repr::Small(r) => {
                let n = r.numer().unsigned_abs();
                let d = r.denom().unsigned_abs();
                (128 - n.max(d).leading_zeros()) as u64
            }
            Repr::Big(b) => b.numer().bits().max(b.denom().bits()),
        }
    }

    /// `self ** e` for an integer exponent; `None` for `0 ** negative`
    /// and for results too large to materialize.
    #[must_use]
    pub fn pow(&self, e: i32) -> Option<Rational> {
        if e < 0 {
            return self.recip()?.pow(e.checked_neg()?);
        }
        if e == 0 {
            return Some(Rational::one());
        }
        let e = e as u32;
        if self.bits().checked_mul(e as u64)? > MAX_BITS {
            return None;
        }
        if let Repr::Small(r) = &self.0 {
            if let (Some(n), Some(d)) = (r.numer().checked_pow(e), r.denom().checked_pow(e)) {
                return Some(Self::small(Small::new_raw(n, d)));
            }
        }
        let b = self.to_big();
        Some(Self::from_big(BigRational::new_raw(
            b.numer().pow(e),
            b.denom().pow(e),
        )))
    }

    /// The exact `n`-th root when one exists (`root(4, 2)` is `2`,
    /// `root(-8, 3)` is `-2`, `root(1/4, 2)` is `1/2`); `None` when the
    /// value is not a perfect power, `n` is zero, or the value is
    /// negative with an even `n`.
    #[must_use]
    pub fn root(&self, n: u32) -> Option<Rational> {
        if n == 0 {
            return None;
        }
        if n == 1 {
            return Some(self.clone());
        }
        if self.is_negative() {
            if n.is_multiple_of(2) {
                return None;
            }
            return Some(self.neg().root(n)?.neg());
        }
        let b = self.to_big();
        let exact_root = |x: &BigInt| {
            let r = x.nth_root(n);
            (r.pow(n) == *x).then_some(r)
        };
        let num = exact_root(b.numer())?;
        let den = exact_root(b.denom())?;
        Some(Self::from_big(BigRational::new_raw(num, den)))
    }

    /// `self ** (p/q)` exactly when the root exists.
    #[must_use]
    pub fn pow_rational(&self, exp: &Rational) -> Option<Rational> {
        let (p, q) = exp.to_i32_parts()?;
        let base = self.root(u32::try_from(q).ok()?)?;
        base.pow(p)
    }

    /// The exact decimal expansion when it terminates: `(negative,
    /// digits, fraction_len)` with `digits` free of a leading zero unless
    /// the integer part is zero.
    fn decimal_parts(&self) -> Option<(bool, String, usize)> {
        let (numer, denom): (BigInt, BigInt) = match &self.0 {
            Repr::Small(r) => (BigInt::from(*r.numer()), BigInt::from(*r.denom())),
            Repr::Big(b) => (b.numer().clone(), b.denom().clone()),
        };
        if denom.is_one() {
            return Some((numer.is_negative(), numer.abs().to_string(), 0));
        }
        let two = BigInt::from(2u32);
        let five = BigInt::from(5u32);
        let mut d = denom;
        let mut twos = 0u32;
        let mut fives = 0u32;
        while d.is_even() {
            d /= &two;
            twos += 1;
        }
        loop {
            let (q, r) = d.div_rem(&five);
            if !r.is_zero() {
                break;
            }
            d = q;
            fives += 1;
        }
        if !d.is_one() {
            return None;
        }
        let k = twos.max(fives);
        let m = numer.abs() * two.pow(k - twos) * five.pow(k - fives);
        let mut s = m.to_string();
        let k = k as usize;
        if s.len() <= k {
            s = format!("{}{}", "0".repeat(k + 1 - s.len()), s);
        }
        Some((numer.is_negative(), s, k))
    }

    /// The exact decimal spelling when the expansion terminates.
    #[must_use]
    pub fn to_decimal_string(&self) -> Option<String> {
        let (neg, digits, k) = self.decimal_parts()?;
        let mut out = String::with_capacity(digits.len() + 2);
        if neg {
            out.push('-');
        }
        if k == 0 {
            out.push_str(&digits);
        } else {
            let split = digits.len() - k;
            out.push_str(&digits[..split]);
            out.push('.');
            out.push_str(&digits[split..]);
        }
        Some(out)
    }

    /// A display spelling that is always a decimal: the exact decimal
    /// when the expansion terminates, otherwise the shortest spelling of
    /// the nearest double marked as approximate (`≈0.3333333333333333`).
    /// For surfaces that favour a glanceable number over a re-parseable
    /// one; [`fmt::Display`] stays exact.
    #[must_use]
    pub fn to_approx_string(&self) -> String {
        match self.to_decimal_string() {
            Some(s) => s,
            None => format!("≈{}", self.to_f64()),
        }
    }

    /// Whether printing this value as a JSON number literal loses
    /// nothing: the spelling is an integer or a terminating decimal that
    /// a double's shortest round-trip spelling reproduces exactly. A JSON
    /// serializer may still spell that double with an exponent (`1e30`,
    /// `1e-7`); the digits are the same, so the literal denotes exactly
    /// this value.
    #[must_use]
    pub fn json_number_is_exact(&self) -> bool {
        let Some(dec) = self.to_decimal_string() else {
            return false;
        };
        let f = self.to_f64();
        if !f.is_finite() {
            return false;
        }
        let shortest = if f.fract() == 0.0 && f.abs() < 1e16 {
            format!("{}", f as i64)
        } else {
            format!("{f}")
        };
        shortest == dec
    }
}

impl Default for Rational {
    fn default() -> Self {
        Rational::zero()
    }
}

impl fmt::Display for Rational {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.to_decimal_string() {
            Some(s) => f.write_str(&s),
            None => {
                let (n, d) = self.to_string_parts();
                write!(f, "{n}/{d}")
            }
        }
    }
}

impl fmt::Debug for Rational {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let (n, d) = self.to_string_parts();
        write!(f, "Rational({n}/{d})")
    }
}

impl PartialEq for Rational {
    fn eq(&self, other: &Rational) -> bool {
        match (&self.0, &other.0) {
            (Repr::Small(a), Repr::Small(b)) => a == b,
            (Repr::Big(a), Repr::Big(b)) => a == b,
            _ => false,
        }
    }
}

impl Eq for Rational {}

impl PartialOrd for Rational {
    fn partial_cmp(&self, other: &Rational) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Rational {
    fn cmp(&self, other: &Rational) -> Ordering {
        match (&self.0, &other.0) {
            (Repr::Small(a), Repr::Small(b)) => a.cmp(b),
            _ => self.to_big().cmp(&other.to_big()),
        }
    }
}

impl Hash for Rational {
    fn hash<H: Hasher>(&self, state: &mut H) {
        match &self.0 {
            Repr::Small(r) => {
                0u8.hash(state);
                r.numer().hash(state);
                r.denom().hash(state);
            }
            Repr::Big(b) => {
                1u8.hash(state);
                b.numer().hash(state);
                b.denom().hash(state);
            }
        }
    }
}

impl From<i128> for Rational {
    fn from(i: i128) -> Self {
        Rational::from_integer(i)
    }
}

impl From<i64> for Rational {
    fn from(i: i64) -> Self {
        Rational::from_integer(i as i128)
    }
}

impl From<i32> for Rational {
    fn from(i: i32) -> Self {
        Rational::from_integer(i as i128)
    }
}

impl From<u32> for Rational {
    fn from(i: u32) -> Self {
        Rational::from_integer(i as i128)
    }
}

impl serde::Serialize for Rational {
    fn serialize<S: serde::Serializer>(&self, s: S) -> Result<S::Ok, S::Error> {
        self.to_string_parts().serialize(s)
    }
}

impl<'de> serde::Deserialize<'de> for Rational {
    fn deserialize<D: serde::Deserializer<'de>>(d: D) -> Result<Self, D::Error> {
        let (n, den): (String, String) = serde::Deserialize::deserialize(d)?;
        let parse = |s: &str| {
            BigInt::parse_bytes(s.as_bytes(), 10)
                .ok_or_else(|| serde::de::Error::custom("malformed rational component"))
        };
        let (n, den) = (parse(&n)?, parse(&den)?);
        if !den.is_positive() {
            return Err(serde::de::Error::custom(
                "rational denominator must be positive",
            ));
        }
        Ok(Rational::from_big(BigRational::new(n, den)))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn dec(s: &str) -> Rational {
        Rational::parse_decimal(s).unwrap()
    }

    #[test]
    fn decimal_literals_are_exact() {
        assert_eq!(dec("0.1").add(&dec("0.2")), dec("0.3"));
        assert_eq!(dec("0.1").add(&dec("0.2")), Rational::new(3, 10).unwrap());
        assert_eq!(dec("100").mul(&dec("1.1")), Rational::from_integer(110));
        assert_eq!(dec("1.1").mul(&dec("1.1")), dec("1.21"));
        assert_eq!(
            dec("2.957353E-05"),
            Rational::new(2_957_353, 100_000_000_000).unwrap()
        );
        assert_eq!(dec("1e30"), Rational::from_integer(10i128.pow(30)));
        assert_eq!(dec(".5"), Rational::new(1, 2).unwrap());
        assert_eq!(dec("5."), Rational::from_integer(5));
        assert_eq!(dec("-0.25"), Rational::new(-1, 4).unwrap());
        assert_eq!(dec("+7"), Rational::from_integer(7));
        assert_eq!(dec("000.000"), Rational::zero());
        assert!(Rational::parse_decimal("1e").is_none());
        assert!(Rational::parse_decimal("abc").is_none());
        assert!(Rational::parse_decimal("1.2.3").is_none());
        assert!(Rational::parse_decimal("").is_none());
        assert!(Rational::parse_decimal("1e999999").is_none());
    }

    #[test]
    fn printed_spellings_parse_back() {
        for text in ["0.3", "110", "-0.5", "1/3", "-500000/3183", "2.957353E-05"] {
            let r = Rational::parse(text).unwrap();
            assert_eq!(Rational::parse(&r.to_string()), Some(r.clone()), "{text}");
        }
        assert_eq!(Rational::parse("1.5/0.5"), Some(Rational::from_integer(3)));
        assert_eq!(Rational::parse(" 2/4 "), Rational::new(1, 2));
        assert!(Rational::parse("1/0").is_none());
        assert!(Rational::parse("1/2/3").is_none());
        assert!(Rational::parse("a/b").is_none());
        let big = Rational::from_integer(i128::MAX).add(&Rational::one());
        assert_eq!(Rational::parse(&big.to_string()), Some(big));
    }

    #[test]
    fn scale_powers_always_compose() {
        assert_eq!(dec("0.001").pow_or_approx(3), dec("1e-9"));
        assert_eq!(
            dec("4").pow_ratio_or_approx((1, 2)),
            Rational::from_integer(2)
        );
        assert_eq!(
            dec("8").pow_ratio_or_approx((-2, 3)),
            Rational::new(1, 4).unwrap()
        );
        // Beyond the exact bound the nearest double stands in.
        let huge = dec("10").pow_or_approx(1_000_000);
        assert_eq!(
            huge,
            Rational::from_f64(f64::INFINITY).unwrap_or_else(Rational::one)
        );
        let root = dec("2").pow_ratio_or_approx((1, 2));
        assert_eq!(root, Rational::from_f64(std::f64::consts::SQRT_2).unwrap());
        assert!(dec("2").pow_ratio_or_approx((1, 0)).is_one());
    }

    #[test]
    fn big_literals_round_trip() {
        let big = dec("123456789012345678901234567890123456789012345678901234567890");
        assert!(big.to_i128().is_none());
        assert!(big.is_integer());
        assert_eq!(
            big.to_string(),
            "123456789012345678901234567890123456789012345678901234567890"
        );
        let tiny = dec("1.602176634e-19");
        assert_eq!(tiny.to_string(), "0.0000000000000000001602176634");
        assert_eq!(tiny.mul(&dec("1e19")), dec("1.602176634"));
    }

    #[test]
    fn display_terminating_or_fraction() {
        assert_eq!(dec("0.3").to_string(), "0.3");
        assert_eq!(dec("110.0").to_string(), "110");
        assert_eq!(dec("-0.5").to_string(), "-0.5");
        assert_eq!(dec("0.000123").to_string(), "0.000123");
        assert_eq!(Rational::new(1, 3).unwrap().to_string(), "1/3");
        assert_eq!(Rational::new(-2, 6).unwrap().to_string(), "-1/3");
        assert_eq!(Rational::new(1, 8).unwrap().to_string(), "0.125");
        assert_eq!(Rational::new(1, 25).unwrap().to_string(), "0.04");
        assert_eq!(Rational::new(7, 2).unwrap().to_string(), "3.5");
        assert_eq!(
            Rational::new(500_000, 3183).unwrap().to_string(),
            "500000/3183"
        );
        assert_eq!(Rational::zero().to_string(), "0");
    }

    #[test]
    fn overflow_promotes_and_demotes() {
        let big = Rational::from_integer(i128::MAX).add(&Rational::one());
        assert!(big.to_i128().is_none());
        assert_eq!(big.to_string(), "170141183460469231731687303715884105728");
        let back = big.sub(&Rational::one());
        assert_eq!(back.to_i128(), Some(i128::MAX));
        let min = Rational::from_integer(i128::MIN);
        assert_eq!(
            min.neg().to_string(),
            "170141183460469231731687303715884105728"
        );
        assert_eq!(min.abs().neg(), min);
        let product = Rational::from_integer(i128::MAX).mul(&Rational::from_integer(i128::MAX));
        assert_eq!(
            product
                .div(&Rational::from_integer(i128::MAX))
                .unwrap()
                .to_i128(),
            Some(i128::MAX)
        );
        // Rational overflow in the sum of two small fractions.
        let a = Rational::new(1, i128::MAX).unwrap();
        let b = Rational::new(1, i128::MAX - 1).unwrap();
        let s = a.add(&b);
        assert_eq!(s.sub(&b), a);
    }

    #[test]
    fn powers_and_roots() {
        assert_eq!(dec("2").pow(10).unwrap(), Rational::from_integer(1024));
        assert_eq!(dec("2").pow(-2).unwrap(), Rational::new(1, 4).unwrap());
        assert_eq!(dec("0.5").pow(3).unwrap(), dec("0.125"));
        assert!(Rational::zero().pow(-1).is_none());
        assert_eq!(dec("2").pow(200).unwrap().to_string().len(), 61);
        assert!(dec("2").pow(i32::MAX).is_none());
        assert_eq!(dec("9").root(2).unwrap(), Rational::from_integer(3));
        assert_eq!(dec("0.25").root(2).unwrap(), dec("0.5"));
        assert_eq!(dec("-8").root(3).unwrap(), Rational::from_integer(-2));
        assert!(dec("2").root(2).is_none());
        assert!(dec("-4").root(2).is_none());
        assert_eq!(
            dec("8")
                .pow_rational(&Rational::new(2, 3).unwrap())
                .unwrap(),
            Rational::from_integer(4)
        );
        assert_eq!(
            dec("4")
                .pow_rational(&Rational::new(-1, 2).unwrap())
                .unwrap(),
            dec("0.5")
        );
    }

    #[test]
    fn rounding_family() {
        assert_eq!(dec("2.5").floor(), Rational::from_integer(2));
        assert_eq!(dec("2.5").ceil(), Rational::from_integer(3));
        assert_eq!(dec("2.5").round(), Rational::from_integer(3));
        assert_eq!(dec("-2.5").round(), Rational::from_integer(-3));
        assert_eq!(dec("-2.5").trunc(), Rational::from_integer(-2));
        assert_eq!(dec("7").rem(&dec("2")).unwrap(), Rational::one());
        assert_eq!(dec("7.5").rem(&dec("2")).unwrap(), dec("1.5"));
        assert_eq!(
            dec("-7").rem(&dec("2")).unwrap(),
            Rational::from_integer(-1)
        );
        assert!(dec("1").rem(&Rational::zero()).is_none());
    }

    #[test]
    fn double_conversion_is_correctly_rounded_and_enclosed() {
        assert_eq!(dec("0.1").to_f64(), 0.1);
        assert_eq!(dec("0.3").to_f64(), 0.3);
        assert_eq!(Rational::new(1, 3).unwrap().to_f64(), 1.0 / 3.0);
        assert_eq!(
            Rational::from_f64(0.1).unwrap().to_string(),
            "0.1000000000000000055511151231257827021181583404541015625"
        );
        assert_eq!(Rational::from_f64(-2.5).unwrap(), dec("-2.5"));
        assert!(Rational::from_f64(f64::INFINITY).is_none());
        assert_eq!(dec("0.5").to_f64_enclosure(), (0.5, 0.5));
        let (lo, hi) = dec("0.1").to_f64_enclosure();
        assert!(lo < hi);
        assert_eq!(hi, lo.next_up());
        assert!(Rational::from_f64(lo).unwrap() < dec("0.1"));
        assert!(Rational::from_f64(hi).unwrap() > dec("0.1"));
        let huge = dec("1e400");
        assert_eq!(huge.to_f64(), f64::INFINITY);
        assert_eq!(huge.to_f64_enclosure(), (f64::MAX, f64::INFINITY));
        assert_eq!(huge.neg().to_f64_enclosure(), (f64::NEG_INFINITY, f64::MIN));
    }

    #[test]
    fn ordering_and_equality_across_representations() {
        let big = Rational::from_integer(i128::MAX).add(&Rational::one());
        assert!(big > Rational::from_integer(i128::MAX));
        assert!(Rational::new(1, 3).unwrap() < dec("0.34"));
        assert!(dec("-1e40") < Rational::from_integer(0));
        assert_eq!(dec("0.10"), dec("0.1"));
        assert_ne!(dec("0.1"), Rational::from_f64(0.1).unwrap());
        use std::collections::HashSet;
        let set: HashSet<Rational> = [dec("0.1"), dec("0.10"), dec("1e-1")].into_iter().collect();
        assert_eq!(set.len(), 1);
    }

    #[test]
    fn approx_text_is_decimal_and_marked() {
        assert_eq!(dec("0.3").to_approx_string(), "0.3");
        assert_eq!(dec("110").to_approx_string(), "110");
        assert_eq!(
            Rational::new(1, 3).unwrap().to_approx_string(),
            "≈0.3333333333333333"
        );
        assert_eq!(
            Rational::new(500_000, 3183).unwrap().to_approx_string(),
            "≈157.08451146716934"
        );
        assert_eq!(
            Rational::new(-2, 3).unwrap().to_approx_string(),
            "≈-0.6666666666666666"
        );
    }

    #[test]
    fn json_exactness_probe() {
        assert!(dec("0.1").json_number_is_exact());
        assert!(dec("0.3").json_number_is_exact());
        assert!(dec("110").json_number_is_exact());
        assert!(dec("1e30").json_number_is_exact());
        assert!(!Rational::new(1, 3).unwrap().json_number_is_exact());
        assert!(
            !dec("0.1000000000000000055511151231257827021181583404541015625")
                .json_number_is_exact()
        );
        assert!(!dec("0.30000000000000004000000001").json_number_is_exact());
    }

    #[test]
    fn serde_round_trip() {
        for r in [
            dec("0.1"),
            Rational::new(-1, 3).unwrap(),
            dec("1e50"),
            Rational::zero(),
        ] {
            let json = serde_json::to_string(&r).unwrap();
            let back: Rational = serde_json::from_str(&json).unwrap();
            assert_eq!(back, r);
        }
        assert!(serde_json::from_str::<Rational>(r#"["1","0"]"#).is_err());
        assert!(serde_json::from_str::<Rational>(r#"["1","-2"]"#).is_err());
    }
}
