//! How an exact rational without a terminating decimal expansion is
//! shown to a reader: `1/15`, `≈0.06666666666666667`, `0.06̅`, `0.0(6)`
//! or `¹/₁₅`. Integers and terminating decimals always print as the
//! exact decimal; only the non-terminating rest depends on the style.
//!
//! One [`NumberFormat`] serves the surfaces that show computed values
//! at a glance — editor value hints, hover values and range hints, and
//! the command line's `eval`, `query` and `verify` output — and parses
//! from one spec string so each host configures it the same way: a
//! style name, then optional `key=value` settings separated by commas
//! (`overline,period=4`, `unicode,mixed=false`). Findings and the
//! bindings that explain a verdict stay exact.
//!
//! | Style | `1/15` | `7/3` | Settings |
//! |---|---|---|---|
//! | `exact` | `1/15` | `7/3` (`mixed`: `2 1/3`) | `mixed`, `fraction-digits`, `digits` |
//! | `approx` | `≈0.06666666666666667` (`digits=4`: `≈0.06667`) | `≈2.3333333333333335` | `digits` |
//! | `overline` | `0.06̅` | `2.3̅` | `period`, `digits` |
//! | `parens` | `0.0(6)` | `2.(3)` | `period`, `digits` |
//! | `unicode` | `¹/₁₅` | `2¹/₃` | `mixed`, `slash`, `glyphs`, `fraction-digits`, `digits` |
//!
//! A value a style cannot show within its limits — a repeating period
//! longer than `period`, a fraction part with more digits than
//! `fraction-digits` — falls back to the approximate decimal with
//! `digits` significant digits, rounded on the exact value (`0` = the
//! double's shortest round-trip spelling). Past `1e21` or below
//! `1e-6` it writes an exponent (`≈3.33e-401`).

use crate::rational::Rational;
use num_bigint::BigInt;
use num_integer::Integer;
use num_traits::{Signed, Zero};
use std::fmt;
use std::str::FromStr;

/// The longest non-repeating prefix a repeating-decimal style prints
/// before it falls back (`1/(3·2^40)` has a 40-digit prefix).
const MAX_PREFIX: usize = 15;
/// The largest `period` a spec may ask for: periods can be as long as
/// the denominator, so the bound keeps rendering cheap.
pub const MAX_PERIOD: u32 = 1000;

/// How a non-terminating rational is written. See the
/// [module docs](self) for examples.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum NumberStyle {
    /// The reduced fraction, `1/15` — exact and re-parseable.
    Exact,
    /// The nearest double, marked approximate: `≈0.06666666666666667`.
    Approx,
    /// A repeating decimal with the period overlined (U+0305): `0.06̅`.
    Overline,
    /// A repeating decimal with the period in parentheses: `0.0(6)`.
    Parens,
    /// A fraction of superscript and subscript digits: `¹/₁₅`, `2¹/₃`.
    Unicode,
}

impl NumberStyle {
    /// Every style, in spec-name order of the docs.
    pub const ALL: &'static [NumberStyle] = &[
        NumberStyle::Exact,
        NumberStyle::Approx,
        NumberStyle::Overline,
        NumberStyle::Parens,
        NumberStyle::Unicode,
    ];

    /// The style's spec name.
    #[must_use]
    pub const fn name(self) -> &'static str {
        match self {
            NumberStyle::Exact => "exact",
            NumberStyle::Approx => "approx",
            NumberStyle::Overline => "overline",
            NumberStyle::Parens => "parens",
            NumberStyle::Unicode => "unicode",
        }
    }
}

/// The character between a `unicode` fraction's numerator and
/// denominator.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum FractionSlash {
    /// `/` (U+002F), drawn by every font.
    Solidus,
    /// `⁄` (U+2044), the typographic fraction slash.
    Fraction,
    /// `∕` (U+2215), the division slash.
    Division,
}

impl FractionSlash {
    const fn name(self) -> &'static str {
        match self {
            FractionSlash::Solidus => "solidus",
            FractionSlash::Fraction => "fraction",
            FractionSlash::Division => "division",
        }
    }

    const fn glyph(self) -> char {
        match self {
            FractionSlash::Solidus => '/',
            FractionSlash::Fraction => '\u{2044}',
            FractionSlash::Division => '\u{2215}',
        }
    }
}

/// A rendering of non-terminating rationals: a [`NumberStyle`] and the
/// settings that tune it. Build one with [`NumberFormat::new`] (the
/// style's defaults), [`NumberFormat::exact`] or
/// [`NumberFormat::approx`], or parse a spec string; [`fmt::Display`]
/// writes the canonical spec back. Two formats are equal when they
/// render alike: settings the style does not use are ignored.
#[derive(Clone, Copy, Debug)]
#[non_exhaustive]
pub struct NumberFormat {
    /// The style.
    pub style: NumberStyle,
    /// Significant digits of an approximate decimal — the `approx`
    /// style's own, and every style's fallback. `0` = the double's
    /// shortest round-trip spelling.
    pub digits: u32,
    /// The longest repeating period `overline` and `parens` write out
    /// (1 to [`MAX_PERIOD`]); a longer one falls back.
    pub period: u32,
    /// `exact` and `unicode`: write an improper fraction as a whole
    /// number and a proper fraction (`2 1/3`, `2¹/₃`).
    pub mixed: bool,
    /// `unicode`: the character between numerator and denominator.
    pub slash: FractionSlash,
    /// `unicode`: use a precomposed glyph (`⅓`, `⅚`, `⅐`, `⅑`) where
    /// Unicode has one for the fraction part.
    pub glyphs: bool,
    /// `exact` and `unicode`: the most digits a fraction's numerator or
    /// denominator may have before the value falls back (a mixed
    /// number's whole part does not count); `0` = no limit.
    pub fraction_digits: u32,
}

impl NumberFormat {
    /// `style` with its default settings.
    #[must_use]
    pub fn new(style: NumberStyle) -> NumberFormat {
        NumberFormat {
            style,
            digits: if style == NumberStyle::Approx { 0 } else { 6 },
            period: 6,
            mixed: style == NumberStyle::Unicode,
            slash: FractionSlash::Solidus,
            glyphs: false,
            fraction_digits: if style == NumberStyle::Unicode { 2 } else { 0 },
        }
    }

    /// The exact fraction, `1/15` — what the evaluator's `Display`
    /// writes, and every surface's default.
    #[must_use]
    pub fn exact() -> NumberFormat {
        NumberFormat::new(NumberStyle::Exact)
    }

    /// The nearest double's shortest spelling, marked approximate.
    #[must_use]
    pub fn approx() -> NumberFormat {
        NumberFormat::new(NumberStyle::Approx)
    }

    /// Parse a spec: a style name, then optional comma-separated
    /// `key=value` settings — `digits`, `period`, `mixed`, `slash`
    /// (`solidus` | `fraction` | `division`), `glyphs`,
    /// `fraction-digits`. A setting the style does not use is an error,
    /// as is a repeated one.
    pub fn parse(spec: &str) -> Result<NumberFormat, String> {
        let mut parts = spec.split(',').map(str::trim);
        let name = parts.next().unwrap_or_default();
        let style = NumberStyle::ALL
            .iter()
            .copied()
            .find(|s| s.name() == name)
            .ok_or_else(|| {
                format!(
                    "unknown number style `{name}` (expected {})",
                    NumberStyle::ALL
                        .iter()
                        .map(|s| format!("`{}`", s.name()))
                        .collect::<Vec<_>>()
                        .join(", ")
                )
            })?;
        let mut f = NumberFormat::new(style);
        let mut seen: Vec<&str> = Vec::new();
        for part in parts {
            let Some((key, value)) = part.split_once('=') else {
                return Err(format!("expected `key=value`, got `{part}`"));
            };
            let (key, value) = (key.trim(), value.trim());
            if seen.contains(&key) {
                return Err(format!("`{key}` is set twice"));
            }
            seen.push(key);
            if !Self::uses(style, key) {
                return Err(if Self::KEYS.contains(&key) {
                    format!("`{key}` does not apply to the `{}` style", style.name())
                } else {
                    format!(
                        "unknown setting `{key}` (expected {})",
                        Self::KEYS
                            .iter()
                            .map(|k| format!("`{k}`"))
                            .collect::<Vec<_>>()
                            .join(", ")
                    )
                });
            }
            let number = |min: u32, max: u32| -> Result<u32, String> {
                value
                    .bytes()
                    .all(|b| b.is_ascii_digit())
                    .then(|| value.parse::<u32>().ok())
                    .flatten()
                    .filter(|n| (min..=max).contains(n))
                    .ok_or_else(|| format!("`{key}` must be a whole number from {min} to {max}"))
            };
            let flag = || -> Result<bool, String> {
                match value {
                    "true" | "on" | "yes" => Ok(true),
                    "false" | "off" | "no" => Ok(false),
                    _ => Err(format!("`{key}` must be `true` or `false`")),
                }
            };
            match key {
                "digits" => f.digits = number(0, 17)?,
                "period" => f.period = number(1, MAX_PERIOD)?,
                "mixed" => f.mixed = flag()?,
                "glyphs" => f.glyphs = flag()?,
                "fraction-digits" => f.fraction_digits = number(0, u32::MAX)?,
                "slash" => {
                    f.slash = [
                        FractionSlash::Solidus,
                        FractionSlash::Fraction,
                        FractionSlash::Division,
                    ]
                    .into_iter()
                    .find(|s| s.name() == value)
                    .ok_or_else(|| {
                        format!(
                            "`slash` must be `solidus`, `fraction` or `division`, got `{value}`"
                        )
                    })?;
                }
                _ => unreachable!("`uses` admits only known keys"),
            }
        }
        Ok(f)
    }

    const KEYS: &'static [&'static str] = &[
        "digits",
        "period",
        "mixed",
        "slash",
        "glyphs",
        "fraction-digits",
    ];

    fn uses(style: NumberStyle, key: &str) -> bool {
        match key {
            "digits" => true,
            "period" => matches!(style, NumberStyle::Overline | NumberStyle::Parens),
            "mixed" | "fraction-digits" => {
                matches!(style, NumberStyle::Exact | NumberStyle::Unicode)
            }
            "slash" | "glyphs" => style == NumberStyle::Unicode,
            _ => false,
        }
    }

    /// `r` as this format writes it.
    #[must_use]
    pub fn render(&self, r: &Rational) -> String {
        if let Some(decimal) = r.to_decimal_string() {
            return decimal;
        }
        let shown = match self.style {
            NumberStyle::Exact => self.fraction(r, false),
            NumberStyle::Approx => None,
            NumberStyle::Overline | NumberStyle::Parens => self.repeating(r),
            NumberStyle::Unicode => self.fraction(r, true),
        };
        shown.unwrap_or_else(|| approximate(r, self.digits))
    }

    /// The fraction spelling, `None` past `fraction_digits`.
    fn fraction(&self, r: &Rational, unicode: bool) -> Option<String> {
        let (negative, numer, denom) = parts(r);
        let (whole, numer) = if self.mixed {
            numer.div_rem(&denom)
        } else {
            (BigInt::zero(), numer)
        };
        let (numer, denom) = (numer.to_string(), denom.to_string());
        let limit = self.fraction_digits as usize;
        if limit > 0 && (numer.len() > limit || denom.len() > limit) {
            return None;
        }
        let mut out = String::new();
        if negative {
            out.push('-');
        }
        if !whole.is_zero() {
            out.push_str(&whole.to_string());
            if !unicode {
                out.push(' ');
            }
        }
        if !unicode {
            out.push_str(&numer);
            out.push('/');
            out.push_str(&denom);
            return Some(out);
        }
        match self
            .glyphs
            .then(|| vulgar_fraction(&numer, &denom))
            .flatten()
        {
            Some(glyph) => out.push(glyph),
            None => {
                out.extend(numer.chars().map(superscript));
                out.push(self.slash.glyph());
                out.extend(denom.chars().map(subscript));
            }
        }
        Some(out)
    }

    /// The repeating-decimal spelling, `None` when the prefix or the
    /// period is too long to write out.
    fn repeating(&self, r: &Rational) -> Option<String> {
        let (negative, numer, denom) = parts(r);
        let (whole, mut rem) = numer.div_rem(&denom);
        // The prefix before the period is as long as the larger power
        // of 2 or 5 dividing the denominator.
        let (mut twos, mut fives, mut rest) = (0usize, 0usize, denom.clone());
        let (two, five) = (BigInt::from(2), BigInt::from(5));
        while rest.is_even() {
            rest /= &two;
            twos += 1;
            if twos > MAX_PREFIX {
                return None;
            }
        }
        while (&rest % &five).is_zero() {
            rest /= &five;
            fives += 1;
            if fives > MAX_PREFIX {
                return None;
            }
        }
        let ten = BigInt::from(10);
        let next_digit = |rem: &mut BigInt| -> char {
            *rem *= &ten;
            let (digit, left) = rem.div_rem(&denom);
            *rem = left;
            char::from(b'0' + u8::try_from(digit).unwrap_or(0))
        };
        let prefix: String = (0..twos.max(fives)).map(|_| next_digit(&mut rem)).collect();
        let start = rem.clone();
        let mut period = String::new();
        loop {
            period.push(next_digit(&mut rem));
            if rem == start {
                break;
            }
            if period.len() >= self.period as usize {
                return None;
            }
        }
        let mut out = String::new();
        if negative {
            out.push('-');
        }
        out.push_str(&whole.to_string());
        out.push('.');
        out.push_str(&prefix);
        if self.style == NumberStyle::Overline {
            for c in period.chars() {
                out.push(c);
                out.push('\u{0305}');
            }
        } else {
            out.push('(');
            out.push_str(&period);
            out.push(')');
        }
        Some(out)
    }
}

impl NumberFormat {
    /// This format with the settings its style does not use reset to
    /// that style's defaults — what equality and hashing compare.
    fn canonical(self) -> NumberFormat {
        let base = NumberFormat::new(self.style);
        let used = |key: &str| Self::uses(self.style, key);
        NumberFormat {
            style: self.style,
            digits: self.digits,
            period: if used("period") {
                self.period
            } else {
                base.period
            },
            mixed: if used("mixed") {
                self.mixed
            } else {
                base.mixed
            },
            slash: if used("slash") {
                self.slash
            } else {
                base.slash
            },
            glyphs: if used("glyphs") {
                self.glyphs
            } else {
                base.glyphs
            },
            fraction_digits: if used("fraction-digits") {
                self.fraction_digits
            } else {
                base.fraction_digits
            },
        }
    }

    fn key(self) -> (NumberStyle, u32, u32, bool, FractionSlash, bool, u32) {
        let c = self.canonical();
        (
            c.style,
            c.digits,
            c.period,
            c.mixed,
            c.slash,
            c.glyphs,
            c.fraction_digits,
        )
    }
}

impl PartialEq for NumberFormat {
    fn eq(&self, other: &NumberFormat) -> bool {
        self.key() == other.key()
    }
}

impl Eq for NumberFormat {}

impl std::hash::Hash for NumberFormat {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.key().hash(state);
    }
}

impl fmt::Display for NumberFormat {
    /// The canonical spec: the style and every setting that differs
    /// from the style's default. Parses back to an equal format.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let base = NumberFormat::new(self.style);
        f.write_str(self.style.name())?;
        if self.digits != base.digits {
            write!(f, ",digits={}", self.digits)?;
        }
        if Self::uses(self.style, "period") && self.period != base.period {
            write!(f, ",period={}", self.period)?;
        }
        if Self::uses(self.style, "mixed") && self.mixed != base.mixed {
            write!(f, ",mixed={}", self.mixed)?;
        }
        if Self::uses(self.style, "slash") && self.slash != base.slash {
            write!(f, ",slash={}", self.slash.name())?;
        }
        if Self::uses(self.style, "glyphs") && self.glyphs != base.glyphs {
            write!(f, ",glyphs={}", self.glyphs)?;
        }
        if Self::uses(self.style, "fraction-digits") && self.fraction_digits != base.fraction_digits
        {
            write!(f, ",fraction-digits={}", self.fraction_digits)?;
        }
        Ok(())
    }
}

impl FromStr for NumberFormat {
    type Err = String;

    fn from_str(s: &str) -> Result<NumberFormat, String> {
        NumberFormat::parse(s)
    }
}

/// Sign and magnitude parts of a reduced rational.
fn parts(r: &Rational) -> (bool, BigInt, BigInt) {
    let (numer, denom) = r.to_string_parts();
    let numer: BigInt = numer.parse().expect("a rational's numerator is an integer");
    let denom: BigInt = denom
        .parse()
        .expect("a rational's denominator is an integer");
    (numer.is_negative(), numer.abs(), denom)
}

/// The value marked approximate. `digits == 0` writes the nearest
/// double's shortest round-trip spelling, unless the value is out of
/// the double's range, when it writes 17 significant digits instead;
/// otherwise `digits` significant digits, rounded half away from zero
/// on the exact value.
fn approximate(r: &Rational, digits: u32) -> String {
    if digits == 0 {
        let x = r.to_f64();
        if x.is_finite() && (x != 0.0 || r.is_zero()) {
            return format!("≈{x}");
        }
        return rounded(r, 17);
    }
    rounded(r, digits)
}

/// `≈` and `r` to `digits` significant digits: plain decimal notation
/// from `1e-6` up to `1e21`, an exponent outside it (`≈3.33e-401`).
fn rounded(r: &Rational, digits: u32) -> String {
    let (negative, numer, denom) = parts(r);
    if numer.is_zero() {
        return "≈0".to_string();
    }
    let ten = BigInt::from(10);
    let pow = |e: i64| ten.pow(u32::try_from(e).expect("an exponent within the value's size"));
    let digits_of = |n: &BigInt| i64::try_from(n.to_string().len()).unwrap_or(i64::MAX);
    // The decimal exponent: 10^e <= numer/denom < 10^(e+1).
    let mut e = digits_of(&numer) - digits_of(&denom);
    let below = if e >= 0 {
        numer < &denom * pow(e)
    } else {
        &numer * pow(-e) < denom
    };
    if below {
        e -= 1;
    }
    let shift = i64::from(digits) - 1 - e;
    let (n, d) = if shift >= 0 {
        (&numer * pow(shift), denom)
    } else {
        (numer, &denom * pow(-shift))
    };
    let (quotient, rem) = n.div_rem(&d);
    let mut mantissa = if &rem * 2 >= d {
        quotient + 1
    } else {
        quotient
    };
    if digits_of(&mantissa) > i64::from(digits) {
        // Rounding carried into a new digit (9.96 → 10.0).
        mantissa /= &ten;
        e += 1;
    }
    let all = mantissa.to_string();
    let sig = all.trim_end_matches('0');
    let mut out = String::from("≈");
    if negative {
        out.push('-');
    }
    if !(-6..21).contains(&e) {
        out.push_str(&sig[..1]);
        if sig.len() > 1 {
            out.push('.');
            out.push_str(&sig[1..]);
        }
        out.push_str(&format!("e{e}"));
    } else if e >= 0 {
        let whole = usize::try_from(e).unwrap_or(0) + 1;
        if sig.len() <= whole {
            out.push_str(sig);
            out.push_str(&"0".repeat(whole - sig.len()));
        } else {
            out.push_str(&sig[..whole]);
            out.push('.');
            out.push_str(&sig[whole..]);
        }
    } else {
        out.push_str("0.");
        out.push_str(&"0".repeat(usize::try_from(-e - 1).unwrap_or(0)));
        out.push_str(sig);
    }
    out
}

fn superscript(c: char) -> char {
    match c {
        '0' => '⁰',
        '1' => '¹',
        '2' => '²',
        '3' => '³',
        '4' => '⁴',
        '5' => '⁵',
        '6' => '⁶',
        '7' => '⁷',
        '8' => '⁸',
        '9' => '⁹',
        c => c,
    }
}

fn subscript(c: char) -> char {
    match c {
        '0' => '₀',
        '1' => '₁',
        '2' => '₂',
        '3' => '₃',
        '4' => '₄',
        '5' => '₅',
        '6' => '₆',
        '7' => '₇',
        '8' => '₈',
        '9' => '₉',
        c => c,
    }
}

/// The precomposed glyph Unicode has for a reduced proper fraction
/// without a terminating decimal expansion (fractions that terminate
/// never reach a fraction style).
fn vulgar_fraction(numer: &str, denom: &str) -> Option<char> {
    Some(match (numer, denom) {
        ("1", "3") => '⅓',
        ("2", "3") => '⅔',
        ("1", "6") => '⅙',
        ("5", "6") => '⅚',
        ("1", "7") => '⅐',
        ("1", "9") => '⅑',
        _ => return None,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn q(n: i128, d: i128) -> Rational {
        Rational::new(n, d).unwrap()
    }

    fn show(spec: &str, n: i128, d: i128) -> String {
        NumberFormat::parse(spec).unwrap().render(&q(n, d))
    }

    #[test]
    fn terminating_values_are_exact_decimals_in_every_style() {
        for style in NumberStyle::ALL {
            let f = NumberFormat::new(*style);
            assert_eq!(f.render(&q(1, 4)), "0.25", "{style:?}");
            assert_eq!(f.render(&q(-3, 1)), "-3", "{style:?}");
            assert_eq!(f.render(&q(1, 1024)), "0.0009765625", "{style:?}");
        }
    }

    #[test]
    fn exact_matches_display() {
        for (n, d) in [(1, 15), (-7, 3), (360, 7), (229_835, 900)] {
            assert_eq!(NumberFormat::exact().render(&q(n, d)), q(n, d).to_string());
        }
        assert_eq!(show("exact,mixed=true", 7, 3), "2 1/3");
        assert_eq!(show("exact,mixed=true", -7, 3), "-2 1/3");
        assert_eq!(show("exact,mixed=true", 1, 15), "1/15");
        assert_eq!(show("exact,fraction-digits=2", 229_835, 900), "≈255.372");
    }

    #[test]
    fn approx_keeps_the_shortest_spelling_by_default() {
        assert_eq!(
            NumberFormat::approx().render(&q(1, 3)),
            "≈0.3333333333333333"
        );
        assert_eq!(
            q(1, 3).to_approx_string(),
            NumberFormat::approx().render(&q(1, 3))
        );
        assert_eq!(show("approx,digits=4", 1, 15), "≈0.06667");
        assert_eq!(show("approx,digits=3", 2, 3), "≈0.667");
        assert_eq!(show("approx,digits=3", -200_000, 3), "≈-66700");
        assert_eq!(show("approx,digits=1", -200_000, 3), "≈-70000");
        assert_eq!(show("approx,digits=2", 1, 3_000_000), "≈3.3e-7");
        assert_eq!(show("approx,digits=2", 1, 300_000), "≈0.0000033");
        // Rounding carries into a new digit.
        assert_eq!(show("approx,digits=1", 29, 3), "≈10");
        assert_eq!(show("approx,digits=2", 299, 3), "≈100");
    }

    #[test]
    fn approximate_rounding_works_on_the_exact_value() {
        let big = |e: u32| Rational::from_bigint(BigInt::from(10).pow(e));
        let third = |r: Rational| r.div(&q(3, 1)).unwrap();
        let digits = |spec: &str, r: &Rational| NumberFormat::parse(spec).unwrap().render(r);
        // Past the double's range: no `inf`, no `0`.
        assert_eq!(digits("approx,digits=3", &third(big(400))), "≈3.33e399");
        let tiny = third(big(400)).mul(&q(9, 1)).recip().unwrap();
        assert_eq!(digits("approx,digits=3", &tiny), "≈3.33e-401");
        assert_eq!(digits("approx,digits=3", &tiny.neg()), "≈-3.33e-401");
        assert_eq!(
            digits("approx", &third(big(400))),
            "≈3.3333333333333333e399"
        );
        assert_eq!(digits("approx", &tiny), "≈3.3333333333333333e-401");
        // Large values within range keep `digits`, not the double's noise.
        assert_eq!(
            digits("approx,digits=3", &big(300).div(&q(7, 1)).unwrap()),
            "≈1.43e299"
        );
        assert_eq!(
            digits("exact,fraction-digits=4", &third(big(400))),
            "≈3.33333e399"
        );
        // Just under a rounding tie rounds down; a double rounds it up.
        let under = q(12_345, 100_000).sub(&big(20).mul(&q(3, 1)).recip().unwrap());
        assert_eq!(digits("approx,digits=4", &under), "≈0.1234");
    }

    #[test]
    fn repeating_decimals_overline_or_parenthesize_the_period() {
        assert_eq!(show("parens", 1, 15), "0.0(6)");
        assert_eq!(show("parens", 7, 3), "2.(3)");
        assert_eq!(show("parens", -5, 12), "-0.41(6)");
        assert_eq!(show("parens", 360, 7), "51.(428571)");
        assert_eq!(show("parens", 1, 6), "0.1(6)");
        assert_eq!(show("overline", 1, 15), "0.06\u{305}");
        assert_eq!(show("overline", 1, 11), "0.0\u{305}9\u{305}");
    }

    #[test]
    fn a_period_past_the_limit_falls_back_to_digits() {
        assert_eq!(show("parens", 1, 97), "≈0.0103093");
        assert_eq!(show("parens,period=5", 360, 7), "≈51.4286");
        assert_eq!(show("parens,period=5,digits=3", 360, 7), "≈51.4");
        assert_eq!(show("parens,period=96", 1, 97).len(), "0.(".len() + 96 + 1);
        // A long prefix (a high power of 2 in the denominator) too.
        let r = Rational::new(1, 3 << 40).unwrap();
        assert!(
            NumberFormat::parse("parens")
                .unwrap()
                .render(&r)
                .starts_with('≈')
        );
    }

    #[test]
    fn unicode_fractions_compose_digits_and_mix_by_default() {
        assert_eq!(show("unicode", 1, 15), "¹/₁₅");
        assert_eq!(show("unicode", 7, 3), "2¹/₃");
        assert_eq!(show("unicode", -5, 12), "-⁵/₁₂");
        assert_eq!(show("unicode", 360, 7), "51³/₇");
        assert_eq!(show("unicode,mixed=false", 7, 3), "⁷/₃");
        assert_eq!(show("unicode,slash=fraction", 1, 15), "¹\u{2044}₁₅");
        assert_eq!(show("unicode,slash=division", 1, 15), "¹\u{2215}₁₅");
        assert_eq!(show("unicode,glyphs=true", 7, 3), "2⅓");
        assert_eq!(show("unicode,glyphs=true", -11, 6), "-1⅚");
        assert_eq!(show("unicode,glyphs=true", 1, 7), "⅐");
        assert_eq!(show("unicode,glyphs=true", 1, 15), "¹/₁₅");
        // The limit counts the fraction part only.
        assert_eq!(show("unicode", 229_835, 900), "≈255.372");
        // 229835/900 reduces to 45967/180.
        assert_eq!(show("unicode,fraction-digits=3", 229_835, 900), "255⁶⁷/₁₈₀");
        assert_eq!(show("unicode,fraction-digits=0", 1, 997), "¹/₉₉₇");
    }

    #[test]
    fn values_respell_their_rationals_wherever_they_sit() {
        use crate::eval::Value;
        let third = Value::Rational(q(1, 3));
        let seq = Value::Sequence(vec![
            third.clone(),
            Value::Integer(2),
            Value::Rational(q(1, 2)),
        ]);
        let parens = NumberFormat::parse("parens").unwrap();
        assert_eq!(third.to_string_with(&parens), "0.(3)");
        assert_eq!(seq.to_string_with(&parens), "(0.(3), 2, 0.5)");
        assert_eq!(seq.to_string_with(&NumberFormat::exact()), seq.to_string());
        assert_eq!(seq.to_approx_string(), "(≈0.3333333333333333, 2, 0.5)");
    }

    #[test]
    fn specs_round_trip_and_reject_what_a_style_does_not_use() {
        for spec in [
            "exact",
            "approx",
            "approx,digits=4",
            "overline,period=3",
            "parens,digits=2",
            "exact,mixed=true,fraction-digits=4",
            "unicode,mixed=false,slash=fraction,glyphs=true,fraction-digits=0",
        ] {
            let f = NumberFormat::parse(spec).unwrap();
            assert_eq!(f.to_string(), spec);
            assert_eq!(f.to_string().parse::<NumberFormat>().unwrap(), f);
        }
        assert_eq!(
            NumberFormat::parse(" unicode , mixed = true ")
                .unwrap()
                .to_string(),
            "unicode"
        );
        // Settings a style does not use do not tell formats apart.
        let mut exact = NumberFormat::exact();
        exact.period = 3;
        exact.glyphs = true;
        assert_eq!(exact, NumberFormat::exact());
        assert_eq!(exact.to_string().parse::<NumberFormat>().unwrap(), exact);
        for (spec, needle) in [
            ("decimal", "unknown number style"),
            ("approx,period=3", "does not apply to the `approx` style"),
            ("exact,glyphs=true", "does not apply"),
            ("overline,width=3", "unknown setting"),
            ("overline,period=0", "from 1 to 1000"),
            ("overline,period=1001", "from 1 to 1000"),
            ("approx,digits=+3", "from 0 to 17"),
            ("unicode,slash=wide", "`slash` must be"),
            ("unicode,mixed=maybe", "`true` or `false`"),
            ("parens,digits", "expected `key=value`"),
            ("parens,digits=2,digits=3", "set twice"),
            ("approx,digits=18", "from 0 to 17"),
        ] {
            let err = NumberFormat::parse(spec).unwrap_err();
            assert!(err.contains(needle), "{spec}: {err}");
        }
    }
}
