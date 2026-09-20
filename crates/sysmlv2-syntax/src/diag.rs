//! Diagnostics reported by the lexer and parser.

use crate::span::Span;
use std::fmt;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum Severity {
    Error,
    Warning,
}

/// A single problem found in the source text.
///
/// The lexer and parser are error-tolerant: they record diagnostics and keep
/// going, so one pass reports as many problems as possible.
///
/// Non-exhaustive: a finding may come to carry more about itself, as it
/// came to carry [`Diagnostic::code`]. Build one with [`Diagnostic::error`]
/// or [`Diagnostic::warning`].
///
/// Two diagnostics are equal when they report the same thing — the same
/// severity, place and message. The rule code is derived state that a
/// serialization round trip does not carry (see the field), so counting
/// it in equality would make a value unequal to its own round trip.
#[derive(Clone, Debug, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[non_exhaustive]
pub struct Diagnostic {
    pub severity: Severity,
    pub span: Span,
    pub message: String,
    /// Identifier of the named rule this finding reports, when it reports
    /// one — so a consumer reads a field instead of parsing the message.
    /// Derived state: it is not carried across a serialization boundary.
    #[cfg_attr(feature = "serde", serde(skip))]
    pub code: Option<&'static str>,
}

impl PartialEq for Diagnostic {
    fn eq(&self, other: &Self) -> bool {
        self.severity == other.severity && self.span == other.span && self.message == other.message
    }
}

impl Diagnostic {
    pub fn error(span: Span, message: impl Into<String>) -> Self {
        Diagnostic {
            severity: Severity::Error,
            span,
            message: message.into(),
            code: None,
        }
    }

    pub fn warning(span: Span, message: impl Into<String>) -> Self {
        Diagnostic {
            severity: Severity::Warning,
            span,
            message: message.into(),
            code: None,
        }
    }

    /// The same finding, reporting the rule `code` names.
    #[must_use]
    pub fn with_code(mut self, code: &'static str) -> Self {
        self.code = Some(code);
        self
    }
}

impl fmt::Display for Diagnostic {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let sev = match self.severity {
            Severity::Error => "error",
            Severity::Warning => "warning",
        };
        write!(f, "{sev}: {} at {:?}", self.message, self.span)
    }
}

/// The diagnostics that made an operation fail, as a single error value.
///
/// Dereferences to the slice, so the individual diagnostics stay reachable
/// (`first`, `len`, iteration, indexing); `Display` lists them one per
/// line; and it is a [`std::error::Error`], so a caller can propagate it
/// with `?` instead of having to unpack a vector by hand.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Diagnostics(Vec<Diagnostic>);

impl Diagnostics {
    /// The diagnostics, giving up the wrapper.
    #[must_use]
    pub fn into_vec(self) -> Vec<Diagnostic> {
        self.0
    }
}

impl From<Vec<Diagnostic>> for Diagnostics {
    fn from(diagnostics: Vec<Diagnostic>) -> Self {
        Diagnostics(diagnostics)
    }
}

impl From<Diagnostics> for Vec<Diagnostic> {
    fn from(diagnostics: Diagnostics) -> Self {
        diagnostics.0
    }
}

impl FromIterator<Diagnostic> for Diagnostics {
    fn from_iter<I: IntoIterator<Item = Diagnostic>>(iter: I) -> Self {
        Diagnostics(iter.into_iter().collect())
    }
}

impl std::ops::Deref for Diagnostics {
    type Target = [Diagnostic];

    fn deref(&self) -> &[Diagnostic] {
        &self.0
    }
}

impl IntoIterator for Diagnostics {
    type Item = Diagnostic;
    type IntoIter = std::vec::IntoIter<Diagnostic>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

impl<'a> IntoIterator for &'a Diagnostics {
    type Item = &'a Diagnostic;
    type IntoIter = std::slice::Iter<'a, Diagnostic>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.iter()
    }
}

impl fmt::Display for Diagnostics {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for (i, d) in self.0.iter().enumerate() {
            if i > 0 {
                writeln!(f)?;
            }
            write!(f, "{d}")?;
        }
        Ok(())
    }
}

impl std::error::Error for Diagnostics {}
