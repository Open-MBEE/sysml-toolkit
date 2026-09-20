//! Byte-offset spans and line/column mapping.

use std::fmt;

/// A byte offset as a span coordinate.
///
/// Span coordinates are 32-bit, so a source text longer than `u32::MAX`
/// bytes cannot be addressed by one. Clamping keeps the spans of a text
/// that long ordered and in range instead of wrapping them around.
pub(crate) fn clamp_offset(byte: usize) -> u32 {
    u32::try_from(byte).unwrap_or(u32::MAX)
}

/// A half-open byte range `[start, end)` into a source text.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Default)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Span {
    pub start: u32,
    pub end: u32,
}

impl Span {
    #[must_use]
    pub fn new(start: u32, end: u32) -> Self {
        debug_assert!(start <= end);
        Span { start, end }
    }

    #[must_use]
    pub fn len(&self) -> u32 {
        self.end - self.start
    }

    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.start == self.end
    }

    /// The smallest span covering both `self` and `other`.
    #[must_use]
    pub fn join(self, other: Span) -> Span {
        Span {
            start: self.start.min(other.start),
            end: self.end.max(other.end),
        }
    }

    #[must_use]
    pub fn slice<'a>(&self, text: &'a str) -> &'a str {
        &text[self.start as usize..self.end as usize]
    }
}

impl fmt::Debug for Span {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}..{}", self.start, self.end)
    }
}

/// 1-based line and column position, computed on demand from a span offset.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct LineCol {
    pub line: u32,
    pub col: u32,
}

/// Maps byte offsets to line/column positions for one source text.
#[derive(Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct LineIndex {
    /// Byte offset of the start of each line.
    line_starts: Vec<u32>,
}

impl LineIndex {
    #[must_use]
    pub fn new(text: &str) -> Self {
        let mut line_starts = vec![0u32];
        for (i, b) in text.bytes().enumerate() {
            if b == b'\n' {
                line_starts.push(clamp_offset(i).saturating_add(1));
            }
        }
        LineIndex { line_starts }
    }

    #[must_use]
    pub fn line_col(&self, offset: u32) -> LineCol {
        let line = match self.line_starts.binary_search(&offset) {
            Ok(l) => l,
            Err(l) => l - 1,
        };
        LineCol {
            line: clamp_offset(line).saturating_add(1),
            col: offset - self.line_starts[line] + 1,
        }
    }
}
