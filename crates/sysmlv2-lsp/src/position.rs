//! Byte-offset ⇄ LSP position conversion for one document text.
//!
//! Every span in the toolkit is a byte range; LSP positions are
//! line/character pairs whose character unit is negotiated at initialize
//! time. UTF-16 is the protocol's mandatory default; UTF-8 (LSP 3.17
//! `positionEncoding`) makes characters plain byte columns.

use lsp_types::{Position, Range};
use std::collections::HashMap;
use std::collections::hash_map::Entry;
use std::hash::Hash;
use sysmlv2_parser::span::Span;

/// A count measured inside one document — a byte offset or length, a
/// line number, the width of one character — as the `u32` every span
/// in the toolkit is measured in. A unit too wide to address in 32
/// bits has no spans to answer with in the first place, so the
/// conversion is total in practice. A document that somehow got here
/// anyway panics rather than answering a silently wrapped position —
/// the request loop turns that into one failed request and a message,
/// which is the containment this relies on.
pub(crate) fn offset32(n: usize) -> u32 {
    u32::try_from(n).expect("a model unit is addressed in 32 bits")
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Encoding {
    Utf8,
    Utf16,
}

/// Line-start table over one text, converting under one [`Encoding`].
pub struct Mapper<'a> {
    text: &'a str,
    /// Byte offset of the start of each line (line 0 starts at 0).
    line_starts: Vec<u32>,
    encoding: Encoding,
}

impl<'a> Mapper<'a> {
    #[must_use]
    pub fn new(text: &'a str, encoding: Encoding) -> Self {
        let mut line_starts = vec![0u32];
        for (i, b) in text.bytes().enumerate() {
            if b == b'\n' {
                line_starts.push(offset32(i) + 1);
            }
        }
        Mapper {
            text,
            line_starts,
            encoding,
        }
    }

    /// The 0-based line containing `offset`.
    fn line_of(&self, offset: u32) -> usize {
        self.line_starts.partition_point(|&s| s <= offset) - 1
    }

    /// Convert a byte offset (clamped to the text) to an LSP position.
    #[must_use]
    pub fn position(&self, offset: u32) -> Position {
        let offset = offset.min(offset32(self.text.len()));
        let line = self.line_of(offset);
        let start = self.line_starts[line] as usize;
        let character = match self.encoding {
            Encoding::Utf8 => offset - offset32(start),
            Encoding::Utf16 => self.text[start..offset as usize]
                .chars()
                .map(|c| offset32(c.len_utf16()))
                .sum(),
        };
        Position {
            line: offset32(line),
            character,
        }
    }

    /// Convert an LSP position to a byte offset, clamping past-the-end
    /// lines and columns (clients may send positions beyond the text).
    #[must_use]
    pub fn offset(&self, pos: Position) -> u32 {
        let Some(&start) = self.line_starts.get(pos.line as usize) else {
            return offset32(self.text.len());
        };
        let line_end = self
            .line_starts
            .get(pos.line as usize + 1)
            .map(|&next| (next - 1) as usize) // before the '\n'
            .unwrap_or(self.text.len());
        let line = &self.text[start as usize..line_end];
        let mut units = 0u32;
        for (i, c) in line.char_indices() {
            if units >= pos.character {
                return start + offset32(i);
            }
            units += match self.encoding {
                Encoding::Utf8 => offset32(c.len_utf8()),
                Encoding::Utf16 => offset32(c.len_utf16()),
            };
        }
        offset32(line_end)
    }

    #[must_use]
    pub fn range(&self, span: Span) -> Range {
        Range {
            start: self.position(span.start),
            end: self.position(span.end),
        }
    }

    /// The range covering the whole document (for full-text edits).
    #[must_use]
    pub fn full_range(&self) -> Range {
        Range {
            start: Position {
                line: 0,
                character: 0,
            },
            end: self.position(offset32(self.text.len())),
        }
    }
}

/// Line indexes over a set of units, each built on first use and shared
/// by every span mapped afterwards. A workspace cycle or a code-action
/// request maps many spans per unit; building the index anew per span
/// walks the whole text each time, which on a large model with
/// thousands of findings costs findings × text bytes.
pub(crate) struct UnitMappers<'a, K> {
    encoding: Encoding,
    built: HashMap<K, (&'a str, Mapper<'a>)>,
}

impl<'a, K: Hash + Eq> UnitMappers<'a, K> {
    pub(crate) fn new(encoding: Encoding) -> Self {
        UnitMappers {
            encoding,
            built: HashMap::new(),
        }
    }

    /// The name and line index of the unit under `key`, built from
    /// `unit()` — its `(name, text)` — on first use; `None` when
    /// `unit()` finds nothing.
    pub(crate) fn get(
        &mut self,
        key: K,
        unit: impl FnOnce() -> Option<(&'a str, &'a str)>,
    ) -> Option<(&'a str, &Mapper<'a>)> {
        let slot = match self.built.entry(key) {
            Entry::Occupied(o) => o.into_mut(),
            Entry::Vacant(v) => {
                let (name, text) = unit()?;
                v.insert((name, Mapper::new(text, self.encoding)))
            }
        };
        Some((slot.0, &slot.1))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const TEXT: &str = "ab😀cd\nxyz\n";

    #[test]
    fn utf16_counts_surrogate_pairs() {
        let m = Mapper::new(TEXT, Encoding::Utf16);
        // "😀" is 4 bytes / 2 UTF-16 units, starting at byte 2.
        assert_eq!(
            m.position(2),
            Position {
                line: 0,
                character: 2
            }
        );
        assert_eq!(
            m.position(6),
            Position {
                line: 0,
                character: 4
            }
        );
        assert_eq!(
            m.position(8),
            Position {
                line: 0,
                character: 6
            }
        );
        assert_eq!(
            m.position(9),
            Position {
                line: 1,
                character: 0
            }
        );
        assert_eq!(
            m.offset(Position {
                line: 0,
                character: 4
            }),
            6
        );
        assert_eq!(
            m.offset(Position {
                line: 1,
                character: 1
            }),
            10
        );
    }

    #[test]
    fn utf8_counts_bytes() {
        let m = Mapper::new(TEXT, Encoding::Utf8);
        assert_eq!(
            m.position(6),
            Position {
                line: 0,
                character: 6
            }
        );
        assert_eq!(
            m.offset(Position {
                line: 0,
                character: 6
            }),
            6
        );
    }

    #[test]
    fn clamps_past_the_end() {
        let m = Mapper::new(TEXT, Encoding::Utf16);
        assert_eq!(
            m.position(999),
            Position {
                line: 2,
                character: 0
            }
        );
        // Past-the-end column clamps to the line end (before the newline).
        assert_eq!(
            m.offset(Position {
                line: 1,
                character: 99
            }),
            12
        );
        assert_eq!(
            m.offset(Position {
                line: 99,
                character: 0
            }),
            offset32(TEXT.len())
        );
    }

    #[test]
    fn round_trips_char_boundaries() {
        for enc in [Encoding::Utf8, Encoding::Utf16] {
            let m = Mapper::new(TEXT, enc);
            for (i, _) in TEXT.char_indices() {
                let off = offset32(i);
                assert_eq!(m.offset(m.position(off)), off, "offset {off} {enc:?}");
            }
        }
    }

    /// Every span of a unit maps through one line index: the second and
    /// later lookups of a unit reuse the index the first built, and each
    /// unit still maps against its own text.
    #[test]
    fn unit_mappers_build_one_index_per_unit() {
        let built = std::cell::Cell::new(0u32);
        let mut mappers: UnitMappers<'static, usize> = UnitMappers::new(Encoding::Utf8);
        let lookup = |unit: usize| {
            built.set(built.get() + 1);
            match unit {
                0 => Some(("a", "one\ntwo\n")),
                1 => Some(("b", "\n\nthree\n")),
                _ => None,
            }
        };
        let at = |mappers: &mut UnitMappers<'static, usize>,
                  unit: usize,
                  offset: u32|
         -> Option<(&'static str, u32)> {
            mappers
                .get(unit, || lookup(unit))
                .map(|(name, m)| (name, m.position(offset).line))
        };
        assert_eq!(at(&mut mappers, 0, 0), Some(("a", 0)));
        assert_eq!(at(&mut mappers, 0, 4), Some(("a", 1)));
        assert_eq!(at(&mut mappers, 1, 4), Some(("b", 2)));
        assert_eq!(at(&mut mappers, 1, 0), Some(("b", 0)));
        assert_eq!(at(&mut mappers, 0, 4), Some(("a", 1)));
        assert_eq!(built.get(), 2, "one index per unit, however many spans");
        // A unit the session does not hold yields nothing, and is not
        // remembered as an index.
        assert_eq!(at(&mut mappers, 2, 0), None);
        assert_eq!(at(&mut mappers, 2, 0), None);
        assert_eq!(built.get(), 4);
    }
}
