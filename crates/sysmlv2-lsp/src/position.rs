//! Byte-offset ⇄ LSP position conversion for one document text.
//!
//! Every span in the toolkit is a byte range; LSP positions are
//! line/character pairs whose character unit is negotiated at initialize
//! time. UTF-16 is the protocol's mandatory default; UTF-8 (LSP 3.17
//! `positionEncoding`) makes characters plain byte columns.

use lsp_types::{Position, Range};
use sysmlv2_parser::span::Span;

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
    pub fn new(text: &'a str, encoding: Encoding) -> Self {
        let mut line_starts = vec![0u32];
        for (i, b) in text.bytes().enumerate() {
            if b == b'\n' {
                line_starts.push(i as u32 + 1);
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
    pub fn position(&self, offset: u32) -> Position {
        let offset = offset.min(self.text.len() as u32);
        let line = self.line_of(offset);
        let start = self.line_starts[line] as usize;
        let character = match self.encoding {
            Encoding::Utf8 => offset - start as u32,
            Encoding::Utf16 => self.text[start..offset as usize]
                .chars()
                .map(|c| c.len_utf16() as u32)
                .sum(),
        };
        Position {
            line: line as u32,
            character,
        }
    }

    /// Convert an LSP position to a byte offset, clamping past-the-end
    /// lines and columns (clients may send positions beyond the text).
    pub fn offset(&self, pos: Position) -> u32 {
        let Some(&start) = self.line_starts.get(pos.line as usize) else {
            return self.text.len() as u32;
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
                return start + i as u32;
            }
            units += match self.encoding {
                Encoding::Utf8 => c.len_utf8() as u32,
                Encoding::Utf16 => c.len_utf16() as u32,
            };
        }
        line_end as u32
    }

    pub fn range(&self, span: Span) -> Range {
        Range {
            start: self.position(span.start),
            end: self.position(span.end),
        }
    }

    /// The range covering the whole document (for full-text edits).
    pub fn full_range(&self) -> Range {
        Range {
            start: Position {
                line: 0,
                character: 0,
            },
            end: self.position(self.text.len() as u32),
        }
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
            TEXT.len() as u32
        );
    }

    #[test]
    fn round_trips_char_boundaries() {
        for enc in [Encoding::Utf8, Encoding::Utf16] {
            let m = Mapper::new(TEXT, enc);
            for (i, _) in TEXT.char_indices() {
                let off = i as u32;
                assert_eq!(m.offset(m.position(off)), off, "offset {off} {enc:?}");
            }
        }
    }
}
