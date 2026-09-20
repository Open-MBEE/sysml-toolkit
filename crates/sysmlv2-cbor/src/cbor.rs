//! Minimal RFC 8949 subset the codec needs: definite-length items only,
//! canonical (shortest) heads, 64-bit floats. The output is plain
//! standard CBOR — any off-the-shelf reader can walk it; this module
//! exists so the codec carries no external dependency and stays
//! wasm-clean by construction.

use crate::{Error, ErrorKind};

const MAJOR_UINT: u8 = 0;
const MAJOR_NINT: u8 = 1;
const MAJOR_BSTR: u8 = 2;
const MAJOR_TSTR: u8 = 3;
const MAJOR_ARRAY: u8 = 4;
const MAJOR_MAP: u8 = 5;
const MAJOR_TAG: u8 = 6;
const MAJOR_SIMPLE: u8 = 7;

#[derive(Default)]
pub struct Writer {
    buf: Vec<u8>,
}

impl Writer {
    /// A writer opened with the RFC 9277 payload magic already
    /// emitted: tag 55799 wrapping application tag `0x24533243`
    /// ("$S2C"); the body written next is the tags' content, so the
    /// whole payload stays one valid CBOR item. Room for roughly
    /// `elements` element records is reserved up front — an id-table
    /// entry is 17 bytes and a record's frame about as much again — so
    /// a whole model never starts from nothing and walks the doubling
    /// sequence.
    pub fn with_magic_for(elements: usize) -> Self {
        let mut w = Self {
            buf: Vec::with_capacity(crate::MAGIC.len() + elements.saturating_mul(48)),
        };
        w.buf.extend_from_slice(crate::MAGIC);
        w
    }

    pub fn into_bytes(self) -> Vec<u8> {
        self.buf
    }

    /// Append pre-encoded CBOR items (candidate encodings compared in
    /// a scratch writer, then adopted verbatim).
    pub fn raw(&mut self, bytes: &[u8]) {
        self.buf.extend_from_slice(bytes);
    }

    // Each arm narrows `arg` to the width its own range bound already
    // proves exact — that is what picking the shortest head means.
    #[allow(clippy::cast_possible_truncation)]
    fn head(&mut self, major: u8, arg: u64) {
        let m = major << 5;
        match arg {
            0..=23 => self.buf.push(m | arg as u8),
            24..=0xFF => {
                self.buf.push(m | 24);
                self.buf.push(arg as u8);
            }
            0x100..=0xFFFF => {
                self.buf.push(m | 25);
                self.buf.extend_from_slice(&(arg as u16).to_be_bytes());
            }
            0x1_0000..=0xFFFF_FFFF => {
                self.buf.push(m | 26);
                self.buf.extend_from_slice(&(arg as u32).to_be_bytes());
            }
            _ => {
                self.buf.push(m | 27);
                self.buf.extend_from_slice(&arg.to_be_bytes());
            }
        }
    }

    pub fn uint(&mut self, v: u64) {
        self.head(MAJOR_UINT, v);
    }

    /// Any integer; negatives use major type 1.
    pub fn int(&mut self, v: i64) {
        if v >= 0 {
            self.head(MAJOR_UINT, v as u64);
        } else {
            self.head(MAJOR_NINT, !(v as u64));
        }
    }

    pub fn bstr(&mut self, b: &[u8]) {
        self.head(MAJOR_BSTR, b.len() as u64);
        self.buf.extend_from_slice(b);
    }

    pub fn tstr(&mut self, s: &str) {
        self.head(MAJOR_TSTR, s.len() as u64);
        self.buf.extend_from_slice(s.as_bytes());
    }

    pub fn array(&mut self, len: usize) {
        self.head(MAJOR_ARRAY, len as u64);
    }

    pub fn map(&mut self, len: usize) {
        self.head(MAJOR_MAP, len as u64);
    }

    pub fn bool(&mut self, v: bool) {
        self.buf.push(0xF4 | v as u8);
    }

    pub fn null(&mut self) {
        self.buf.push(0xF6);
    }

    pub fn f64(&mut self, v: f64) {
        self.buf.push(0xFB);
        self.buf.extend_from_slice(&v.to_be_bytes());
    }
}

/// One decoded item head. Container heads carry their length; the
/// caller walks the contained items.
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum Head {
    Uint(u64),
    /// Negative integer `-1 - arg`.
    NInt(u64),
    Bstr(usize),
    Tstr(usize),
    Array(usize),
    Map(usize),
    False,
    True,
    Null,
    F64(f64),
}

pub struct Reader<'a> {
    buf: &'a [u8],
    pos: usize,
}

impl<'a> Reader<'a> {
    pub fn new(buf: &'a [u8]) -> Self {
        Self { buf, pos: 0 }
    }

    pub fn done(&self) -> bool {
        self.pos == self.buf.len()
    }

    /// Bytes left — the upper bound on any remaining item count, used
    /// to reject adversarial length headers before allocating.
    pub fn remaining(&self) -> usize {
        self.buf.len() - self.pos
    }

    fn byte(&mut self) -> Result<u8, Error> {
        let b = *self
            .buf
            .get(self.pos)
            .ok_or_else(|| Error::of(ErrorKind::Truncated, "truncated payload"))?;
        self.pos += 1;
        Ok(b)
    }

    pub fn take(&mut self, n: usize) -> Result<&'a [u8], Error> {
        let end = self
            .pos
            .checked_add(n)
            .filter(|&e| e <= self.buf.len())
            .ok_or_else(|| Error::of(ErrorKind::Truncated, "truncated payload"))?;
        let s = &self.buf[self.pos..end];
        self.pos = end;
        Ok(s)
    }

    fn arg(&mut self, ai: u8) -> Result<u64, Error> {
        Ok(match ai {
            0..=23 => ai as u64,
            24 => self.byte()? as u64,
            25 => u16::from_be_bytes(self.take(2)?.try_into().unwrap()) as u64,
            26 => u32::from_be_bytes(self.take(4)?.try_into().unwrap()) as u64,
            27 => u64::from_be_bytes(self.take(8)?.try_into().unwrap()),
            _ => return Err(Error::new("indefinite or reserved length")),
        })
    }

    fn len(arg: u64) -> Result<usize, Error> {
        usize::try_from(arg).map_err(|_| Error::new("length overflow"))
    }

    /// Narrow an already-read wire integer to an in-memory index or
    /// position. Wire integers are 64-bit and `usize` is 32 bits on
    /// the wasm targets, so a value that cannot address memory here is
    /// a malformed payload rather than a silently wrapped index.
    pub fn index_of(arg: u64) -> Result<usize, Error> {
        usize::try_from(arg).map_err(|_| Error::new(format!("wire index {arg} out of range")))
    }

    /// Read an unsigned wire integer as an index or position
    /// ([`Self::index_of`]).
    pub fn index(&mut self) -> Result<usize, Error> {
        Self::index_of(self.uint()?)
    }

    pub fn head(&mut self) -> Result<Head, Error> {
        let b = self.byte()?;
        let (major, ai) = (b >> 5, b & 0x1F);
        Ok(match major {
            MAJOR_UINT => Head::Uint(self.arg(ai)?),
            MAJOR_NINT => Head::NInt(self.arg(ai)?),
            MAJOR_BSTR => Head::Bstr(Self::len(self.arg(ai)?)?),
            MAJOR_TSTR => Head::Tstr(Self::len(self.arg(ai)?)?),
            MAJOR_ARRAY => Head::Array(Self::len(self.arg(ai)?)?),
            MAJOR_MAP => Head::Map(Self::len(self.arg(ai)?)?),
            MAJOR_TAG => return Err(Error::new("unexpected tag")),
            MAJOR_SIMPLE => match ai {
                20 => Head::False,
                21 => Head::True,
                22 => Head::Null,
                27 => Head::F64(f64::from_be_bytes(self.take(8)?.try_into().unwrap())),
                _ => return Err(Error::new("unsupported simple/float value")),
            },
            _ => unreachable!(),
        })
    }

    pub fn uint(&mut self) -> Result<u64, Error> {
        match self.head()? {
            Head::Uint(v) => Ok(v),
            _ => Err(Error::new("expected unsigned integer")),
        }
    }

    pub fn array(&mut self) -> Result<usize, Error> {
        match self.head()? {
            Head::Array(n) => Ok(n),
            _ => Err(Error::new("expected array")),
        }
    }

    pub fn bstr(&mut self, expect_len: usize) -> Result<&'a [u8], Error> {
        match self.head()? {
            Head::Bstr(n) if n == expect_len => self.take(n),
            Head::Bstr(_) => Err(Error::new("unexpected byte-string length")),
            _ => Err(Error::new("expected byte string")),
        }
    }

    pub fn tstr_body(&mut self, n: usize) -> Result<&'a str, Error> {
        std::str::from_utf8(self.take(n)?).map_err(|_| Error::new("invalid UTF-8 text"))
    }

    /// Skip `count` complete items, containers included, without
    /// materializing anything — the structural walk behind
    /// [`crate::describe`]. Iterative (a pending counter, not
    /// recursion), and every step consumes at least one byte, so
    /// adversarial nesting terminates at the truncation error.
    /// Read a map keyed by strictly ascending in-memory indices — the
    /// shape every exception, owner and units section shares. The
    /// header is gated against the payload before anything is
    /// allocated (`per_entry` is the fewest bytes one entry can
    /// occupy), each key is narrowed and checked against its
    /// predecessor, and `value` reads the value with the reader
    /// positioned on it. `what` names the section in the three errors
    /// this can raise.
    pub fn ascending_map<T>(
        &mut self,
        what: &str,
        per_entry: usize,
        mut value: impl FnMut(&mut Self) -> Result<T, Error>,
    ) -> Result<Vec<(usize, T)>, Error> {
        let n = match self.head()? {
            Head::Map(n) if n <= self.remaining() / per_entry => n,
            Head::Map(_) => return Err(Error::new(format!("{what} longer than payload"))),
            _ => return Err(Error::new(format!("{what} expected"))),
        };
        let mut out = Vec::with_capacity(n);
        let mut prev: Option<usize> = None;
        for _ in 0..n {
            let key = self.index()?;
            if prev.is_some_and(|p| key <= p) {
                return Err(Error::new(format!("{what} indices not ascending")));
            }
            prev = Some(key);
            let v = value(self)?;
            out.push((key, v));
        }
        Ok(out)
    }

    pub fn skip_items(&mut self, count: u64) -> Result<(), Error> {
        let mut pending = count;
        while pending > 0 {
            pending -= 1;
            match self.head()? {
                Head::Uint(_)
                | Head::NInt(_)
                | Head::False
                | Head::True
                | Head::Null
                | Head::F64(_) => {}
                Head::Bstr(n) | Head::Tstr(n) => {
                    self.take(n)?;
                }
                Head::Array(n) => {
                    pending = pending
                        .checked_add(n as u64)
                        .ok_or_else(|| Error::new("nesting overflow"))?;
                }
                Head::Map(n) => {
                    pending = pending
                        .checked_add(n as u64)
                        .and_then(|p| p.checked_add(n as u64))
                        .ok_or_else(|| Error::new("nesting overflow"))?;
                }
            }
        }
        Ok(())
    }
}
