//! CBOR binary encoding of the compact JSON interchange form (the flat
//! element array of KerML 10.4.4).
//!
//! The codec is a leaf at the serialization boundary — `Value ↔ bytes` —
//! driven entirely by the generated tables in
//! [`sysmlv2_model::cbor_tables`]: the concrete-metaclass type index,
//! per-metaclass field ordinals with value kinds and defaults, and the
//! closed enum vocabularies. [`to_compact_cbor`] and
//! [`from_compact_cbor`] round-trip Value-identically; the byte output
//! is a pure function of the input (definite lengths, shortest heads,
//! canonical field/type/table ordering) and plain RFC 8949 — any
//! off-the-shelf CBOR reader can walk it.

// Wire integers are 64-bit and `usize` is not: a payload read on a
// 32-bit target (the wasm hosts) must refuse an out-of-range index
// rather than wrap into a different one. Every narrowing cast in the
// crate is therefore either a checked conversion or carries its own
// justification.
#![warn(clippy::cast_possible_truncation)]

mod canonical;
mod cbor;
mod decode;
mod delta;
mod describe;
mod encode;
pub mod index;
pub mod resolver;

pub use canonical::{canonicalize_compact, graph_normalize, graph_normalize_compact};
pub use decode::{
    from_cbor, from_cbor_with, from_cbor_with_units, from_compact_cbor, from_compact_cbor_elided,
    from_compact_cbor_units, from_full_cbor,
};
pub use delta::{
    ApplyReport, Claim, DeltaOptions, FLAG_DELTA, FLAG_DELTA_PORTABLE, apply_delta_cbor,
    apply_delta_cbor_lenient, apply_delta_cbor_report, apply_delta_cbor_report_with,
    apply_delta_cbor_with, delta_canonical, delta_compact_cbor, delta_compact_cbor_elided,
    empty_base_digest, rebase_ids, state_digest,
};
pub use describe::describe;
pub use encode::{
    FLAG_ELIDE_IDS, FLAG_EXPLICIT_IDS, FLAG_FULL_FORM, FLAG_IMPLIED_OWNERS, FLAG_UNIT_PATHS,
    to_compact_cbor, to_compact_cbor_elided, to_compact_cbor_elided_with_units,
    to_compact_cbor_with_units, to_compact_cbor_with_units_explicit, to_full_cbor,
    to_full_cbor_with_units,
};
pub use sysmlv2_model::cbor_tables as tables;

use std::fmt;

/// Every payload opens with this fixed eight-byte prefix — the
/// RFC 9277 "tag-wrapped" file magic: the self-described-CBOR tag
/// 55799 (`D9 D9F7`) wrapping application tag `0x24533243`
/// (`DA 24 53 32 43`), whose big-endian bytes spell **`$S2C`**
/// ("SysML v2 CBOR"). Files and streams are recognizable by prefix
/// alone *and* remain a single valid CBOR item from byte 0 — the
/// body array is the tags' content. Conventional file extension:
/// `.s2c`; media type `application/vnd.sysmlv2.s2c+cbor`
/// (see `CBOR.md`).
pub const MAGIC: &[u8; 8] = &[0xD9, 0xD9, 0xF7, 0xDA, 0x24, 0x53, 0x32, 0x43];

/// Wire-**layout** generation: the array shapes, presence encoding,
/// reference index spaces, and delta framing. Decoders refuse a
/// mismatch unconditionally. One of the three version axes in the
/// header word (`layout u8 · tables u16 · scheme u8 · flags u8`);
/// the others are [`tables::CBOR_TABLES_VERSION`] (the generated
/// metamodel tables) and [`ID_SCHEME_VERSION`].
pub const LAYOUT_VERSION: u8 = 1;

/// The **id-derivation scheme** stamp (the graph-derived derivation
/// of `IDS.md`). Consulted only where derivation is actually in play
/// — id-elided payloads, snapshot or delta — so a scheme change never
/// blocks decoding payloads that carry their ids explicitly.
pub const ID_SCHEME_VERSION: u8 = 1;

pub(crate) fn strip_magic(bytes: &[u8]) -> Result<&[u8], Error> {
    match bytes.strip_prefix(MAGIC) {
        Some(rest) => Ok(rest),
        None => Err(Error::of(
            ErrorKind::MissingMagic,
            "not an s2c payload (missing the RFC 9277 magic — tag 55799 \
             wrapping tag 0x24533243, \"$S2C\")",
        )),
    }
}

/// What a codec error *is*, for callers that act on the classes
/// differently — refetch a base, fetch a resolver, route to another
/// entry point, or give up on the bytes. The [`fmt::Display`] text
/// stays the explanation; this is the decision.
///
/// Non-exhaustive: later wire generations will distinguish more.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum ErrorKind {
    /// The bytes do not open with the payload magic — not an s2c
    /// payload at all.
    MissingMagic,
    /// A version axis (wire layout, generated tables, id-derivation
    /// scheme, base-index or resolver artifact) this build does not
    /// implement.
    UnsupportedVersion,
    /// An id-elided payload reached an entry point that carries no
    /// name resolver.
    NeedsResolver,
    /// A well-formed payload of the wrong kind for this entry point
    /// (a delta to a snapshot decoder, a full form to the compact
    /// one, and so on) — the message names the one to use.
    WrongForm,
    /// The held base is not the one the delta names.
    BaseDigestMismatch,
    /// The payload ends inside an item.
    Truncated,
    /// Anything else refused on the way in or out: a structure the
    /// wire format does not allow, or a `Value` outside the compact
    /// interchange shape.
    Malformed,
}

/// Codec error: malformed input on decode, or a `Value` outside the
/// compact interchange shape on encode. [`Error::kind`] classifies it;
/// the [`fmt::Display`] text explains it.
#[derive(Debug)]
pub struct Error {
    kind: ErrorKind,
    message: String,
}

impl Error {
    fn new(message: impl Into<String>) -> Self {
        Self::of(ErrorKind::Malformed, message)
    }

    fn of(kind: ErrorKind, message: impl Into<String>) -> Self {
        Self {
            kind,
            message: message.into(),
        }
    }

    /// The class this error falls in.
    #[must_use]
    pub fn kind(&self) -> ErrorKind {
        self.kind
    }
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.message)
    }
}

impl std::error::Error for Error {}

/// Wire type code for a metaclass name, if it is a concrete metaclass.
#[must_use]
pub fn type_code(name: &str) -> Option<u16> {
    tables::METACLASS_FIELDS
        .binary_search_by(|(n, _)| n.cmp(&name))
        .ok()
        .and_then(|i| u16::try_from(i).ok())
}

/// Field table for a wire type code.
#[must_use]
pub fn fields_of(code: u16) -> Option<&'static [tables::CborField]> {
    tables::METACLASS_FIELDS.get(code as usize).map(|(_, f)| *f)
}

/// Wire ordinal of `prop` within a field table.
#[must_use]
pub fn ordinal(fields: &'static [tables::CborField], prop: &str) -> Option<u8> {
    fields
        .binary_search_by(|(n, _, _, _)| n.cmp(&prop))
        .ok()
        .and_then(|i| u8::try_from(i).ok())
}
