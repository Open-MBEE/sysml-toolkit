//! Span-splice transformation engine for SysML v2 / KerML textual models.
//!
//! Navigate semantically, edit syntactically: a [`Session`] holds the
//! source texts and their resolved model; an [`EditBuilder`] turns
//! structured edits (rename, set value, insert, remove, retarget) into
//! **minimal text splices** at resolver-recorded spans, so everything the
//! edit does not touch is preserved byte for byte — notes, formatting,
//! the lot. [`EditBuilder::commit`] applies the batch, reparses,
//! re-resolves, and verifies **semantic identity**: every reference site
//! the edit did not explicitly change must resolve to the same element
//! (compared by qualified name, mapped through the commit's renames).
//! On any failure the session is left untouched.
//!
//! The parser stays the only authority on syntax — new fragments are
//! validated by parsing, and a commit whose result does not reparse
//! cleanly is rejected wholesale.

pub mod eligibility;
pub mod projection;

use std::collections::{BTreeMap, HashMap, HashSet};
use std::fmt;
use std::path::{Path, PathBuf};

pub use sysmlv2_model::json::{ElementRef, RefSite, ResolvedModel, UnresolvedReference};
pub use sysmlv2_model::model::Model as ModelHandle;

use sysmlv2_model::libcache;
use sysmlv2_model::model::Model;
use sysmlv2_syntax::ast::escape_name;
use sysmlv2_syntax::diag::Diagnostic;
pub use sysmlv2_syntax::diag::Severity;
use sysmlv2_syntax::lexer::{tokenize, unescape};
use sysmlv2_syntax::parser::{parse_expression, parse_kerml_source, parse_source};
pub use sysmlv2_syntax::print::Indent;
use sysmlv2_syntax::print::{indent_unit, reindent_member_text};
use sysmlv2_syntax::span::LineIndex;
pub use sysmlv2_syntax::span::Span;
use sysmlv2_syntax::token::TokenKind;
use uuid::Uuid;

/// The name a spelled token denotes: quoted spellings unescape, plain
/// spellings are themselves.
fn decode_name(spelled: &str) -> String {
    if spelled.starts_with('\'') {
        unescape(spelled)
    } else {
        spelled.to_string()
    }
}

/// Spell `name` as a source token: [`escape_name`] quoting for
/// non-identifier characters, plus quotes for words reserved in *either*
/// dialect (a rename batch can touch `.sysml` and `.kerml` units at
/// once, and a quoted spelling is legal everywhere) —
/// [`sysmlv2_syntax::name::spell_name_in`] without a dialect.
#[must_use]
pub fn spell_name(name: &str) -> String {
    sysmlv2_syntax::name::spell_name_in(None, name)
}

/// Stable identity for one unresolved reference across a semantics-preserving
/// edit. The spelling alone is insufficient: removing `Missing` at one site
/// while introducing the same spelling at another must still be a refusal.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
struct UnresolvedSiteKey {
    unit: usize,
    anchor: String,
    owner_metaclass: &'static str,
    relative_span: Span,
    spelling: String,
}

fn unresolved_site_key(
    resolved: &mut ResolvedModel,
    reference: &UnresolvedReference,
    map_qn: &dyn Fn(&str) -> String,
) -> UnresolvedSiteKey {
    // RefSite/unresolved owners are often property-carrying relationships.
    // Climb to the nearest source member so offsets remain stable when edits
    // elsewhere in the unit shift absolute byte positions.
    let mut cursor = Some(reference.owner);
    let mut source_anchor = None;
    while let Some(e) = cursor {
        if let Some((unit, extent)) = resolved.member_extent(e) {
            source_anchor = Some((e, unit, extent));
            break;
        }
        cursor = resolved.owner(e);
    }

    let (unit, anchor, relative_span) = match source_anchor {
        Some((e, unit, extent)) => {
            let anchor = resolved
                .element_qualified_name(e)
                .map(|qn| map_qn(&qn))
                .unwrap_or_else(|| format!("<{}>", resolved.element_type(e)));
            (
                unit,
                anchor,
                Span::new(
                    reference.span.start.saturating_sub(extent.start),
                    reference.span.end.saturating_sub(extent.start),
                ),
            )
        }
        None => (
            reference.unit,
            format!("<{}>", resolved.element_type(reference.owner)),
            reference.span,
        ),
    };

    UnresolvedSiteKey {
        unit,
        anchor,
        owner_metaclass: resolved.element_type(reference.owner),
        relative_span,
        spelling: reference.spelling.clone(),
    }
}

/// Stable identity for a syntax-validation finding across a relocating edit.
/// Diagnostic text alone is insufficient: removing one violation must not
/// excuse introducing the same message at a different declaration.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
struct ValidationFindingKey {
    message: String,
    anchor: String,
    relative_span: Span,
    whole_member: bool,
}

/// Identity of an untouched import after mapping its pre-edit extent
/// into prospective coordinates. Including the site prevents identical
/// import spellings in one unit from aliasing each other.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
struct ImportSiteKey {
    unit: usize,
    span: Span,
    spelling: String,
}

fn import_site_key(unit: usize, span: Span, spelling: String) -> ImportSiteKey {
    ImportSiteKey {
        unit,
        span,
        spelling,
    }
}

fn validation_finding_key(
    resolved: &mut ResolvedModel,
    unit: usize,
    diagnostic: &Diagnostic,
    map_qn: &dyn Fn(&str) -> String,
) -> ValidationFindingKey {
    let source_anchor = resolved
        .user_elements()
        .filter_map(|e| {
            let (u, extent) = resolved.member_extent(e)?;
            (u == unit
                && diagnostic.span.start >= extent.start
                && diagnostic.span.end <= extent.end)
                .then_some((e, extent))
        })
        .min_by_key(|(_, extent)| extent.len());

    let (anchor, relative_span, whole_member) = match source_anchor {
        Some((e, extent)) => {
            let anchor = resolved
                .element_qualified_name(e)
                .map(|qn| map_qn(&qn))
                .unwrap_or_else(|| format!("<{}@{}>", resolved.element_type(e), extent.start));
            let whole = diagnostic.span == extent;
            let relative = if whole {
                Span::default()
            } else {
                Span::new(
                    diagnostic.span.start.saturating_sub(extent.start),
                    diagnostic.span.end.saturating_sub(extent.start),
                )
            };
            (anchor, relative, whole)
        }
        None => (
            format!(
                "<unit {unit} bytes {}..{}>",
                diagnostic.span.start, diagnostic.span.end
            ),
            Span::default(),
            false,
        ),
    };

    ValidationFindingKey {
        message: diagnostic.message.clone(),
        anchor,
        relative_span,
        whole_member,
    }
}

/// Whether a unit name spells the KerML dialect. The extension is read
/// without case, so a unit named `Model.KerML` is KerML like
/// `model.kerml` — the file systems these names come from do not
/// distinguish the two.
pub(crate) fn is_kerml_unit(name: &str) -> bool {
    Path::new(name)
        .extension()
        .is_some_and(|e| e.eq_ignore_ascii_case("kerml"))
}

/// Parse a unit's text in the dialect its name spells.
fn parse_unit_source(name: &str, text: &str) -> sysmlv2_syntax::parser::Parse {
    if is_kerml_unit(name) {
        parse_kerml_source(text)
    } else {
        parse_source(text)
    }
}

fn syntax_validation(unit_name: &str, text: &str) -> Vec<Diagnostic> {
    let parse = parse_unit_source(unit_name, text);
    sysmlv2_syntax::check::validate(&parse.unit)
}

/// Removal span (relative to `text`, a usage's member text) for
/// dropping one typing entry. The sole entry removes its `:` /
/// `defined by` introducer back to the previous token's end (the exact
/// region extract's untyped path inserts, so `inline(extract(u))` is
/// byte-identical); a list entry removes itself plus the adjoining
/// comma. `None` for shapes it cannot prove (interleaved clauses, no
/// introducer) — the caller refuses rather than guesses.
fn typing_entry_removal(text: &str, entry: Span, entries: &[Span]) -> Option<Span> {
    let (tokens, _) = tokenize(text);
    let toks: Vec<&sysmlv2_syntax::token::Token> = tokens
        .iter()
        .filter(|t| !t.kind.is_trivia() && t.kind != TokenKind::Eof)
        .collect();
    let first = toks.iter().position(|t| t.span.start == entry.start)?;
    if entries.len() == 1 {
        // `x : Engine` → drop from after `x` through the entry; the
        // introducer is `:` or the two words `defined by`.
        let intro = first.checked_sub(1)?;
        let start_tok = match toks[intro].kind {
            TokenKind::Colon => intro,
            _ if slice(text, toks[intro].span) == "by"
                && intro >= 1
                && slice(text, toks[intro - 1].span) == "defined" =>
            {
                intro - 1
            }
            _ => return None,
        };
        let prev = start_tok.checked_sub(1)?;
        return Some(Span::new(toks[prev].span.end, entry.end));
    }
    let mut sorted: Vec<Span> = entries.to_vec();
    sorted.sort_by_key(|sp| sp.start);
    let k = sorted.iter().position(|sp| *sp == entry)?;
    // The gap to the neighbor must be exactly one comma.
    let only_comma = |lo: u32, hi: u32| -> bool {
        let between: Vec<_> = toks
            .iter()
            .filter(|t| t.span.start >= lo && t.span.end <= hi)
            .collect();
        between.len() == 1 && between[0].kind == TokenKind::Comma
    };
    if k > 0 {
        let prev = sorted[k - 1];
        only_comma(prev.end, entry.start).then(|| Span::new(prev.end, entry.end))
    } else {
        let next = sorted[k + 1];
        only_comma(entry.end, next.start).then(|| Span::new(entry.start, next.start))
    }
}

/// Span of a qualified name's terminal token, relative to its written
/// spelling. The lexer keeps quoted identifiers whole, so `'A::B'` is
/// one name token rather than three text-split segments.
fn terminal_name_span(spelling: &str) -> Span {
    let (tokens, _) = tokenize(spelling);
    tokens
        .iter()
        .rev()
        .find(|t| !t.kind.is_trivia() && t.kind != TokenKind::Eof)
        .map(|t| t.span)
        .unwrap_or_else(|| Span::new(0, spelling.len() as u32))
}

/// The definition name [`EditBuilder::extract_definition`] synthesizes
/// when none is given — exposed so surfaces (the LSP action title, the
/// CLI's dry-run output) can spell the name the engine will use.
#[must_use]
pub fn synthesized_definition_name(usage_name: &str) -> String {
    upper_camel(usage_name)
}

/// UpperCamel synthesis for a definition name: split on `_`/`-`/spaces,
/// capitalize each segment's first character (`engine` → `Engine`,
/// `fuel_tank` → `FuelTank`).
fn upper_camel(name: &str) -> String {
    name.split(|c: char| c == '_' || c == '-' || c.is_whitespace())
        .filter(|s| !s.is_empty())
        .map(|seg| {
            let mut cs = seg.chars();
            match cs.next() {
                Some(f) => f.to_uppercase().collect::<String>() + cs.as_str(),
                None => String::new(),
            }
        })
        .collect()
}

// ---------------------------------------------------------------------------
// Errors
// ---------------------------------------------------------------------------

/// The leading diagnostic's message, for the error messages that quote
/// one. The diagnostic list belongs to whoever built the error, so an
/// empty one reads as a missing detail instead of ending the message
/// in a fault.
fn first_message(diagnostics: &[Diagnostic]) -> &str {
    diagnostics
        .first()
        .map_or("no diagnostic reported", |d| d.message.as_str())
}

/// Failure opening (or rebuilding) a session. Variants are added as
/// new ways to refuse a session appear, so a host matches with a
/// fallback arm.
#[derive(Debug)]
#[non_exhaustive]
pub enum SessionError {
    Io(std::io::Error),
    /// A unit does not parse; the session cannot be built.
    Parse {
        unit: String,
        diagnostics: Vec<Diagnostic>,
    },
    /// A compact-form CBOR payload does not decode.
    Cbor(sysmlv2_cbor::Error),
    /// The session holds explicit ids, which an id-elided encoding
    /// would lose.
    ExplicitIds,
    /// A unit name is blank. Every unit is laid out under its name (the
    /// binary payloads carry it), so a blank one is refused when the
    /// session is built rather than when it is emitted.
    InvalidUnitName(String),
}

impl fmt::Display for SessionError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            SessionError::ExplicitIds => write!(
                f,
                "the session holds explicit ids; an id-elided payload would lose them"
            ),
            SessionError::Io(e) => write!(f, "{e}"),
            SessionError::Parse { unit, diagnostics } => {
                write!(f, "{unit} does not parse: {}", first_message(diagnostics))
            }
            SessionError::Cbor(e) => write!(f, "invalid CBOR payload: {e}"),
            SessionError::InvalidUnitName(n) => {
                write!(f, "invalid unit name {n:?}: a unit name must not be blank")
            }
        }
    }
}

impl From<std::io::Error> for SessionError {
    fn from(e: std::io::Error) -> Self {
        SessionError::Io(e)
    }
}

impl From<sysmlv2_cbor::Error> for SessionError {
    fn from(e: sysmlv2_cbor::Error) -> Self {
        SessionError::Cbor(e)
    }
}

/// Failure planning or committing an edit batch. The session is left in
/// its pre-commit state in every case. Variants are added as new
/// refusals appear, so a host matches with a fallback arm.
#[derive(Debug)]
#[non_exhaustive]
pub enum TransformError {
    /// The element has no declaration site (anonymous or synthesized).
    NotDeclared(ElementRef),
    /// The new name is empty.
    InvalidName(String),
    /// The replacement expression does not parse.
    InvalidExpression { text: String, message: String },
    /// The inserted member text does not parse.
    InvalidMember { text: String, message: String },
    /// `set_feature_value` on an element that has no `= …` value and no
    /// `;`-terminated declaration to extend.
    NoEditableValue(ElementRef),
    /// The replacement type spelling does not parse as a typing target.
    InvalidType { text: String, message: String },
    /// `set_feature_type` on a declaration with more than one written
    /// `: T` clause — which one to replace is ambiguous.
    AmbiguousTyping(ElementRef),
    /// The element has no recorded member extent (synthesized, root, or
    /// an alias/import that owns no element).
    NoExtent(ElementRef),
    /// `retarget` to an element with no qualified name.
    AnonymousTarget(ElementRef),
    /// `move_member` destination lies inside the moved subtree.
    MoveIntoOwnSubtree(ElementRef),
    /// No unit with the given name in the session.
    UnknownUnit(String),
    /// `add_unit` with a name the session already holds.
    UnitExists(String),
    /// A package cannot be split as asked; the reason names the member.
    SplitIneligible { reason: String },
    /// Two edits touch overlapping text.
    OverlappingEdits { unit: usize, at: Span },
    /// Removing the element would strand references outside the removed
    /// text (each entry is one broken site's unit index and span).
    RemovalBreaksReferences {
        element: String,
        sites: Vec<(usize, Span)>,
    },
    /// The edited text no longer parses (the commit was rolled back).
    ReparseFailed {
        unit: String,
        diagnostics: Vec<Diagnostic>,
    },
    /// Reference sites the edit did not touch changed their targets
    /// (the commit was rolled back). Each entry names one broken site.
    SemanticIdentity { broken: Vec<String> },
    /// A relocating edit would leave references unresolved that resolved
    /// before it (the commit was rolled back). Relocation ops refuse
    /// these outright — the general pipeline's unresolved-count finding
    /// is not strict enough when headers are synthesized and bodies
    /// move. Each entry names one newly unresolved spelling.
    NewUnresolvedReferences { refs: Vec<String> },
    /// A relocating edit would introduce body-context violations the
    /// pre-commit text did not have (the commit was rolled back) — e.g.
    /// a synthesized definition landing in a body whose context does
    /// not admit definitions. `rebuild` only parses; relocation ops
    /// additionally hold the syntax checker's verdict constant.
    NewValidationFindings { findings: Vec<String> },
    /// `extract_definition` on a usage the eligibility policy
    /// refuses (kind, header shape, dialect, body context, …).
    ExtractIneligible { reason: eligibility::ExtractRefusal },
    /// `inline_definition` on a definition the eligibility policy
    /// refuses (kind, header, usage count, provenance, collisions, …).
    InlineIneligible { reason: eligibility::InlineRefusal },
    /// The requested definition name is already declared by a sibling
    /// in the destination scope.
    NameTaken { name: String, existing: String },
    /// A relocated element's effective-member projection changed across
    /// the commit beyond the admitted owned↔inherited edge (the commit
    /// was rolled back). Each entry is one row present on only one side
    /// (`-` pre, `+` post).
    StructuralIdentity {
        element: String,
        broken: Vec<String>,
    },
}

impl fmt::Display for TransformError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TransformError::NotDeclared(e) => write!(f, "element {e:?} has no declared name"),
            TransformError::InvalidName(n) => write!(f, "invalid name `{n}`"),
            TransformError::InvalidExpression { text, message } => {
                write!(f, "expression `{text}` does not parse: {message}")
            }
            TransformError::InvalidMember { text, message } => {
                write!(f, "member text `{text}` does not parse: {message}")
            }
            TransformError::SplitIneligible { reason } => write!(f, "cannot split: {reason}"),
            TransformError::NoEditableValue(e) => {
                write!(f, "element {e:?} has no editable feature value")
            }
            TransformError::InvalidType { text, message } => {
                write!(f, "type `{text}` does not parse: {message}")
            }
            TransformError::AmbiguousTyping(e) => {
                write!(f, "element {e:?} has multiple written typings")
            }
            TransformError::NoExtent(e) => {
                write!(f, "element {e:?} has no recorded source extent")
            }
            TransformError::AnonymousTarget(e) => {
                write!(f, "element {e:?} has no qualified name to spell")
            }
            TransformError::MoveIntoOwnSubtree(e) => {
                write!(f, "cannot move {e:?} into its own subtree")
            }
            TransformError::UnknownUnit(n) => write!(f, "no unit named `{n}`"),
            TransformError::UnitExists(n) => write!(f, "a unit named `{n}` already exists"),
            TransformError::OverlappingEdits { unit, at } => {
                write!(
                    f,
                    "overlapping edits in unit {unit} at {}..{}",
                    at.start, at.end
                )
            }
            TransformError::RemovalBreaksReferences { element, sites } => {
                write!(
                    f,
                    "removing `{element}` breaks {} reference(s)",
                    sites.len()
                )
            }
            TransformError::ReparseFailed { unit, diagnostics } => {
                write!(
                    f,
                    "edited {unit} does not parse: {}",
                    first_message(diagnostics)
                )
            }
            TransformError::SemanticIdentity { broken } => write!(
                f,
                "edit refused: {} reference{} would break: {}",
                broken.len(),
                if broken.len() == 1 { "" } else { "s" },
                broken.join("; ")
            ),
            TransformError::NewUnresolvedReferences { refs } => write!(
                f,
                "edit refused: {} reference{} would become unresolved: {}",
                refs.len(),
                if refs.len() == 1 { "" } else { "s" },
                refs.join("; ")
            ),
            TransformError::NewValidationFindings { findings } => write!(
                f,
                "edit refused: {} new body-context violation{}: {}",
                findings.len(),
                if findings.len() == 1 { "" } else { "s" },
                findings.join("; ")
            ),
            TransformError::ExtractIneligible { reason } => {
                write!(f, "extract refused: {reason}")
            }
            TransformError::InlineIneligible { reason } => {
                write!(f, "inline refused: {reason}")
            }
            TransformError::NameTaken { name, existing } => {
                write!(f, "name `{name}` is already declared by `{existing}`")
            }
            TransformError::StructuralIdentity { element, broken } => write!(
                f,
                "edit refused: `{element}`'s effective members would change structurally: {}",
                broken.join("; ")
            ),
        }
    }
}

impl std::error::Error for SessionError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            SessionError::Io(e) => Some(e),
            SessionError::Cbor(e) => Some(e),
            SessionError::Parse { .. }
            | SessionError::InvalidUnitName(_)
            | SessionError::ExplicitIds => None,
        }
    }
}

impl std::error::Error for TransformError {}

// ---------------------------------------------------------------------------
// Session
// ---------------------------------------------------------------------------

/// A set of model sources with their resolved model, rebuilt on every
/// committed edit batch. Single-owner: all navigation and editing goes
/// through it.
pub struct Session {
    /// (unit name, current text) in model order — user units only.
    sources: Vec<(String, String)>,
    lib: Option<Library>,
    /// Number of library units preceding the user units in the model
    /// (RefSite/unit indices include them).
    unit_offset: usize,
    model: Model,
    resolved: ResolvedModel,
    /// Non-fatal problems from lifting interchange JSON (unknown
    /// constructs, unresolvable references) — empty for text sessions.
    warnings: Vec<String>,
    /// Explicit ids: graph-derived id → (the id the loaded document
    /// carried, the element's metaclass) for every element whose given
    /// id is not its derivation. Re-applied after every rebuild, keyed by
    /// the derived id, and pruned to the entries that still land on an
    /// element of the recorded metaclass: an edit that restructures an
    /// element's ownership path (rename, move, delete) retires that
    /// subtree's entries, so a later element deriving the same key never
    /// inherits a vanished element's identity.
    explicit_ids: HashMap<Uuid, (Uuid, &'static str)>,
    /// Whether the loaded document carried references the lift could only
    /// spell as ids, so emissions must bind them.
    binds_ids: bool,
}

/// Where a session's standard library comes from: a directory on disk
/// (the CLI shape — the sealed-snapshot cache applies), or in-memory
/// `(unit name, text)` sources for hosts without a filesystem (WASM,
/// embedded consumers). Cheap to clone; sessions keep one for rebuilds.
#[derive(Clone)]
pub enum Library {
    Dir(PathBuf),
    /// An immutable graph shared across session builds and edits.
    Prepared(std::sync::Arc<sysmlv2_model::prepared::PreparedLibrary>),
    Sources {
        units: std::sync::Arc<Vec<(String, String)>>,
        /// A sealed snapshot (`LibraryCache::to_bytes`) recorded against
        /// exactly these units in this order — resolution replays
        /// instead of searching. Stale or foreign bytes are rejected by
        /// the snapshot's own version/fingerprint/checksum guards and
        /// the build falls back to a cold resolve.
        snapshot: Option<std::sync::Arc<Vec<u8>>>,
    },
}

impl Library {
    /// Prepare ordered in-memory library sources once for repeated session builds.
    /// The optional resolution snapshot has the same fallback behavior as
    /// [`Self::sources_with_snapshot`]. Changed or appended sources require a new
    /// library; sessions cloned from this value share only immutable library data.
    pub fn prepared_sources(
        units: Vec<(String, String)>,
        snapshot: Option<Vec<u8>>,
    ) -> Result<Library, SessionError> {
        let source = Library::Sources {
            units: std::sync::Arc::new(units),
            snapshot: snapshot.map(std::sync::Arc::new),
        };
        let mut model = Model::new();
        load_library_into(&mut model, &source)?;
        Ok(Library::Prepared(model.prepare_library()?))
    }

    pub fn dir(path: impl Into<PathBuf>) -> Library {
        Library::Dir(path.into())
    }

    /// An in-memory library from `(unit name, text)` pairs. Unit names
    /// ending in `.kerml` parse as KerML.
    #[must_use]
    pub fn sources(units: Vec<(String, String)>) -> Library {
        Library::Sources {
            units: std::sync::Arc::new(units),
            snapshot: None,
        }
    }

    /// [`Self::sources`] with a sealed resolution snapshot
    /// ([`sysmlv2_model::libcache::LibraryCache::to_bytes`]) recorded
    /// against the same units in the same order.
    #[must_use]
    pub fn sources_with_snapshot(units: Vec<(String, String)>, snapshot: Vec<u8>) -> Library {
        Library::Sources {
            units: std::sync::Arc::new(units),
            snapshot: Some(std::sync::Arc::new(snapshot)),
        }
    }
}

/// Load a [`Library`] into `model`. Directories share the CLI's prepared
/// graph cache; a returned path is for saving a legacy resolution recording
/// when preparation is unavailable. In-memory sources have no disk cache.
fn load_library_into(model: &mut Model, lib: &Library) -> Result<Option<PathBuf>, SessionError> {
    match lib {
        Library::Dir(dir) => load_library_with_cache(model, dir),
        Library::Prepared(library) => {
            library.clone().install(model)?;
            Ok(None)
        }
        Library::Sources { units, snapshot } => {
            for (name, src) in units.iter() {
                model.add_library_source(name.clone(), src);
            }
            if let Some(cache) = snapshot
                .as_deref()
                .and_then(|bytes| libcache::LibraryCache::from_bytes(bytes))
            {
                model.set_library_cache(cache);
            }
            Ok(None)
        }
    }
}

/// Use the same prepared-library loader as the CLI. Live models keep the shared
/// library alive across session edits; changing its content selects a new base.
///
/// A cache the loader could not write is dropped here for the same reason the
/// recording's own `save` result is: a session's hosts (a language server, a
/// browser, an embedding process) have no stream this could be written to, and
/// the cache is an optimization the session never depends on.
fn load_library_with_cache(model: &mut Model, dir: &Path) -> Result<Option<PathBuf>, SessionError> {
    Ok(sysmlv2_model::prepared::load_library_with_cache(model, dir)?.recording_path)
}

/// The pipeline stage a check finding came from. A session refuses only
/// units with `Parse` findings; a host that degrades gracefully keys on
/// this rather than on severity alone.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CheckStage {
    /// The unit did not parse; the remaining stages did not run on it.
    Parse,
    /// Body-context legality (a member the grammar does not allow in its
    /// surrounding body).
    Context,
    /// Reference resolution against the model and library.
    Referential,
    /// Semantic constraints on a resolved model.
    Semantic,
}

impl CheckStage {
    #[must_use]
    pub fn as_str(self) -> &'static str {
        match self {
            CheckStage::Parse => "parse",
            CheckStage::Context => "context",
            CheckStage::Referential => "referential",
            CheckStage::Semantic => "semantic",
        }
    }
}

/// One finding from [`check_sources`]: the CLI `check` verdict shape with
/// the unit name and a 1-based line/column position resolved from the
/// diagnostic's span.
#[derive(Clone, Debug)]
pub struct CheckFinding {
    pub severity: Severity,
    pub message: String,
    /// Unit name of the source the finding is in (as passed to
    /// [`check_sources`]).
    pub unit: String,
    pub line: u32,
    pub col: u32,
    /// The diagnostic's byte span in the unit's text.
    pub span: Span,
    /// The stage that produced the finding.
    pub stage: CheckStage,
}

/// Text a lenient parse removed from a unit, or closers it appended —
/// see [`lenient_sources`]. Offsets are bytes and columns byte-based, as
/// in [`CheckFinding`].
#[derive(Clone, Debug)]
pub struct DroppedText {
    pub unit: String,
    /// Byte span in the unit's original text (empty when text was
    /// appended).
    pub start: u32,
    pub end: u32,
    /// 1-based positions of the span's start and end in the original
    /// text.
    pub line: u32,
    pub col: u32,
    pub end_line: u32,
    pub end_col: u32,
    /// The removed text (empty when text was appended).
    pub text: String,
    /// Line breaks the removal took out of the text as it stood (so the
    /// counts of a unit's records are disjoint even when a later removal
    /// encloses an earlier one), and whether it took whole lines (the
    /// indentation before the text and the line break after it): what
    /// maps a line of the repaired text back to the original, records
    /// taken in order of `start`.
    pub lines_removed: u32,
    pub whole_lines: bool,
    /// Text appended at `start`: the closers of bodies left open at the
    /// end of the unit (empty when text was removed).
    pub inserted: String,
    /// The parse message the repair answered.
    pub message: String,
}

/// A unit a lenient parse could not repair — see [`lenient_sources`].
#[derive(Clone, Debug)]
pub struct UnrepairedUnit {
    pub unit: String,
    /// The first parse message still standing, at its 1-based position
    /// in the repaired text.
    pub message: String,
    pub line: u32,
    pub col: u32,
}

/// What [`lenient_sources`] produced.
#[derive(Clone, Debug, Default)]
pub struct LenientSources {
    /// Every unit in input order, repaired where it had to be.
    pub sources: Vec<(String, String)>,
    /// What the repairs removed or appended, in unit order.
    pub dropped: Vec<DroppedText>,
    /// Units still failing to parse after the repair; their entry in
    /// `sources` carries the partially repaired text.
    pub unrepaired: Vec<UnrepairedUnit>,
}

/// Rounds of parse-and-cut per unit: each round answers every diagnostic
/// of one parse, so a unit needs several only when a cut uncovers new
/// errors.
const LENIENT_ROUNDS: usize = 64;

/// The sources with every unit that fails to parse repaired so that a
/// session can be built over what parsed. Each round parses the unit and
/// answers every diagnostic at once. An error inside a member's
/// declaration removes that member; a zero-width error at a member's end
/// (the parser kept the member but it lacks its `;`) removes that member;
/// an error inside a body where the parser skipped a failed member
/// removes that member's text, recovered from the trivia-free tokens
/// between the end of the previous sibling (or the body's `{`) and the
/// `;` that ends it, the body it opens, or the `}` that closes the
/// enclosing body — the way the parser skips it; an error at the end of
/// the unit with bodies left open appends the missing closers. Text that
/// stands alone on its lines goes with its indentation and line break.
/// The unit is parsed again until it is clean; a unit that stays broken
/// is named in [`LenientSources::unrepaired`]. Every record is in the
/// original text's coordinates. The syntax tree is partial, never
/// absent, so a broken file is not a blank file.
#[must_use]
pub fn lenient_sources(sources: &[(String, String)]) -> LenientSources {
    use sysmlv2_syntax::token::TokenKind;
    let mut out = LenientSources::default();
    for (name, text) in sources {
        let parse_unit = |t: &str| parse_unit_source(name, t);
        let original = text.as_str();
        let orig_len = original.len() as u32;
        let index = LineIndex::new(original);
        let mut current = text.clone();
        // Removed spans in original coordinates: disjoint and sorted, so
        // a position in the current text maps back by adding the length
        // of every removal before it. Appended closers sit past the end.
        let mut drops: Vec<(u32, u32)> = Vec::new();
        let to_original = |pos: u32, drops: &[(u32, u32)], exclusive_end: bool| -> u32 {
            let mut p = pos;
            for (s, e) in drops {
                let before = if exclusive_end { *s < p } else { *s <= p };
                if before {
                    p += e - s;
                } else {
                    break;
                }
            }
            p.min(orig_len)
        };
        let record_drop = |drops: &mut Vec<(u32, u32)>, mut s: u32, mut e: u32| {
            // A removal enclosing or touching earlier ones absorbs them.
            drops.retain(|(a, b)| {
                let touches = *a <= e && *b >= s;
                if touches {
                    s = s.min(*a);
                    e = e.max(*b);
                }
                !touches
            });
            drops.push((s, e));
            drops.sort_unstable();
        };
        let mut remaining: Option<Diagnostic> = None;
        for round in 0..=LENIENT_ROUNDS {
            let parse = parse_unit(&current);
            let Some(first) = parse.diagnostics.first().cloned() else {
                remaining = None;
                break;
            };
            if round == LENIENT_ROUNDS {
                remaining = Some(first);
                break;
            }
            let len = current.len() as u32;
            let (mut tokens, _) = tokenize(&current);
            tokens.retain(|t| !t.kind.is_trivia() && t.kind != TokenKind::Eof);
            // Plan this round's cuts against the current text: the
            // recorded span, the widened cut, and the message.
            let mut cuts: Vec<(Span, Span, String)> = Vec::new();
            let mut closers = 0usize;
            let mut closer_message = String::new();
            for d in &parse.diagnostics {
                let mut at = d.span.start.min(len);
                if at >= len {
                    let depth = tokens.iter().fold(0i64, |n, t| match t.kind {
                        TokenKind::LBrace => n + 1,
                        TokenKind::RBrace => (n - 1).max(0),
                        _ => n,
                    });
                    if depth > 0 {
                        if closers == 0 {
                            closer_message = d.message.clone();
                        }
                        closers = closers.max(depth as usize);
                        continue;
                    }
                    if len == 0 {
                        continue;
                    }
                    at = len - 1;
                }
                let zero_width = d.span.end <= d.span.start;
                let span = failed_extent(&parse.unit.members, &tokens, at, zero_width);
                if span.end <= span.start {
                    continue;
                }
                cuts.push((span, widen_to_own_lines(&current, span), d.message.clone()));
            }
            // Disjoint cuts: ones that overlap, touch, or sit on one line
            // with only blanks between them become one record, widened
            // again as a whole (three stray closers on one line go with
            // their line). A cut that already took its line break is a
            // record of its own.
            cuts.sort_by_key(|(s, _, _)| (s.start, s.end));
            let bytes = current.as_bytes();
            cuts.dedup_by(|later, earlier| {
                let end = earlier.1.end as usize;
                let joins = later.1.start < earlier.1.end
                    || (end > 0
                        && bytes[end - 1] != b'\n'
                        && bytes[end..later.1.start as usize]
                            .iter()
                            .all(|b| matches!(b, b' ' | b'\t')));
                if joins {
                    earlier.0 = Span::new(
                        earlier.0.start.min(later.0.start),
                        earlier.0.end.max(later.0.end),
                    );
                    earlier.1 = Span::new(
                        earlier.1.start.min(later.1.start),
                        earlier.1.end.max(later.1.end),
                    );
                }
                joins
            });
            for cut in &mut cuts {
                cut.1 = widen_to_own_lines(&current, cut.1);
            }
            // Records in original coordinates, planned before any cut. A
            // cut lying entirely in appended closers has nothing original
            // to record and is applied silently.
            let mut planned: Vec<(u32, u32, u32, u32, u32, String)> = Vec::new();
            for (span, cut, message) in &cuts {
                let cs = to_original(cut.start, &drops, false);
                if cs >= orig_len {
                    // Appended closers being cut again: the record that
                    // appended them gives the text back.
                    let text = &current[cut.start as usize..cut.end as usize];
                    if let Some(rec) = out
                        .dropped
                        .iter_mut()
                        .rev()
                        .find(|d| d.unit == *name && !d.inserted.is_empty())
                    {
                        rec.inserted = rec.inserted.replacen(text, "", 1);
                    }
                    continue;
                }
                let os = to_original(span.start, &drops, false);
                let oe = to_original(span.end, &drops, true);
                let ce = to_original(cut.end, &drops, true);
                let lines = current[cut.start as usize..cut.end as usize]
                    .matches('\n')
                    .count() as u32;
                planned.push((os, oe, cs, ce, lines, message.clone()));
            }
            if cuts.is_empty() && closers == 0 {
                remaining = Some(first);
                break;
            }
            // Closers were counted over tokens this round's cuts may take
            // away: the next parse decides on the cut text.
            if !cuts.is_empty() {
                closers = 0;
            }
            for (os, oe, cs, ce, lines, message) in &planned {
                let start = index.line_col(*os);
                let end = index.line_col(*oe);
                out.dropped.push(DroppedText {
                    unit: name.clone(),
                    start: *os,
                    end: *oe,
                    line: start.line,
                    col: start.col,
                    end_line: end.line,
                    end_col: end.col,
                    text: original[*os as usize..*oe as usize].to_string(),
                    lines_removed: *lines,
                    whole_lines: (*cs, *ce) != (*os, *oe),
                    inserted: String::new(),
                    message: message.clone(),
                });
                record_drop(&mut drops, *cs, *ce);
            }
            for (_, cut, _) in cuts.iter().rev() {
                current.replace_range(cut.start as usize..cut.end as usize, "");
            }
            if closers > 0 {
                let mut inserted = String::new();
                if !current.is_empty() && !current.ends_with('\n') {
                    inserted.push('\n');
                }
                for _ in 0..closers {
                    inserted.push_str("}\n");
                }
                let pos = index.line_col(orig_len);
                out.dropped.push(DroppedText {
                    unit: name.clone(),
                    start: orig_len,
                    end: orig_len,
                    line: pos.line,
                    col: pos.col,
                    end_line: pos.line,
                    end_col: pos.col,
                    text: String::new(),
                    lines_removed: 0,
                    whole_lines: false,
                    inserted: inserted.clone(),
                    message: closer_message.clone(),
                });
                current.push_str(&inserted);
            }
        }
        if let Some(d) = remaining {
            let pos = LineIndex::new(&current).line_col(d.span.start.min(current.len() as u32));
            out.unrepaired.push(UnrepairedUnit {
                unit: name.clone(),
                message: d.message,
                line: pos.line,
                col: pos.col,
            });
        }
        out.sources.push((name.clone(), current));
    }
    out
}

/// The start of the run of spaces and tabs ending at `pos` — where the
/// line's indentation begins, when only indentation precedes `pos`.
fn indent_start(bytes: &[u8], pos: u32) -> u32 {
    let mut start = pos;
    while start > 0 && matches!(bytes[start as usize - 1], b' ' | b'\t') {
        start -= 1;
    }
    start
}

/// The text a removal takes with the member at `extent`: its own lines,
/// indentation and line break included (either line ending), when the
/// member stands alone on them. A member that shares its line keeps the
/// line as written, and so does one with no line break after it —
/// there, only the blanks trailing the member go with it.
///
/// Sibling of [`widen_to_own_lines`], which repairs unparseable text
/// rather than planning an edit and so also takes the indentation of a
/// member that ends the file.
fn cut_whole_lines(src: &str, extent: Span) -> Span {
    let bytes = src.as_bytes();
    let start = indent_start(bytes, extent.start);
    if start > 0 && bytes[start as usize - 1] != b'\n' {
        return extent;
    }
    let mut end = extent.end;
    while (end as usize) < bytes.len() && matches!(bytes[end as usize], b' ' | b'\t') {
        end += 1;
    }
    let rest = &bytes[end as usize..];
    if rest.starts_with(b"\r\n") {
        Span::new(start, end + 2)
    } else if rest.starts_with(b"\n") {
        Span::new(start, end + 1)
    } else {
        // Nothing closes the line, so the indentation stays where it is.
        Span::new(extent.start, end)
    }
}

/// Widen `span` to whole lines when its text stands alone on them: the
/// indentation before it and the line break after it go with it.
fn widen_to_own_lines(text: &str, span: Span) -> Span {
    let bytes = text.as_bytes();
    let start = indent_start(bytes, span.start);
    if start > 0 && bytes[start as usize - 1] != b'\n' {
        return span;
    }
    let mut end = span.end;
    while (end as usize) < bytes.len() && matches!(bytes[end as usize], b' ' | b'\t') {
        end += 1;
    }
    let rest = &bytes[end as usize..];
    if rest.starts_with(b"\r\n") {
        Span::new(start, end + 2)
    } else if rest.starts_with(b"\n") {
        Span::new(start, end + 1)
    } else if rest.is_empty() {
        Span::new(start, end)
    } else {
        span
    }
}

/// The body members of a member, for every kind that owns a body. The
/// sub-bodies of control usages (`if`/`while`/`for` branches) are not
/// descended: an error in one charges the whole control usage.
fn member_body(m: &sysmlv2_syntax::ast::Member) -> Option<&[sysmlv2_syntax::ast::Member]> {
    use sysmlv2_syntax::ast::MemberKind;
    match &m.kind {
        MemberKind::Package(p) => p.body.as_deref(),
        MemberKind::Definition(d) => d.body.as_deref(),
        MemberKind::Usage(u)
        | MemberKind::Subject(u)
        | MemberKind::Actor(u)
        | MemberKind::Stakeholder(u)
        | MemberKind::Objective(u)
        | MemberKind::FramedConcern(u)
        | MemberKind::RequirementVerification(u)
        | MemberKind::Render(u)
        | MemberKind::Return(u)
        | MemberKind::RequirementConstraint { usage: u, .. }
        | MemberKind::StateSubaction {
            action: Some(u), ..
        } => u.body.as_deref(),
        MemberKind::MultiplicityDecl(d) => d.body.as_deref(),
        _ => None,
    }
}

/// The innermost member whose span holds `offset`, across nested bodies.
fn innermost_member(
    members: &[sysmlv2_syntax::ast::Member],
    offset: u32,
) -> Option<&sysmlv2_syntax::ast::Member> {
    for m in members {
        if m.span.start <= offset && offset < m.span.end {
            if let Some(inner) = member_body(m).and_then(|b| innermost_member(b, offset)) {
                return Some(inner);
            }
            return Some(m);
        }
    }
    None
}

/// The deepest member whose span ends exactly at `offset`: where the
/// parser reports a missing terminator.
fn deepest_member_ending_at(
    members: &[sysmlv2_syntax::ast::Member],
    offset: u32,
) -> Option<&sysmlv2_syntax::ast::Member> {
    let m = members.iter().find(|m| m.span.end == offset)?;
    Some(
        member_body(m)
            .and_then(|b| deepest_member_ending_at(b, offset))
            .unwrap_or(m),
    )
}

/// The end offset of the `{` that opens the member's own body: the one
/// the member's last `}` closes, or — for a member the parser left open
/// at the end of the unit — the outermost `{` inside it without a match.
/// `None` when the member has no braces.
fn member_body_open(
    m: &sysmlv2_syntax::ast::Member,
    tokens: &[sysmlv2_syntax::token::Token],
) -> Option<u32> {
    use sysmlv2_syntax::token::TokenKind;
    let first = tokens.partition_point(|t| t.span.start < m.span.start);
    let mut open: Vec<u32> = Vec::new();
    let mut last_closed: Option<u32> = None;
    for t in tokens[first..]
        .iter()
        .take_while(|t| t.span.start < m.span.end)
    {
        match t.kind {
            TokenKind::LBrace => open.push(t.span.end),
            TokenKind::RBrace => {
                if let Some(o) = open.pop() {
                    last_closed = Some(o);
                }
            }
            _ => {}
        }
    }
    open.first().copied().or(last_closed)
}

/// The text a diagnostic at `at` condemns: the member whose declaration
/// holds it; the member ending there when the diagnostic is zero-width
/// (it lacks its terminator); otherwise the failed statement the parser
/// skipped in the enclosing body, recovered from the tokens after the
/// previous sibling (or the body's `{`).
fn failed_extent(
    members: &[sysmlv2_syntax::ast::Member],
    tokens: &[sysmlv2_syntax::token::Token],
    at: u32,
    zero_width: bool,
) -> Span {
    let (siblings, floor): (&[sysmlv2_syntax::ast::Member], u32) =
        match innermost_member(members, at) {
            Some(m) => match (member_body(m), member_body_open(m, tokens)) {
                (Some(body), Some(open_end)) if at >= open_end => (body, open_end),
                _ => return m.span,
            },
            None => (members, 0),
        };
    if zero_width {
        if let Some(c) = deepest_member_ending_at(siblings, at) {
            return c.span;
        }
    }
    let anchor = siblings
        .iter()
        .filter(|c| c.span.end <= at)
        .map(|c| c.span.end)
        .max()
        .unwrap_or(floor)
        .max(floor);
    statement_extent(tokens, anchor, at)
}

/// The failed statement between `anchor` (the end of the last parsed
/// text before it) and the diagnostic at `at`, recovered from the
/// trivia-free tokens the way the parser skips it: from the first token
/// at or after `anchor`, forward through the next `;` at depth zero or
/// the end of a body opened inside it, stopping before the `}` that
/// closes the enclosing body. A diagnostic sitting on a brace at the
/// statement's start names a stray brace: that token alone.
fn statement_extent(tokens: &[sysmlv2_syntax::token::Token], anchor: u32, at: u32) -> Span {
    use sysmlv2_syntax::token::TokenKind;
    let start = tokens.partition_point(|t| t.span.start < anchor);
    let i = tokens.partition_point(|t| t.span.end <= at);
    if start >= tokens.len() {
        return Span::new(at, at);
    }
    let i = i.max(start).min(tokens.len() - 1);
    if i == start && matches!(tokens[i].kind, TokenKind::LBrace | TokenKind::RBrace) {
        return tokens[i].span;
    }
    let mut end = i;
    let mut depth = 0i64;
    let mut k = i;
    while k < tokens.len() {
        match tokens[k].kind {
            TokenKind::LBrace => depth += 1,
            TokenKind::RBrace => {
                if depth == 0 {
                    break;
                }
                depth -= 1;
                if depth == 0 {
                    end = k + 1;
                    break;
                }
            }
            TokenKind::Semi if depth == 0 => {
                end = k + 1;
                break;
            }
            _ => {}
        }
        k += 1;
        end = k;
    }
    if end <= start {
        return tokens[i].span;
    }
    Span::new(tokens[start].span.start, tokens[end - 1].span.end)
}

/// Check in-memory sources: per-unit parse
/// and body-context validation always; referential and semantic checks
/// against the standard library when `lib_dir` is given (loaded through
/// the same prepared-library cache as [`Session`]). Unlike CLI `check`,
/// model-level checks require a library here, and unused-import analysis is
/// not included. Unit names ending in
/// `.kerml` parse as KerML.
///
/// Model problems come back as [`CheckFinding`]s — a broken parse is a
/// finding, not an `Err`. `Err` is reserved for operational failures
/// (unreadable library directory).
pub fn check_sources(
    sources: &[(String, String)],
    lib_dir: Option<&Path>,
) -> Result<Vec<CheckFinding>, SessionError> {
    check_sources_with_library(sources, lib_dir.map(Library::dir).as_ref())
}

/// [`check_sources`] over any [`Library`] source — the entry point for
/// hosts that carry the standard library in memory (WASM).
pub fn check_sources_with_library(
    sources: &[(String, String)],
    lib: Option<&Library>,
) -> Result<Vec<CheckFinding>, SessionError> {
    let mut parsed = Vec::new();
    let mut findings = syntax_findings(sources, |source| {
        if lib.is_some() {
            parsed.push(source);
        }
    });

    // Referential + semantic checks: all cleanly-parsed units as one
    // model against the library.
    if let Some(lib) = lib {
        let mut model = Model::new();
        let cache_path = load_library_into(&mut model, lib)?;
        for source in parsed {
            model.add_parsed_source(source);
        }
        let mut resolved = ResolvedModel::build(&model);
        if let (Some(path), Some(cache)) = (cache_path, model.take_recorded_library_cache()) {
            let _ = cache.save(&path);
        }
        for (unit, d) in sysmlv2_model::check::validate_model_with(&mut resolved, &model) {
            let name = &model.unit(unit).name;
            let index = &model.unit(unit).lines;
            findings.extend(findings_for(name, index, &[d], CheckStage::Referential));
        }
        for (unit, d) in sysmlv2_model::check::validate_semantics_with(&mut resolved, &model) {
            let name = &model.unit(unit).name;
            let index = &model.unit(unit).lines;
            findings.extend(findings_for(name, index, &[d], CheckStage::Semantic));
        }
    }

    Ok(findings)
}

/// Re-apply a session's explicit ids after a rebuild and bind the
/// references the lift could only spell as ids.
fn apply_explicit_ids(
    resolved: &mut ResolvedModel,
    explicit_ids: &mut HashMap<Uuid, (Uuid, &'static str)>,
    binds_ids: bool,
    warnings: &mut Vec<String>,
) {
    if explicit_ids.is_empty() && !binds_ids {
        // A text session: nothing to overlay, and a quoted name that
        // happens to look like an id stays a name.
        return;
    }
    let map: HashMap<Uuid, Uuid> = explicit_ids.iter().map(|(d, (g, _))| (*d, *g)).collect();
    let applied = resolved.override_ids(&map);
    // Prune: an entry survives only while it lands on an element of the
    // metaclass it was recorded for; a vanished or restructured element's
    // entry dies with it.
    let kept: HashMap<Uuid, (Uuid, &'static str)> = applied
        .into_iter()
        .filter(|(d, _, ty)| explicit_ids.get(d).is_some_and(|(_, t)| t == ty))
        .map(|(d, g, ty)| (d, (g, ty)))
        .collect();
    let stale: Vec<Uuid> = explicit_ids
        .keys()
        .filter(|d| !kept.contains_key(*d))
        .copied()
        .collect();
    if !stale.is_empty() {
        // Undo any override applied to an element of another metaclass.
        let undo: HashMap<Uuid, Uuid> = stale
            .iter()
            .filter_map(|d| explicit_ids.get(d).map(|(g, _)| (*g, *d)))
            .collect();
        resolved.override_ids(&undo);
    }
    *explicit_ids = kept;
    if !binds_ids {
        return;
    }
    let bound = resolved.bind_id_spelled_references();
    if !bound.is_empty() {
        // The lift's "cannot name reference target" notes for the ids
        // that are now bound no longer apply. A bound id with no element
        // in the model (a library element with no library loaded) is
        // kept as spelled and reported once, so a library-typed payload
        // loaded without its library still says so.
        let spellings: Vec<String> = bound.iter().map(|u| u.to_string()).collect();
        warnings.retain(|w| {
            !(w.contains("cannot name reference target") && spellings.iter().any(|s| w.contains(s)))
        });
        let outside = bound
            .iter()
            .filter(|id| resolved.element_by_id(&id.to_string()).is_none())
            .count();
        // Re-applied after every rebuild: state the count once.
        warnings.retain(|w| !w.contains("target elements outside the document"));
        if outside > 0 {
            warnings.push(format!(
                "{outside} reference(s) target elements outside the document and are kept by id \
                 (load the library to resolve them)"
            ));
        }
    }
}

/// The per-unit stages of [`check_sources_with_library`] alone: parse
/// diagnostics, and body-context checks on every unit that parsed
/// cleanly (context checks on a broken parse would mislead). No model
/// is built — the host that goes on to open a [`Session`] over the
/// units that parsed gets the resolution stages from
/// [`Session::check_findings`] without resolving the sources twice.
#[must_use]
pub fn check_sources_syntax(sources: &[(String, String)]) -> Vec<CheckFinding> {
    syntax_findings(sources, |_| {})
}

fn findings_for(
    name: &str,
    index: &LineIndex,
    diags: &[Diagnostic],
    stage: CheckStage,
) -> Vec<CheckFinding> {
    diags
        .iter()
        .map(|d| {
            let pos = index.line_col(d.span.start);
            CheckFinding {
                severity: d.severity,
                message: d.message.clone(),
                unit: name.to_string(),
                line: pos.line,
                col: pos.col,
                span: d.span,
                stage,
            }
        })
        .collect()
}

/// Report syntax findings and pass each clean parse to its consumer. A
/// syntax-only caller drops each tree before the next source is parsed.
fn syntax_findings(
    sources: &[(String, String)],
    mut clean: impl FnMut(sysmlv2_model::model::ParsedSource),
) -> Vec<CheckFinding> {
    let mut findings = Vec::new();
    for (name, src) in sources {
        let parsed = sysmlv2_model::model::ParsedSource::new(name.clone(), src);
        if !parsed.diagnostics().is_empty() {
            findings.extend(findings_for(
                name,
                parsed.lines(),
                parsed.diagnostics(),
                CheckStage::Parse,
            ));
            continue;
        }
        findings.extend(findings_for(
            name,
            parsed.lines(),
            &sysmlv2_syntax::check::validate(parsed.unit()),
            CheckStage::Context,
        ));
        clean(parsed);
    }
    findings
}

fn rebuild(
    sources: &[(String, String)],
    lib: Option<&Library>,
) -> Result<(Model, ResolvedModel, usize), SessionError> {
    // Checked before the library loads: the payload emitters key every
    // unit by its name, so a blank one has no place to be laid out.
    if let Some((name, _)) = sources.iter().find(|(name, _)| name.trim().is_empty()) {
        return Err(SessionError::InvalidUnitName(name.clone()));
    }
    let mut model = Model::new();
    let mut cache_path = None;
    if let Some(lib) = lib {
        cache_path = load_library_into(&mut model, lib)?;
    }
    let unit_offset = model.unit_count();
    for (name, src) in sources {
        let unit = model.add_source(name.clone(), src);
        if !unit.diagnostics.is_empty() {
            return Err(SessionError::Parse {
                unit: name.clone(),
                diagnostics: unit.diagnostics.clone(),
            });
        }
    }
    let resolved = ResolvedModel::build(&model);
    if let (Some(path), Some(cache)) = (cache_path, model.take_recorded_library_cache()) {
        let _ = cache.save(&path);
    }
    Ok((model, resolved, unit_offset))
}

/// The unused-private-import check over an already-built model: the
/// Session-free entry for callers (the CLI `check` verb) that carry
/// their own `ResolvedModel`. `texts` maps *model* unit indices to
/// source texts for the user units — units absent from it (the library)
/// are never reported. See [`Session::unused_private_imports`] for the
/// three-condition contract.
pub fn unused_private_imports_with(
    resolved: &mut ResolvedModel,
    texts: &[(usize, String)],
) -> Vec<(usize, Span)> {
    let units: Vec<_> = texts.iter().map(|(unit, _)| *unit).collect();
    let candidates = resolved.unused_private_imports_for_units(&units);
    let mut by_unit = std::collections::HashMap::new();
    for (unit, text) in texts {
        by_unit.entry(*unit).or_insert(text);
    }
    let targets: Vec<_> = candidates.iter().map(|(_, target, _, _)| *target).collect();
    let names = resolved.namespace_member_names_many(&targets);
    let mut occurrences = std::collections::HashMap::new();
    let mut out = Vec::new();
    for (_, target, unit, span) in candidates {
        let Some(text) = by_unit.get(&unit) else {
            continue;
        };
        let names = &names[&target];
        let mentioned = names.iter().any(|name| {
            occurrences
                .entry((unit, name.clone()))
                .or_insert_with(|| mention_extent(text, name))
                .is_some_and(|(start, end)| start < span.start as usize || end > span.end as usize)
        });
        if !mentioned {
            out.push((unit, span));
        }
    }
    out
}

/// Does `name` occur in `text` as a whole word outside the `skip` span?
/// 1-based line and (byte) column of a byte offset in `text`.
fn line_col(text: &str, pos: usize) -> (usize, usize) {
    let upto = &text[..pos.min(text.len())];
    match upto.rfind('\n') {
        Some(i) => (upto.matches('\n').count() + 1, upto.len() - i),
        None => (1, upto.len() + 1),
    }
}

// Whole-source ASCII word boundaries intentionally include comments and
// restricted names. Changing to identifier tokens would change the contract.
fn mention_extent(text: &str, name: &str) -> Option<(usize, usize)> {
    if name.is_empty() {
        return None;
    }
    let bytes = text.as_bytes();
    let is_word = |b: u8| b.is_ascii_alphanumeric() || b == b'_';
    let mut from = 0;
    let mut extent: Option<(usize, usize)> = None;
    while let Some(i) = text[from..].find(name) {
        let start = from + i;
        let end = start + name.len();
        // Include overlapping occurrences, without slicing inside a UTF-8
        // character when a restricted name starts with a non-ASCII letter.
        from = start + name.chars().next().unwrap().len_utf8();
        let left_ok = start == 0 || !is_word(bytes[start - 1]);
        let right_ok = end >= bytes.len() || !is_word(bytes[end]);
        if left_ok && right_ok {
            extent = Some(extent.map_or((start, end), |(first, _)| (first, end)));
        }
    }
    extent
}

impl Session {
    /// Open a session over files on disk (`.sysml` / `.kerml`).
    pub fn open(paths: &[PathBuf]) -> Result<Session, SessionError> {
        let mut sources = Vec::with_capacity(paths.len());
        for p in paths {
            sources.push((p.display().to_string(), std::fs::read_to_string(p)?));
        }
        Session::from_sources(sources)
    }

    /// Open a session over in-memory sources: `(unit name, text)` pairs.
    /// Unit names ending in `.kerml` parse as KerML.
    pub fn from_sources(sources: Vec<(String, String)>) -> Result<Session, SessionError> {
        Self::from_sources_with_library(sources, None)
    }

    /// [`Self::from_sources`] resolved against a library in the same
    /// build — [`Self::from_sources`] followed by
    /// [`Self::load_library_from`] would resolve the user units twice.
    pub fn from_sources_with_library(
        sources: Vec<(String, String)>,
        lib: Option<Library>,
    ) -> Result<Session, SessionError> {
        let (model, resolved, unit_offset) = rebuild(&sources, lib.as_ref())?;
        Ok(Session {
            sources,
            lib,
            unit_offset,
            model,
            resolved,
            warnings: Vec::new(),
            explicit_ids: HashMap::new(),
            binds_ids: false,
        })
    }

    /// Open a session over an interchange JSON document — the payload
    /// path for models with no text behind them (e.g. Flexo MMS). The
    /// element list may be compact or full form (derived properties are
    /// ignored, implied relationships dropped) and may be wrapped as
    /// Flexo `{payload, identity}` change records. A multi-document list
    /// becomes one unit per root namespace, named by the root's
    /// `qualifiedName` when it looks like a model file name (the Flexo
    /// convention — this is also what keeps our re-emitted ids stable),
    /// else `document-N.sysml`. Lift problems are non-fatal:
    /// [`Session::warnings`].
    pub fn from_interchange_json(value: &serde_json::Value) -> Result<Session, SessionError> {
        Self::from_interchange_json_with_library(value, None)
    }

    /// [`Self::from_interchange_json`] resolving against a standard
    /// library: library element ids in the payload lift to their
    /// qualified names (a library-typed payload lifts to parseable text
    /// only when the library is available to name those references),
    /// and the session keeps the library for later resolution and full
    /// emission — as if opened with [`Self::with_library`].
    pub fn from_interchange_json_with_library(
        value: &serde_json::Value,
        lib: Option<&Path>,
    ) -> Result<Session, SessionError> {
        Self::from_interchange_json_with(value, lib.map(Library::dir).as_ref())
    }

    /// [`Self::from_interchange_json_with_library`] over any [`Library`]
    /// source — the entry point for hosts that carry the standard
    /// library in memory (WASM).
    pub fn from_interchange_json_with(
        value: &serde_json::Value,
        lib: Option<&Library>,
    ) -> Result<Session, SessionError> {
        Self::from_interchange_json_named(value, lib, &[])
    }

    /// [`Self::from_interchange_json_with`] with explicit unit names:
    /// `unit_names[i]` names the i-th document (payloads that carry
    /// their unit structure — binary interchange — restore the model's
    /// original file layout this way). Documents past the list fall
    /// back to the usual naming.
    pub fn from_interchange_json_named(
        value: &serde_json::Value,
        lib: Option<&Library>,
        unit_names: &[String],
    ) -> Result<Session, SessionError> {
        Self::from_interchange_json_indented(value, lib, unit_names, Indent::default())
    }

    /// [`Self::from_interchange_json_named`] with an explicit
    /// indentation style for the lifted unit text (presentation only —
    /// ids derive from names and structure, never from layout).
    pub fn from_interchange_json_indented(
        value: &serde_json::Value,
        lib: Option<&Library>,
        unit_names: &[String],
        indent: Indent,
    ) -> Result<Session, SessionError> {
        let value = unwrap_flexo(value);
        let mut warnings = Vec::new();
        // Library ids are named through the same map the CLI seeds for
        // its JSON → text conversion.
        let mut names = match lib {
            Some(l) => {
                let mut model = Model::new();
                let cache_path = load_library_into(&mut model, l)?;
                let names = sysmlv2_model::json::library_name_map(&model);
                if let (Some(path), Some(cache)) = (cache_path, model.take_recorded_library_cache())
                {
                    let _ = cache.save(&path);
                }
                names
            }
            None => Default::default(),
        };
        // split_documents handles multi-root lists; a single-document
        // payload still carries its Flexo name on the root — extract it
        // the same way, since the unit name prefixes every ownership
        // path (= every re-emitted id).
        let docs: Vec<(Option<String>, serde_json::Value)> =
            sysmlv2_model::lift::split_documents(&value)
                .unwrap_or_else(|| vec![(single_root_name(&value), value.clone())]);
        names.extend(sysmlv2_model::lift::document_reference_name_map(&value));
        let mut sources = Vec::with_capacity(docs.len());
        for (i, (root_name, doc)) in docs.iter().enumerate() {
            let unit_name = unit_names
                .get(i)
                .cloned()
                .unwrap_or_else(|| doc_unit_name(root_name.as_deref(), i));
            let lifted = sysmlv2_model::lift::from_compact_json_with_names(doc, &names).map_err(
                |message| SessionError::Parse {
                    unit: unit_name.clone(),
                    diagnostics: vec![Diagnostic::error(Span::default(), message)],
                },
            )?;
            warnings.extend(lifted.errors);
            // Lifted doc/comment bodies are dedented (interchange
            // normalization stripped their margins) — re-lay them.
            sources.push((
                unit_name,
                sysmlv2_syntax::print::print_source_opts(
                    &lifted.unit,
                    sysmlv2_syntax::print::PrintOptions {
                        indent,
                        reflow_doc_bodies: true,
                        ..Default::default()
                    },
                ),
            ));
        }
        let (model, mut resolved, unit_offset) = rebuild(&sources, lib)?;
        // Explicit ids: pair the loaded document's elements with the
        // rebuilt model's by ownership path (roots by document order),
        // and keep every id the document carried that the derivation
        // would have replaced.
        let external = |s: &str| names.get(s).and_then(|segs| segs.last().cloned());
        let (mut explicit_ids, unmatched) =
            sysmlv2_model::loader::explicit_id_map(&value, &model, &external, &mut warnings);
        if unmatched > 0 {
            warnings.push(format!(
                "{unmatched} element(s) of the document have no structural counterpart in the \
                 rebuilt model; their ids are not preserved"
            ));
        }
        let binds_ids = warnings
            .iter()
            .any(|w| w.contains("cannot name reference target"));
        apply_explicit_ids(&mut resolved, &mut explicit_ids, binds_ids, &mut warnings);
        Ok(Session {
            sources,
            lib: lib.cloned(),
            unit_offset,
            model,
            resolved,
            warnings,
            explicit_ids,
            binds_ids,
        })
    }

    /// The session's compact element array with the explicit-id overlay.
    fn compact_json_overlaid(&self) -> serde_json::Value {
        let mut v = sysmlv2_model::json::model_to_compact_json(&self.model);
        self.overlay(&mut v);
        v
    }

    fn compact_json_with_units_overlaid(&self) -> (serde_json::Value, Vec<(usize, String)>) {
        let (mut v, units) = sysmlv2_model::json::model_to_compact_json_with_units(&self.model);
        self.overlay(&mut v);
        (v, units)
    }

    fn overlay(&self, v: &mut serde_json::Value) {
        if self.explicit_ids.is_empty() && !self.binds_ids {
            return;
        }
        sysmlv2_model::loader::overlay_explicit_ids(v, &self.explicit_ids);
    }

    /// Whether the session holds **explicit ids** — ids the loaded
    /// document carried that are not this toolkit's graph derivation
    /// (IDS.md). Such a session's compact payloads carry
    /// [`sysmlv2_cbor::FLAG_EXPLICIT_IDS`], and id elision is refused.
    pub fn has_explicit_ids(&self) -> bool {
        !self.explicit_ids.is_empty()
    }

    /// Non-fatal problems from lifting interchange JSON (empty for
    /// sessions opened over text).
    pub fn warnings(&self) -> &[String] {
        &self.warnings
    }

    /// Resolve against a standard-library directory (rebuilds; the
    /// stdlib cache applies automatically, as in the CLI).
    pub fn with_library(mut self, dir: &Path) -> Result<Session, SessionError> {
        self.load_library(dir)?;
        Ok(self)
    }

    /// [`Self::with_library`] in place: on failure the session keeps its
    /// previous state.
    pub fn load_library(&mut self, dir: &Path) -> Result<(), SessionError> {
        self.load_library_from(Library::dir(dir))
    }

    /// [`Self::load_library`] over any [`Library`] source — in-memory
    /// `(unit name, text)` library units included (the WASM shape).
    pub fn load_library_from(&mut self, lib: Library) -> Result<(), SessionError> {
        let (model, mut resolved, unit_offset) = rebuild(&self.sources, Some(&lib))?;
        apply_explicit_ids(
            &mut resolved,
            &mut self.explicit_ids,
            self.binds_ids,
            &mut self.warnings,
        );
        self.lib = Some(lib);
        self.unit_offset = unit_offset;
        self.model = model;
        // The closure policy is a session setting: it survives a rebuild.
        let policy = self.resolved.closure_policy();
        self.resolved = resolved;
        self.resolved.set_closure_policy(policy);
        Ok(())
    }

    /// Emit the session's model as compact interchange JSON (KerML 10.4;
    /// user units only — library elements resolve but never serialize).
    pub fn to_compact_json(&self) -> serde_json::Value {
        self.compact_json_overlaid()
    }

    /// Emit the session's model as compact-form CBOR — the
    /// deterministic binary re-encoding of [`Self::to_compact_json`],
    /// decodable back to the identical element array.
    ///
    /// # Panics
    ///
    /// If the model's compact form falls outside the codec tables. The
    /// codec's corpus gate pins the compact emitter to those tables, and
    /// a session refuses a blank unit name, which is the one input the
    /// encoder rejects outright.
    pub fn to_compact_cbor(&self) -> Vec<u8> {
        // The corpus gate in sysmlv2-cbor pins the compact emitter's
        // output to the codec tables, so the session's own compact form
        // always encodes. Payloads carry the model's unit structure —
        // each unit root's element index paired with its source path —
        // so decoders can lay the model back out as its original files.
        let (json, units) = self.compact_json_with_units_overlaid();
        if self.has_explicit_ids() {
            sysmlv2_cbor::to_compact_cbor_with_units_explicit(&json, &units)
        } else {
            sysmlv2_cbor::to_compact_cbor_with_units(&json, &units)
        }
        .expect("session compact form is covered by the codec tables")
    }

    /// The unit structure the session's binary payloads carry: for
    /// each user unit, the compact element-array index of its root
    /// namespace and the unit's source path.
    pub fn unit_structure(&self) -> Vec<(usize, String)> {
        sysmlv2_model::json::model_to_compact_json_with_units(&self.model).1
    }

    /// [`Self::to_compact_cbor`] with **id elision** (opt-in):
    /// graph-derivable ids are not shipped — receivers
    /// recompute them, verified by the payload digest. The session's
    /// standard library (when loaded) names the `:>>`-effective-name
    /// targets, so the exception map stays roots-only; decode against
    /// the **same library version** (`from_compact_cbor_elided` /
    /// `from_cbor_with`), or the digest refuses the payload.
    ///
    /// Refused (`Err`) for a session holding explicit ids: every given id
    /// would ride the exception map anyway, and the payload must carry
    /// the explicit-id flag, which the elided form does not.
    pub fn to_compact_cbor_elided(&self) -> Result<Vec<u8>, SessionError> {
        if self.has_explicit_ids() {
            return Err(SessionError::ExplicitIds);
        }
        let names = self.library_id_names();
        let (json, units) = self.compact_json_with_units_overlaid();
        Ok(sysmlv2_cbor::to_compact_cbor_elided_with_units(
            &json,
            &|s| names.get(s).cloned(),
            &units,
        )
        .expect("session compact form is covered by the codec tables"))
    }

    /// Encode the delta from `base` (a compact element array, any
    /// element order) to this session's model as a CBOR delta payload
    /// `portable` selects id-keyed identities for
    /// best-effort application to divergent bases; the strict default
    /// is smaller and digest-gated.
    pub fn delta_cbor_from(
        &self,
        base: &serde_json::Value,
        portable: bool,
    ) -> Result<Vec<u8>, SessionError> {
        // One emission feeds both the target and its unit table so the
        // indices line up by construction. Unit paths ride strict
        // deltas only — portable result indices are not exact.
        let (target, units) = self.compact_json_with_units_overlaid();
        let units = if portable { Vec::new() } else { units };
        sysmlv2_cbor::delta_compact_cbor(
            base,
            &target,
            &sysmlv2_cbor::DeltaOptions::new()
                .with_portable(portable)
                .with_units(units),
        )
        .map_err(SessionError::Cbor)
    }

    /// [`Self::delta_cbor_from`] with **id elision** (strict identity
    /// only): created ids the applier can re-derive
    /// from the applied graph are not shipped — the session's standard
    /// library (when loaded) names the effective-name targets, and the
    /// receiver applies with the same library version
    /// ([`Self::apply_delta_cbor`] / `apply_delta_cbor_with`), or the
    /// delta's id digest refuses the payload.
    pub fn delta_cbor_elided_from(
        &self,
        base: &serde_json::Value,
    ) -> Result<Vec<u8>, SessionError> {
        // Same policy as the elided snapshot: an explicit-id session
        // produces no elided form.
        if self.has_explicit_ids() {
            return Err(SessionError::ExplicitIds);
        }
        let names = self.library_id_names();
        let (target, units) = self.compact_json_with_units_overlaid();
        sysmlv2_cbor::delta_compact_cbor_elided(
            base,
            &target,
            &sysmlv2_cbor::DeltaOptions::new().with_units(units),
            &|s| names.get(s).cloned(),
        )
        .map_err(SessionError::Cbor)
    }

    /// `elementId → last qualified-name segment` for the session's
    /// library elements — the resolver every id-derivation surface
    /// (elision, elided deltas, decode) names external targets with.
    fn library_id_names(&self) -> HashMap<String, String> {
        sysmlv2_model::json::library_name_map(&self.model)
            .into_iter()
            .filter_map(|(id, segs)| segs.last().cloned().map(|n| (id.to_string(), n)))
            .collect()
    }

    /// The model's **state digest** — the content identity
    /// a delta names its base by. Emission-order-independent: the same
    /// model state digests identically however it was produced.
    ///
    /// # Panics
    ///
    /// As [`Self::to_compact_cbor`] — the digest runs over the same
    /// compact form.
    pub fn state_digest(&self) -> Uuid {
        sysmlv2_cbor::state_digest(&self.to_compact_json())
            .expect("session compact form is covered by the codec tables")
    }

    /// Decode any snapshot-form s2c payload (compact, id-elided, or
    /// full) to its element array, naming elided derivation targets
    /// through the session's standard library. Delta payloads refuse
    /// with their pointed message — apply those with
    /// [`Self::apply_delta_cbor`].
    pub fn decode_cbor(&self, bytes: &[u8]) -> Result<serde_json::Value, SessionError> {
        let names = self.library_id_names();
        sysmlv2_cbor::from_cbor_with(bytes, &|s| names.get(s).cloned()).map_err(SessionError::Cbor)
    }

    /// Apply a delta payload against this session's model, returning
    /// the applied element array (delta-canonical order) and the
    /// report. Strict application refuses a wrong base hard — id-elided
    /// deltas re-derive their created ids through the session's
    /// library; `lenient` applies portable deltas best-effort to a
    /// divergent base with the report saying what happened. The session
    /// itself is not modified — the caller decides what to do with the
    /// result.
    pub fn apply_delta_cbor(
        &self,
        bytes: &[u8],
        lenient: bool,
    ) -> Result<(serde_json::Value, sysmlv2_cbor::ApplyReport), SessionError> {
        self.apply_delta_cbor_to(bytes, &self.to_compact_json(), lenient)
    }

    /// [`Self::apply_delta_cbor`] against a caller-held base document
    /// (a compact element array) instead of the session's own model —
    /// the payload-file base path, for a caller that holds the base
    /// document without having loaded it into a session (a loaded
    /// session keeps the document's ids, so [`Self::apply_delta_cbor`]
    /// serves that case). The session still serves as the library
    /// context for elided created ids.
    pub fn apply_delta_cbor_to(
        &self,
        bytes: &[u8],
        base: &serde_json::Value,
        lenient: bool,
    ) -> Result<(serde_json::Value, sysmlv2_cbor::ApplyReport), SessionError> {
        if lenient {
            sysmlv2_cbor::apply_delta_cbor_lenient(bytes, base).map_err(SessionError::Cbor)
        } else {
            let names = self.library_id_names();
            // The real report — it carries the delta's unit
            // structure; strict application refuses a wrong base, so a
            // returned report always has base_matched.
            sysmlv2_cbor::apply_delta_cbor_report_with(bytes, base, &|s| names.get(s).cloned())
                .map_err(SessionError::Cbor)
        }
    }

    /// Open a session over a compact-form CBOR payload — the binary
    /// counterpart of [`Self::from_interchange_json`] (which see for
    /// multi-document naming and warning semantics).
    pub fn from_compact_cbor(bytes: &[u8]) -> Result<Session, SessionError> {
        Self::from_compact_cbor_with_library(bytes, None)
    }

    /// [`Self::from_compact_cbor`] resolving against a standard-library
    /// directory, as [`Self::from_interchange_json_with_library`].
    pub fn from_compact_cbor_with_library(
        bytes: &[u8],
        lib: Option<&Path>,
    ) -> Result<Session, SessionError> {
        Self::from_compact_cbor_with(bytes, lib.map(Library::dir).as_ref())
    }

    /// [`Self::from_compact_cbor_with_library`] over any [`Library`]
    /// source — the entry point for hosts that carry the standard
    /// library in memory (WASM).
    pub fn from_compact_cbor_with(
        bytes: &[u8],
        lib: Option<&Library>,
    ) -> Result<Session, SessionError> {
        Self::from_compact_cbor_indented(bytes, lib, Indent::default())
    }

    /// [`Self::from_compact_cbor_with`] with an explicit indentation
    /// style for the lifted unit text.
    pub fn from_compact_cbor_indented(
        bytes: &[u8],
        lib: Option<&Library>,
        indent: Indent,
    ) -> Result<Session, SessionError> {
        let (value, units) = sysmlv2_cbor::from_compact_cbor_units(bytes)?;
        // Payloads carrying their unit structure restore the model's
        // original file layout: unit-path order is document order.
        let unit_names: Vec<String> = units.into_iter().map(|(_, path)| path).collect();
        Self::from_interchange_json_indented(&value, lib, &unit_names, indent)
    }

    /// Emit the session's model as full interchange JSON (derived
    /// properties + implied relationships, schema-valid).
    pub fn to_full_json(&self) -> serde_json::Value {
        self.to_full_json_with(true)
    }

    /// [`Self::to_full_json`] with unresolved-reference recovery
    /// annotations: when `recover_refs` is set, every reference that
    /// serializes as a dangling id also carries its source spelling, so
    /// a partial model survives emit → lift losslessly (the Flexo
    /// change-record path).
    pub fn to_full_json_with(&self, recover_refs: bool) -> serde_json::Value {
        let mut v = sysmlv2_model::full::model_to_full_json_with(&self.model, recover_refs);
        self.overlay(&mut v);
        v
    }

    /// Emit the session's model as **full-form CBOR** — the binary
    /// re-encoding of [`Self::to_full_json_with`]. An emit view
    /// only: transport the compact form; expand at the edge.
    ///
    /// # Panics
    ///
    /// As [`Self::to_compact_cbor`], for the full form's tables.
    pub fn to_full_cbor(&self, recover_refs: bool) -> Vec<u8> {
        let full = self.to_full_json_with(recover_refs);
        // Root indices differ between the compact and full arrays
        // (implied relationships join the full form): re-locate each
        // unit root by element id.
        let (compact, units) = self.compact_json_with_units_overlaid();
        let by_id: HashMap<&str, usize> = full
            .as_array()
            .map(|arr| {
                arr.iter()
                    .enumerate()
                    .filter_map(|(i, e)| e.get("@id").and_then(|v| v.as_str()).map(|s| (s, i)))
                    .collect()
            })
            .unwrap_or_default();
        let mut full_units: Vec<(usize, String)> = units
            .iter()
            .filter_map(|(i, path)| {
                let id = compact.get(*i)?.get("@id")?.as_str()?;
                by_id.get(id).map(|&fi| (fi, path.clone()))
            })
            .collect();
        full_units.sort_by_key(|&(i, _)| i);
        sysmlv2_cbor::to_full_cbor_with_units(&full, &full_units)
            .expect("session full form is covered by the codec tables")
    }

    /// Map an interchange document's element ids to this session's ids
    /// by qualified name — `(input id, session id)` for every named
    /// input element present here under a different id. A document
    /// loaded into this session keeps its ids and maps nothing; the
    /// mapping is for an input whose structure the session no longer
    /// has (after a rename, or a text session compared with an earlier
    /// export).
    pub fn id_map_from(&mut self, input: &serde_json::Value) -> Vec<(Uuid, Uuid)> {
        let input = unwrap_flexo(input);
        let names = sysmlv2_model::lift::document_name_map(&input);
        let mut session_ids: HashMap<String, Uuid> = HashMap::new();
        let user: Vec<ElementRef> = self.resolved.user_elements().collect();
        for e in user {
            if let Some(qn) = self.resolved.element_qualified_name(e) {
                session_ids.insert(qn, self.resolved.element_id(e));
            }
        }
        let mut out = Vec::new();
        for (id, segments) in &names {
            let Ok(old_id) = Uuid::parse_str(id) else {
                continue;
            };
            let qn = segments
                .iter()
                .map(|s| escape_name(s))
                .collect::<Vec<_>>()
                .join("::");
            if let Some(&new_id) = session_ids.get(&qn) {
                if new_id != old_id {
                    out.push((old_id, new_id));
                }
            }
        }
        out.sort();
        out
    }

    /// The check findings of the session's own model: what
    /// [`check_sources_with_library`] reports for the same sources and
    /// library, read off the session's build instead of a second one.
    /// Parse findings never occur (a session holds only units that
    /// parsed); context findings come from each unit's syntax, and the
    /// referential and semantic stages — like `check`, only with a
    /// library — from the resolved model, whose unresolved list and
    /// import provenance both passes leave intact. Same order as
    /// `check`: each unit's context findings, then referential, then
    /// semantic.
    pub fn check_findings(&mut self) -> Vec<CheckFinding> {
        let mut findings = Vec::new();
        for (unit, name, _) in self.units() {
            let mu = self.model.unit(unit);
            findings.extend(findings_for(
                name,
                &mu.lines,
                &sysmlv2_syntax::check::validate(&mu.unit),
                CheckStage::Context,
            ));
        }
        if self.lib.is_none() {
            return findings;
        }
        let stage =
            |diags: Vec<(usize, Diagnostic)>, stage: CheckStage, out: &mut Vec<CheckFinding>| {
                for (unit, d) in diags {
                    let Some(i) = unit.checked_sub(self.unit_offset) else {
                        continue;
                    };
                    let name = &self.sources[i].0;
                    let index = &self.model.unit(unit).lines;
                    out.extend(findings_for(name, index, &[d], stage));
                }
            };
        let referential =
            sysmlv2_model::check::validate_model_with(&mut self.resolved, &self.model);
        stage(referential, CheckStage::Referential, &mut findings);
        let semantic =
            sysmlv2_model::check::validate_semantics_with(&mut self.resolved, &self.model);
        stage(semantic, CheckStage::Semantic, &mut findings);
        findings
    }

    /// The resolved model — navigation, `query`, evaluation.
    pub fn resolved(&mut self) -> &mut ResolvedModel {
        &mut self.resolved
    }

    /// Read-only view of the resolved model (for the `&self` accessors:
    /// `unresolved_count`, `reference_sites`, …).
    pub fn resolved_ref(&self) -> &ResolvedModel {
        &self.resolved
    }

    /// The session's built model — read-only access for consumers that
    /// drive analysis passes over it (constraint verification, interval
    /// propagation) without re-lowering the sources.
    pub fn model(&self) -> &sysmlv2_model::model::Model {
        &self.model
    }

    /// Current text of a unit, by *model* unit index (the index space of
    /// [`RefSite::unit`]). `None` for library units.
    pub fn source(&self, unit: usize) -> Option<&str> {
        let i = unit.checked_sub(self.unit_offset)?;
        self.sources.get(i).map(|(_, s)| s.as_str())
    }

    /// The user units as `(model unit index, name, text)`.
    pub fn units(&self) -> impl Iterator<Item = (usize, &str, &str)> + '_ {
        self.sources
            .iter()
            .enumerate()
            .map(|(i, (n, s))| (i + self.unit_offset, n.as_str(), s.as_str()))
    }

    /// Name and text of a *library* unit by model unit index — the
    /// units below [`RefSite::unit`]'s user range. `None` for user
    /// units and for directory libraries, whose units live on disk
    /// ([`Self::library_unit_path`]).
    pub fn library_unit(&self, unit: usize) -> Option<(&str, &str)> {
        if unit >= self.unit_offset {
            return None;
        }
        match &self.lib {
            Some(Library::Prepared(library)) => library.source(unit),
            Some(Library::Sources { units, .. }) => {
                units.get(unit).map(|(n, s)| (n.as_str(), s.as_str()))
            }
            _ => None,
        }
    }

    /// On-disk path of a *directory* library's unit by model unit index
    /// (the deterministic add order of [`Model::load_library_dir`]).
    /// `None` for user units and in-memory libraries.
    pub fn library_unit_path(&self, unit: usize) -> Option<std::path::PathBuf> {
        if unit >= self.unit_offset {
            return None;
        }
        match &self.lib {
            Some(Library::Dir(dir)) => sysmlv2_model::model::library_dir_files(dir)
                .ok()?
                .into_iter()
                .nth(unit),
            _ => None,
        }
    }

    /// Plan splitting `root` (a package in a user unit) into one unit
    /// per directly nested package: the file tree, the root-level name
    /// collisions and their renames. Apply it with
    /// [`EditBuilder::split`]. Deeper levels split by running the plan
    /// again on a hoisted package.
    ///
    /// New units take the root unit's extension; a root named without one
    /// parses as SysML, so its new units take `.sysml`.
    pub fn split_plan(
        &mut self,
        root: ElementRef,
        options: &SplitOptions,
    ) -> Result<SplitPlan, TransformError> {
        let unit_offset = self.unit_offset;
        let r = &mut self.resolved;
        if r.element_type(root) != "Package" {
            return Err(TransformError::SplitIneligible {
                reason: format!("`{}` is not a package", r.element_type(root)),
            });
        }
        let (unit, _) = r
            .member_extent(root)
            .ok_or(TransformError::NoExtent(root))?;
        if unit < unit_offset {
            return Err(TransformError::NotDeclared(root));
        }
        let root_name = r
            .element_name(root)
            .ok_or(TransformError::NotDeclared(root))?
            .to_string();
        let unit_name = self.sources[unit - unit_offset].0.clone();
        // The file segment alone carries the extension: a dot in a
        // directory name must not be read as one.
        let (dir_prefix, file) = unit_name
            .rsplit_once('/')
            .map_or(("", unit_name.as_str()), |(d, f)| (d, f));
        let (stem, extension) = file
            .rsplit_once('.')
            .filter(|(stem, ext)| !stem.is_empty() && !ext.is_empty())
            .unwrap_or((file, "sysml"));
        let directory = match &options.directory {
            Some(d) => d.trim_end_matches('/').to_string(),
            None if dir_prefix.is_empty() => stem.to_string(),
            None => format!("{dir_prefix}/{stem}"),
        };
        let children: Vec<ElementRef> = r
            .owned_members(root)
            .into_iter()
            .filter(|&m| r.element_type(m) == "Package" && r.element_name(m).is_some())
            .collect();
        if children.is_empty() {
            return Err(TransformError::SplitIneligible {
                reason: format!("`{root_name}` owns no nested package"),
            });
        }
        let mut entries: Vec<SplitEntry> = Vec::new();
        let mut taken_names: Vec<String> = Vec::new();
        let mut taken_units: Vec<String> = Vec::new();
        for child in children {
            let name = r.element_name(child).unwrap_or_default().to_string();
            let qualified = r
                .element_qualified_name(child)
                .ok_or(TransformError::NotDeclared(child))?;
            let (_, extent) = r
                .member_extent(child)
                .ok_or(TransformError::NoExtent(child))?;
            // A hoisted package becomes a root-level name: it must not
            // collide with one the model already resolves (user or
            // library) or with another hoisted package.
            let mut top = name.clone();
            let mut attempt = 0;
            while r.resolve_qualified(&escape_name(&top)).is_some() || taken_names.contains(&top) {
                attempt += 1;
                top = if attempt == 1 {
                    format!("{root_name} {name}")
                } else {
                    format!("{root_name} {name} {attempt}")
                };
            }
            taken_names.push(top.clone());
            let new_name = (top != name).then_some(top.clone());
            let file = match options.naming {
                SplitNaming::Keep => file_segment(&top),
                SplitNaming::Slug => slug(&top),
            };
            let file = if options.uri_units {
                uri_segment(&file)
            } else {
                file
            };
            let mut unit = format!("{directory}/{file}.{extension}");
            let mut n = 1;
            while taken_units.contains(&unit) || self.sources.iter().any(|(u, _)| *u == unit) {
                n += 1;
                unit = format!("{directory}/{file}-{n}.{extension}");
            }
            taken_units.push(unit.clone());
            entries.push(SplitEntry {
                package: child,
                qualified,
                name,
                new_name,
                unit,
                bytes: (extent.end - extent.start) as usize,
            });
        }
        Ok(SplitPlan {
            root,
            root_unit: unit_name,
            directory,
            entries,
        })
    }

    /// Textual `private import` members that provably feed nothing in
    /// their unit — the unused-import check. Three conditions, all
    /// required (each alone over-reports):
    ///
    /// 1. No lookup resolved a name through the import in this build
    ///    (resolver-recorded provenance).
    /// 2. Nothing the unit references lives under the imported namespace
    ///    (reference-site owner chains).
    /// 3. No member name of the imported namespace even *appears* in the
    ///    unit's text outside the import member itself. This is the
    ///    backstop for reference shapes the site table does not record
    ///    (flow-payload typings): a name that is never spelled cannot be
    ///    referenced.
    ///
    /// Returns `(model unit index, span of the whole import member)` —
    /// the span is the removal range for a quickfix.
    pub fn unused_private_imports(&mut self) -> Vec<(usize, Span)> {
        let texts: Vec<(usize, String)> =
            self.units().map(|(i, _, s)| (i, s.to_string())).collect();
        unused_private_imports_with(&mut self.resolved, &texts)
    }

    /// Start an edit batch. Nothing changes until
    /// [`EditBuilder::commit`] succeeds.
    pub fn edit(&mut self) -> EditBuilder<'_> {
        EditBuilder {
            session: self,
            ops: Vec::new(),
            skip_colliding_renames: false,
        }
    }

    /// The shortest spelling of `target` that resolves to it from
    /// inside `context`'s declaration — what a generated expression
    /// (a value set from a UI, say) should write instead of the full
    /// qualified name. The resolution scope is borrowed from a
    /// reference site inside the context's member extent (its typing;
    /// every typed feature has one); a context with no recorded sites
    /// falls back to the full qualified name. Same suffix discipline
    /// as [`Self::minimize_qualifications`], without any rewriting.
    pub fn minimal_spelling(&mut self, context: ElementRef, target: ElementRef) -> Option<String> {
        use sysmlv2_syntax::ast::{Name, QualifiedName};
        // The lookup-name spelling: it re-resolves, where the
        // specification's `qualifiedName` may name an unnamed end by its
        // implied positional name.
        let full_qn = self.resolved.element_reference_spelling(target)?;
        let full = sysmlv2_syntax::name::respell_canonical(None, &full_qn);
        let Some((unit, extent)) = self.resolved.member_extent(context) else {
            return Some(full);
        };
        let scope = self
            .resolved
            .reference_sites()
            .iter()
            .find(|s| s.unit == unit && s.span.start >= extent.start && s.span.end <= extent.end)
            .map(|s| s.scope);
        let Some(scope) = scope else {
            return Some(full);
        };
        let segs = sysmlv2_syntax::name::split_canonical(&full_qn);
        for k in 1..=segs.len() {
            let suffix = &segs[segs.len() - k..];
            let qn = QualifiedName {
                is_global: false,
                segments: suffix
                    .iter()
                    .map(|v| Name {
                        value: v.clone(),
                        span: Span::default(),
                    })
                    .collect(),
                span: Span::default(),
            };
            if self.resolved.resolve_in_excluding(scope, &qn, None) == Some(target) {
                return Some(
                    suffix
                        .iter()
                        .map(|v| spell_name(v))
                        .collect::<Vec<_>>()
                        .join("::"),
                );
            }
        }
        Some(full)
    }

    /// Respell every reference with the **shortest** spelling that still
    /// resolves to the same element: bare name where unambiguous,
    /// a qualified suffix where needed, the original spelling as the
    /// untouched fallback. *Plain* sites and **import targets** are
    /// considered (chain steps and other special-rule sites are not);
    /// candidates are pre-checked by resolving from the site's own
    /// recorded scope — a heuristic for import targets, whose own rules
    /// differ — and the whole result is verified by a reparse: every
    /// respelled site must resolve to the identical qualified name,
    /// every untouched site must be unaffected, or the offending
    /// respells are dropped and the pass retried. Declarations never
    /// move, so interchange ids are untouched by construction.
    ///
    /// # Panics
    ///
    /// If a feature-chain run is assembled with no sites in it, which
    /// the grouping cannot produce.
    pub fn minimize_qualifications(&mut self) -> Result<MinimizeReport, TransformError> {
        use sysmlv2_syntax::ast::{Name, QualifiedName};
        struct Cand {
            unit: usize,
            start: u32,
            end: u32,
            text: String,
            qn: String,
            name_len: u32,
        }
        impl Cand {
            fn range(&self) -> (usize, u32, u32) {
                (self.unit, self.start, self.end)
            }
        }
        // Candidate respells: per plain site, the shortest suffix of the
        // target's qualified name that resolves back to the same element
        // from the site's scope, when strictly shorter than the written
        // spelling. (A quoted segment containing `::` would split wrong
        // here; such a candidate simply fails the resolve check and the
        // site keeps its original spelling.)
        let sites: Vec<RefSite> = self.resolved.reference_sites().to_vec();
        // Primary sites (qualifier twins share the primary's span),
        // sorted for chain-adjacency detection. Import targets resolve
        // under their own rules (not `plain`), but they still respell
        // safely: the plain resolver picks the candidate heuristically
        // and the reparse verification below is the actual gate — a
        // candidate the import rules read differently fails it and the
        // site keeps its printed spelling.
        let import_site =
            |s: &RefSite| matches!(s.kind.as_str(), "importedNamespace" | "importedMembership");
        let mut primaries: Vec<&RefSite> = Vec::new();
        let mut seen: HashSet<(usize, u32, u32)> = HashSet::new();
        for s in &sites {
            if (!s.plain && !import_site(s)) || s.kind == "qualifier" || s.unit < self.unit_offset {
                continue;
            }
            if seen.insert((s.unit, s.span.start, s.span.end)) {
                primaries.push(s);
            }
        }
        primaries.sort_by_key(|s| (s.unit, s.span.start));

        // A maximal run of sites joined by single `.`s is one feature
        // chain (the lift spells chain links as `$::`-rooted names) —
        // links are not independent references, so a run respells
        // atomically: the shortest head spelling, then the printed
        // member names as the tail. A dangling `.` beyond the run means
        // the chain continues into something this pass does not model —
        // the whole run keeps its printed form.
        let mut cands: Vec<Cand> = Vec::new();
        let mut i = 0usize;
        while i < primaries.len() {
            let src = &self.sources[primaries[i].unit - self.unit_offset].1;
            let mut group = vec![primaries[i]];
            while i + 1 < primaries.len() {
                let (a, b) = (primaries[i], primaries[i + 1]);
                if b.unit == a.unit
                    && b.span.start == a.span.end + 1
                    && src.as_bytes().get(a.span.end as usize) == Some(&b'.')
                {
                    group.push(b);
                    i += 1;
                } else {
                    break;
                }
            }
            i += 1;
            let (first, last) = (group[0], *group.last().expect("nonempty group"));
            if src[..first.span.start as usize].ends_with('.') {
                // Mid-chain: the receiver is a relative spine this run
                // does not start — keep the printed form.
                continue;
            }
            let tail = &src[last.span.end as usize..];
            if tail.starts_with('.') && tail[1..].starts_with("$::") {
                // The chain continues into another *global* link, whose
                // anchoring a head respell would move — keep it whole.
                continue;
            }
            // Shortest head: the suffix of the target's qualified name
            // that resolves back to the same element under the site's
            // own scope and exclusion. (A quoted segment containing `::`
            // would split wrong here; such a candidate simply fails the
            // resolve check and the site keeps its original spelling.)
            let Some(head_qn) = self.resolved.element_qualified_name(first.target) else {
                continue;
            };
            let segs = sysmlv2_syntax::name::split_canonical(&head_qn);
            let mut head: Option<String> = None;
            for k in 1..=segs.len() {
                let suffix = &segs[segs.len() - k..];
                let cand_qn = QualifiedName {
                    is_global: false,
                    segments: suffix
                        .iter()
                        .map(|v| Name {
                            value: v.clone(),
                            span: Span::default(),
                        })
                        .collect(),
                    span: Span::default(),
                };
                if self
                    .resolved
                    .resolve_in_excluding(first.scope, &cand_qn, first.exclude)
                    == Some(first.target)
                {
                    head = Some(
                        suffix
                            .iter()
                            .map(|v| spell_name(v))
                            .collect::<Vec<_>>()
                            .join("::"),
                    );
                    break;
                }
            }
            let Some(mut text) = head else { continue };
            for link in &group[1..] {
                text.push('.');
                text.push_str(&src[link.name_span.start as usize..link.name_span.end as usize]);
            }
            let orig_len = (last.span.end - first.span.start) as usize;
            if text.len() >= orig_len {
                continue;
            }
            let (qn, name_len) = if group.len() == 1 {
                (
                    head_qn,
                    spell_name(segs.last().expect("nonempty qn")).len() as u32,
                )
            } else {
                let Some(q) = self.resolved.element_qualified_name(last.target) else {
                    continue;
                };
                (q, last.name_span.end - last.name_span.start)
            };
            cands.push(Cand {
                unit: first.unit,
                start: first.span.start,
                end: last.span.end,
                text,
                qn,
                name_len,
            });
        }
        cands.sort_by_key(|c| (c.unit, c.start, c.end));

        let mut report = MinimizeReport::default();
        let mut banned: HashSet<(usize, u32)> = HashSet::new();
        // Candidates come from disjoint reference spans, so they should
        // not overlap — but the pass below splices them in one cursor
        // sweep per unit, which would slice backwards if two ever did.
        // An overlapping candidate is banned outright: the first of the
        // run is respelled and the rest keep their printed spelling.
        for i in overlapping_candidates(&cands.iter().map(Cand::range).collect::<Vec<_>>()) {
            banned.insert((cands[i].unit, cands[i].start));
        }
        loop {
            let active: Vec<&Cand> = cands
                .iter()
                .filter(|c| !banned.contains(&(c.unit, c.start)))
                .collect();
            if active.is_empty() {
                return Ok(report);
            }
            // Apply to source copies, tracking each splice's new position.
            let mut new_sources = self.sources.clone();
            let mut new_positions: Vec<u32> = vec![0; active.len()];
            for (local, new_src) in new_sources.iter_mut().enumerate() {
                let unit = local + self.unit_offset;
                let src = &self.sources[local].1;
                let mut out = String::with_capacity(src.len());
                let mut cursor = 0usize;
                for (i, c) in active.iter().enumerate() {
                    if c.unit != unit {
                        continue;
                    }
                    out.push_str(&src[cursor..c.start as usize]);
                    new_positions[i] = out.len() as u32;
                    out.push_str(&c.text);
                    cursor = c.end as usize;
                }
                out.push_str(&src[cursor..]);
                new_src.1 = out;
            }
            let (new_model, mut new_resolved, _off) = rebuild(&new_sources, self.lib.as_ref())
                .map_err(|e| match e {
                    SessionError::Parse { unit, diagnostics } => {
                        TransformError::ReparseFailed { unit, diagnostics }
                    }
                    // rebuild() reparses text — only Io is reachable here.
                    e => TransformError::ReparseFailed {
                        unit: "<library>".into(),
                        diagnostics: vec![Diagnostic::error(Span::default(), e.to_string())],
                    },
                })?;
            let post_sites: Vec<RefSite> = new_resolved.reference_sites().to_vec();
            let mut post_by_span: HashMap<(usize, u32, u32), ElementRef> = HashMap::new();
            for s in &post_sites {
                post_by_span.insert((s.unit, s.name_span.start, s.name_span.end), s.target);
            }
            // Verify each respell resolves to its expected qualified name.
            let mut failed: Vec<(usize, u32)> = Vec::new();
            for (i, c) in active.iter().enumerate() {
                let end = new_positions[i] + c.text.len() as u32;
                let start = end - c.name_len;
                let ok = post_by_span
                    .get(&(c.unit, start, end))
                    .and_then(|&t| new_resolved.element_qualified_name(t))
                    .is_some_and(|got| got == c.qn);
                if !ok {
                    failed.push((c.unit, c.start));
                }
            }
            if !failed.is_empty() {
                report.reverted += failed.len();
                banned.extend(failed);
                continue;
            }
            // Belt and braces: untouched sites cannot change (respelling a
            // reference moves no declaration), but verify anyway.
            let shift = |unit: usize, pos: u32| -> Option<u32> {
                let mut delta: i64 = 0;
                for c in &active {
                    if c.unit != unit {
                        continue;
                    }
                    if pos >= c.end {
                        delta += c.text.len() as i64 - (c.end - c.start) as i64;
                    } else if pos > c.start {
                        return None;
                    }
                }
                Some((pos as i64 + delta) as u32)
            };
            let mut broken: Vec<String> = Vec::new();
            for s in &sites {
                if active
                    .iter()
                    .any(|c| c.unit == s.unit && s.span.start >= c.start && s.span.end <= c.end)
                {
                    continue; // inside a respelled range
                }
                let (Some(ns), Some(ne)) = (
                    shift(s.unit, s.name_span.start),
                    shift(s.unit, s.name_span.end),
                ) else {
                    continue;
                };
                let expected = self.resolved.element_qualified_name(s.target);
                let got = post_by_span
                    .get(&(s.unit, ns, ne))
                    .and_then(|&t| new_resolved.element_qualified_name(t));
                if expected != got {
                    broken.push(format!(
                        "unit {} at {}..{}: expected `{}`, now `{}`",
                        s.unit,
                        ns,
                        ne,
                        expected.as_deref().unwrap_or("<anonymous>"),
                        got.as_deref().unwrap_or("<anonymous>")
                    ));
                }
            }
            if !broken.is_empty() {
                broken.truncate(20);
                return Err(TransformError::SemanticIdentity { broken });
            }
            report.respelled = active.len();
            self.sources = new_sources;
            apply_explicit_ids(
                &mut new_resolved,
                &mut self.explicit_ids,
                self.binds_ids,
                &mut self.warnings,
            );
            self.model = new_model;
            let policy = self.resolved.closure_policy();
            self.resolved = new_resolved;
            self.resolved.set_closure_policy(policy);
            return Ok(report);
        }
    }
}

/// Indexes of the ranges that overlap one kept before them, over
/// `(unit, start, end)` ranges sorted by `(unit, start)`: the first
/// range of an overlapping run is kept and every later range that
/// reaches back into it is reported. Applying the kept ranges in order
/// is then a single forward sweep per unit.
fn overlapping_candidates(ranges: &[(usize, u32, u32)]) -> Vec<usize> {
    let mut overlapping = Vec::new();
    let mut kept: Option<(usize, u32, u32)> = None;
    for (i, &r) in ranges.iter().enumerate() {
        match kept {
            // A later range that starts before the kept one ends —
            // nested in it, or straddling its end.
            Some((unit, _, end)) if unit == r.0 && r.1 < end => overlapping.push(i),
            _ => kept = Some(r),
        }
    }
    overlapping
}

/// Outcome of a [`Session::minimize_qualifications`] pass.
#[derive(Debug, Default, Clone)]
pub struct MinimizeReport {
    /// Reference sites respelled with a shorter equivalent.
    pub respelled: usize,
    /// Candidate respellings dropped by the reparse verification (their
    /// sites keep the original spelling).
    pub reverted: usize,
}

// ---------------------------------------------------------------------------
// Edits
// ---------------------------------------------------------------------------

enum Op {
    Rename {
        e: ElementRef,
        new_name: String,
    },
    SetFeatureValue {
        e: ElementRef,
        expr: String,
    },
    SetFeatureType {
        e: ElementRef,
        ty: String,
    },
    InsertMember {
        owner: ElementRef,
        text: String,
    },
    InsertTopLevel {
        unit_name: String,
        text: String,
    },
    AddUnit {
        name: String,
    },
    Remove {
        e: ElementRef,
    },
    ReplaceMember {
        e: ElementRef,
        text: String,
    },
    Retarget {
        site: RefSite,
        to: ElementRef,
    },
    ExtractDefinition {
        usage: ElementRef,
        name: Option<String>,
    },
    HoistToUnit {
        e: ElementRef,
        unit_name: String,
        new_name: Option<String>,
    },
    InlineDefinition {
        definition: ElementRef,
    },
    MoveMember {
        e: ElementRef,
        new_owner: ElementRef,
        index: Option<usize>,
    },
}

impl Op {
    /// The element whose text the edit reads or rewrites, when it has
    /// one — the handle the library guard checks. A move's destination
    /// and a retarget's new target are checked by their own planners;
    /// extract and inline answer through their eligibility gates, which
    /// name the refusal precisely.
    fn subject(&self) -> Option<ElementRef> {
        match self {
            Op::Rename { e, .. }
            | Op::SetFeatureValue { e, .. }
            | Op::SetFeatureType { e, .. }
            | Op::Remove { e }
            | Op::ReplaceMember { e, .. }
            | Op::HoistToUnit { e, .. }
            | Op::MoveMember { e, .. } => Some(*e),
            Op::InsertMember { owner, .. } => Some(*owner),
            Op::Retarget { site, .. } => Some(site.owner),
            Op::InsertTopLevel { .. }
            | Op::AddUnit { .. }
            | Op::ExtractDefinition { .. }
            | Op::InlineDefinition { .. } => None,
        }
    }
}

/// One committed batch's outcome.
#[derive(Debug, Default)]
pub struct CommitReport {
    /// Interchange `@id` changes for elements whose ownership path moved
    /// (renames rewrite the paths of the element and its descendants):
    /// `(old id, new id)`, matched by qualified name through the rename
    /// map. Unchanged elements keep their deterministic ids and do not
    /// appear.
    pub id_map: Vec<(Uuid, Uuid)>,
    /// Non-fatal observations (e.g. the unresolved-reference count moved
    /// because inserted text references something absent).
    pub findings: Vec<String>,
    /// The text replacements the commit applied, in **pre-commit**
    /// coordinates (byte offsets into each unit's previous source),
    /// ordered by (unit, start) and non-overlapping. A caller mirroring
    /// the session's sources elsewhere (an editor buffer, a review UI)
    /// can replay exactly these instead of diffing whole units.
    pub splices: Vec<AppliedSplice>,
}

/// One applied text replacement from a committed edit batch, in
/// pre-commit coordinates.
#[derive(Debug, Clone)]
pub struct AppliedSplice {
    /// Unit name (as given to the session), not a resolver index.
    pub unit: String,
    /// Replaced byte range in the unit's pre-commit source.
    pub start: u32,
    pub end: u32,
    /// Replacement text.
    pub text: String,
}

/// How a split names the files it creates.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Default)]
pub enum SplitNaming {
    /// The package name as written (`02 JPL.sysml`).
    #[default]
    Keep,
    /// Letters, digits, `.`, `_` and `-` only; runs of anything else
    /// become one `-` (`02-JPL.sysml`).
    Slug,
}

/// Options for [`Session::split_plan`].
#[derive(Clone, Debug, Default)]
pub struct SplitOptions {
    pub naming: SplitNaming,
    /// Directory (unit-name prefix) for the new units; by default the
    /// root's unit name without its extension (`models/TMT.sysml` →
    /// `models/TMT`).
    pub directory: Option<String>,
    /// Unit names are URIs (an editor's workspace): the new units' file
    /// segments are percent-encoded the way editors spell a path
    /// segment — every byte outside the unreserved set (letters,
    /// digits, `-` `.` `_` `~`) as `%XX` — so a name with a space or a
    /// sub-delimiter yields the exact string the editor opens the
    /// created file under. Off for path-named (CLI) sessions.
    pub uri_units: bool,
}

/// One package of a split: where it goes and what it is called there.
#[derive(Clone, Debug)]
pub struct SplitEntry {
    pub package: ElementRef,
    /// Qualified name before the split.
    pub qualified: String,
    pub name: String,
    /// The root-level name the package takes when its own would collide
    /// with a name the model already resolves or another hoisted package.
    pub new_name: Option<String>,
    /// Name of the new unit (a relative file path for CLI sessions).
    pub unit: String,
    /// Size of the package's text, for reporting.
    pub bytes: usize,
}

/// A planned split — see [`Session::split_plan`].
#[derive(Clone, Debug)]
pub struct SplitPlan {
    pub root: ElementRef,
    /// Unit the root package is declared in.
    pub root_unit: String,
    pub directory: String,
    pub entries: Vec<SplitEntry>,
}

/// A name as one path segment: path separators and NUL become `-`, and
/// a name that would climb or vanish becomes `package`.
fn file_segment(name: &str) -> String {
    let out: String = name
        .chars()
        .map(|c| {
            if matches!(c, '/' | '\\' | '\0') {
                '-'
            } else {
                c
            }
        })
        .collect();
    if out.is_empty() || out == "." || out == ".." {
        "package".to_string()
    } else {
        out
    }
}

/// A file segment as a URI path segment: bytes outside the unreserved
/// set (`A-Z a-z 0-9 - . _ ~`) become `%XX` (uppercase hex, UTF-8
/// bytes), the spelling editors give a created file's uri.
fn uri_segment(name: &str) -> String {
    const HEX: &[u8; 16] = b"0123456789ABCDEF";
    let mut out = String::with_capacity(name.len());
    for b in name.bytes() {
        if b.is_ascii_alphanumeric() || matches!(b, b'-' | b'.' | b'_' | b'~') {
            out.push(b as char);
        } else {
            out.push('%');
            out.push(HEX[usize::from(b >> 4)] as char);
            out.push(HEX[usize::from(b & 0x0F)] as char);
        }
    }
    out
}

/// A file-name slug: letters, digits, `.`, `_`, `-`; anything else
/// collapses to one `-`.
fn slug(name: &str) -> String {
    let mut out = String::with_capacity(name.len());
    let mut dash = false;
    for c in name.chars() {
        if c.is_alphanumeric() || matches!(c, '.' | '_' | '-') {
            out.push(c);
            dash = false;
        } else if !dash && !out.is_empty() {
            out.push('-');
            dash = true;
        }
    }
    let out = out.trim_end_matches('-').to_string();
    if out.is_empty() {
        "package".to_string()
    } else {
        out
    }
}

/// Remove `indent` from the start of every line after the first that
/// carries it. Returns the text and, per line, (old start, new start)
/// offsets for mapping positions.
fn dedent_lines(text: &str, indent: &str) -> (String, Vec<(u32, u32)>) {
    let mut out = String::with_capacity(text.len());
    let mut lines = Vec::new();
    let mut old_pos = 0u32;
    for (i, line) in text.split_inclusive('\n').enumerate() {
        let stripped = if i > 0 && !indent.is_empty() && line.starts_with(indent) {
            &line[indent.len()..]
        } else {
            line
        };
        let new_start = out.len() as u32;
        let old_start = old_pos + (line.len() - stripped.len()) as u32;
        lines.push((old_start, new_start));
        out.push_str(stripped);
        old_pos += line.len() as u32;
    }
    (out, lines)
}

/// An accumulating edit batch over a [`Session`].
#[must_use = "an edit batch does nothing until committed"]
pub struct EditBuilder<'s> {
    session: &'s mut Session,
    ops: Vec<Op>,
    /// Colliding renames (see [`Self::skip_colliding_renames`]) are
    /// dropped from the batch and reported instead of refusing it.
    skip_colliding_renames: bool,
}

/// One planned text replacement, in pre-commit coordinates.
struct Splice {
    unit: usize,
    start: u32,
    end: u32,
    text: String,
    /// Expected targets for reference sites this splice writes — one per
    /// generated reference (a rename/retarget rewrites one; synthesized
    /// headers may carry several typing/specialization targets). Each is
    /// verified post-commit at the splice's new location.
    expects: Vec<SpliceExpect>,
}

struct SpliceExpect {
    /// Expected qualified name of the site's target, in pre-commit
    /// spellings — verification maps it through the batch's rename/move
    /// correspondences before comparing (a sibling op may rename an
    /// ancestor). With `new_leaf`, the final segment is already the
    /// post-commit name and only the ancestor path is mapped.
    qn: String,
    /// The final segment spells the target's *new* name (a rename
    /// rewrite); everything before it is still pre-commit.
    new_leaf: bool,
    /// Byte range of the reference's final segment within the splice
    /// text (the post-commit `name_span` is `offset..offset + len`
    /// shifted by the splice's new position).
    offset: u32,
    len: u32,
}

impl EditBuilder<'_> {
    /// Rename `e`: respell its declaration and every reference site
    /// written with its current name (sites spelled through aliases or
    /// effective names are left alone — if the rename strands one, the
    /// commit's semantic-identity check rejects it).
    pub fn rename(&mut self, e: ElementRef, new_name: &str) -> &mut Self {
        self.ops.push(Op::Rename {
            e,
            new_name: new_name.to_string(),
        });
        self
    }

    /// Drop, instead of refusing on, every rename whose new name a
    /// sibling in the same owner already carries after the batch (a
    /// declared or short name the batch leaves in place, or a name
    /// another rename in the batch gives a sibling). By default such a
    /// rename refuses the whole batch with
    /// [`TransformError::NameTaken`] before anything is planned; with
    /// this policy the rest of the batch commits and each dropped
    /// rename is one line of [`CommitReport::findings`]. Built for
    /// bulk fix-all batches, where one clashing suggestion must not
    /// hold up thousands of legal renames.
    pub fn skip_colliding_renames(&mut self) -> &mut Self {
        self.skip_colliding_renames = true;
        self
    }

    /// Replace `e`'s feature value expression (`= …`), or add one before
    /// the terminating `;` when the declaration has none.
    pub fn set_feature_value(&mut self, e: ElementRef, expr: &str) -> &mut Self {
        self.ops.push(Op::SetFeatureValue {
            e,
            expr: expr.to_string(),
        });
        self
    }

    /// Set `e`'s declared type in place: replace the written `: T`
    /// clause with `ty` (spelled as written — a name or qualified name),
    /// or add one where the declaration has none — after the declared
    /// name, or after the last specialization clause of an unnamed
    /// feature (`:>> mass` → `:>> mass : T`). Declaration position,
    /// value, and body are untouched. Whether the new spelling resolves
    /// surfaces through the commit's findings (unresolved-count change),
    /// like inserted member text.
    pub fn set_feature_type(&mut self, e: ElementRef, ty: &str) -> &mut Self {
        self.ops.push(Op::SetFeatureType {
            e,
            ty: ty.to_string(),
        });
        self
    }

    /// Insert `text` as the last member of `owner`'s body (a
    /// `;`-terminated declaration grows a body).
    pub fn insert_member(&mut self, owner: ElementRef, text: &str) -> &mut Self {
        self.ops.push(Op::InsertMember {
            owner,
            text: text.to_string(),
        });
        self
    }

    /// Append `text` as a top-level member of the named unit.
    pub fn insert_top_level(&mut self, unit_name: &str, text: &str) -> &mut Self {
        self.ops.push(Op::InsertTopLevel {
            unit_name: unit_name.to_string(),
            text: text.to_string(),
        });
        self
    }

    /// Create a new, empty unit under `name`. Refuses a name the
    /// session already holds. Later ops in the same batch may write into
    /// it (`insert_top_level`, `hoist_to_unit`); it joins the session at
    /// commit.
    pub fn add_unit(&mut self, name: &str) -> &mut Self {
        self.ops.push(Op::AddUnit {
            name: name.to_string(),
        });
        self
    }

    /// Remove the member declaration that created `e` (and everything it
    /// owns). Fails at commit if any reference outside the removed text
    /// targets the element or its descendants.
    pub fn remove(&mut self, e: ElementRef) -> &mut Self {
        self.ops.push(Op::Remove { e });
        self
    }

    /// Replace the member declaration that created `e` (and everything
    /// it owns) with exactly one new member parsed from `text` —
    /// identity-preserving update, where `remove` + `insert_member`
    /// would refuse any member that outside references target. When the
    /// declared name changes, reference sites written with the old name
    /// are respelled to the new one and the old→new qualified-name
    /// correspondence is recorded (reported in the commit's id map like
    /// a rename); alias and short-name spellings stay as written and
    /// must still resolve post-commit — the standard verification. No
    /// pre-state outside-reference refusal: validity is judged on the
    /// post-edit model.
    pub fn replace_member(&mut self, e: ElementRef, text: &str) -> &mut Self {
        self.ops.push(Op::ReplaceMember {
            e,
            text: text.to_string(),
        });
        self
    }

    /// Respell one reference site to denote `to` (written as `to`'s
    /// qualified name; the commit verifies it resolves there).
    pub fn retarget(&mut self, site: RefSite, to: ElementRef) -> &mut Self {
        self.ops.push(Op::Retarget { site, to });
        self
    }

    /// Move the member declaration that created `e` into `new_owner`'s
    /// body, at `index` among its current lexical members (`e` itself
    /// excluded; `None` or past-the-end appends). Same-owner moves
    /// reorder; cross-owner moves re-parent, and the ownership-path
    /// change re-verifies every reference — outside spellings must
    /// still denote the moved element, references carried inside the
    /// moved text must still resolve to their old targets — or the
    /// commit rolls back. Multi-line members keep their internal
    /// indentation as written.
    pub fn move_member(
        &mut self,
        e: ElementRef,
        new_owner: ElementRef,
        index: Option<usize>,
    ) -> &mut Self {
        self.ops.push(Op::MoveMember {
            e,
            new_owner,
            index,
        });
        self
    }

    /// Hoist the member declaration that created `e` (a package, as a
    /// rule) to the top level of `unit_name` — an existing unit, or one
    /// this batch adds — under `new_name` when given. The moved text is
    /// dedented to the top level and every reference written inside it
    /// to something outside it is respelled by its reference spelling,
    /// so the moved body resolves on its own; references from elsewhere
    /// keep resolving when the old owner re-exports the moved package
    /// (see [`Session::split_plan`]). Verified like a move.
    pub fn hoist_to_unit(
        &mut self,
        e: ElementRef,
        unit_name: &str,
        new_name: Option<&str>,
    ) -> &mut Self {
        self.ops.push(Op::HoistToUnit {
            e,
            unit_name: unit_name.to_string(),
            new_name: new_name.map(str::to_string),
        });
        self
    }

    /// Apply a [`SplitPlan`]: every entry's package is hoisted into its
    /// own new unit and the root package re-exports it — `public import
    /// <name>;`, or `public alias <old> for <new>;` when the package was
    /// renamed to avoid a root-level collision — so every qualified
    /// reference through the root keeps resolving.
    pub fn split(&mut self, plan: &SplitPlan) -> &mut Self {
        for entry in &plan.entries {
            self.add_unit(&entry.unit);
        }
        for entry in &plan.entries {
            self.hoist_to_unit(entry.package, &entry.unit, entry.new_name.as_deref());
        }
        for entry in &plan.entries {
            let text = match &entry.new_name {
                Some(new) => format!(
                    "public alias {} for {};",
                    spell_name(&entry.name),
                    spell_name(new)
                ),
                None => format!("public import {};", spell_name(&entry.name)),
            };
            self.insert_member(plan.root, &text);
        }
        self
    }

    /// Extract `usage`'s inline body into a fresh definition: the
    /// body region moves byte-preserved into a
    /// `<keyword> def` inserted as the sibling immediately before the
    /// usage; plain typings generalize to definition specializations
    /// (`: A` → `:> A`); the usage keeps everything else and is retyped
    /// by the new definition (`part engine : A { … }` →
    /// `part def Engine :> A { … }` + `part engine : Engine;`).
    ///
    /// `name` `None` synthesizes UpperCamel from the usage's declared
    /// name (`fuel_tank` → `FuelTank`); a sibling already declaring the
    /// name refuses with [`TransformError::NameTaken`]. Eligibility is
    /// the eligibility policy ([`eligibility::ExtractRefusal`] via
    /// [`TransformError::ExtractIneligible`]). The commit runs under
    /// relocation discipline: every generated reference target is
    /// expectation-verified, any newly unresolved reference refuses,
    /// and the usage's effective-member projection must be unchanged
    /// under the correspondence map.
    pub fn extract_definition(&mut self, usage: ElementRef, name: Option<&str>) -> &mut Self {
        self.ops.push(Op::ExtractDefinition {
            usage,
            name: name.map(str::to_string),
        });
        self
    }

    /// Inline `definition` into its sole typed usage:
    /// the definition's body members splice in **before** the usage's
    /// own body members (each region's order and documentation
    /// preserved), the usage's typing entry is retargeted to the
    /// definition's plain specializations (or dropped when it has
    /// none — the implied library base applies), and the definition is
    /// deleted — all in one atomic, verified commit.
    ///
    /// Inlining a definition just produced by
    /// [`Self::extract_definition`] restores the original usage
    /// byte-for-byte; no reverse-placement or body-partition promise is
    /// made for arbitrary definitions. Eligibility is the policy
    /// ([`eligibility::InlineRefusal`] via
    /// [`TransformError::InlineIneligible`]): sole plain FeatureTyping,
    /// provenance-classified incoming references, no member-name
    /// collisions. The commit runs under relocation discipline and
    /// reports imports the deletion left unused as findings (the
    /// unused-import quick fix removes them) rather than deleting them itself.
    pub fn inline_definition(&mut self, definition: ElementRef) -> &mut Self {
        self.ops.push(Op::InlineDefinition { definition });
        self
    }

    /// Apply the batch: plan splices, apply, reparse, rebuild, verify
    /// semantic identity — or roll back and report why.
    pub fn commit(self) -> Result<CommitReport, TransformError> {
        self.run(false)
    }

    /// Dry-run the batch: the full verified-commit pipeline — plan,
    /// splice, reparse, rebuild, semantic identity — against copies,
    /// with the session untouched either way. `Ok(report)` is exactly
    /// what [`Self::commit`] would have returned (splices, findings,
    /// id map); `Err` is exactly the refusal it would have rolled back
    /// with.
    pub fn check(self) -> Result<CommitReport, TransformError> {
        self.run(true)
    }

    fn run(self, dry_run: bool) -> Result<CommitReport, TransformError> {
        let EditBuilder {
            session,
            ops,
            skip_colliding_renames,
        } = self;
        let mut planner = Planner::new(session);
        let skipped = planner.rename_collisions(&ops, skip_colliding_renames)?;
        if !ops.is_empty() && skipped.len() == ops.len() {
            // Every op was dropped: nothing to splice, the session is
            // untouched, and the report says why.
            return Ok(CommitReport {
                findings: skipped.into_values().collect(),
                ..CommitReport::default()
            });
        }
        for (i, op) in ops.iter().enumerate() {
            if skipped.contains_key(&i) {
                continue;
            }
            planner.plan(op)?;
        }
        planner.findings.extend(skipped.into_values());
        planner.commit(dry_run)
    }
}

// ---------------------------------------------------------------------------
// Planning + commit pipeline
// ---------------------------------------------------------------------------

struct Planner<'s> {
    session: &'s mut Session,
    splices: Vec<Splice>,
    /// The element-correspondence map: (old qualified name, new
    /// qualified name) per element whose identity the batch relocates —
    /// renames, moves, and extracted/inlined subtree roots.
    /// Descendants correspond through prefix mapping (`map_qn`), so one
    /// entry covers a whole moved subtree; untouched sites verify
    /// against the mapped target, carried sites at their destination.
    correspondence: Vec<(String, String)>,
    /// Pre-commit spans whose *contents* are edited or removed — old
    /// sites inside them carry no expectation.
    consumed: Vec<(usize, Span)>,
    /// Reference sites carried inside moved text (`move_member`), to be
    /// re-verified at their post-insert positions.
    moved_expects: Vec<MovedExpects>,
    /// Relocation discipline: when set (relocating ops — extract /
    /// inline opt in), any reference that resolved before the commit but
    /// not after is a refusal, not a finding — the general pipeline's
    /// unresolved-count delta is not strict enough for ops that
    /// synthesize headers and move bodies.
    refuse_new_unresolved: bool,
    /// Elements whose effective-member projection must be structurally
    /// identical across the commit (by qualified name — relocation ops
    /// register the touched usage; its own name never moves). Compared
    /// under the correspondence map after the reference nets pass.
    projection_subjects: Vec<String>,
    /// Inline sets this: the deletion can leave imports unused; they
    /// are reported as findings (the unused-import quick fix removes them) —
    /// never deleted in the same commit.
    report_unused_imports: bool,
    /// Units this batch creates (empty, appended at commit before the
    /// rebuild). Not splices — splices key existing unit indices.
    new_units: Vec<String>,
    /// Findings recorded while planning (dropped colliding renames);
    /// they lead the committed report's findings.
    findings: Vec<String>,
}

/// One `move_member`'s carried reference sites: the destination
/// splice's identity (unit, start, full text — how it is found again
/// after the commit sorts/dedups) plus each site's (offset within the
/// splice text, length, pre-commit target qualified name; `None` =
/// only require that it resolves).
struct MovedExpects {
    unit: usize,
    at: u32,
    text: String,
    sites: Vec<(u32, u32, Option<String>)>,
}

impl<'s> Planner<'s> {
    fn new(session: &'s mut Session) -> Self {
        Planner {
            session,
            splices: Vec::new(),
            correspondence: Vec::new(),
            consumed: Vec::new(),
            moved_expects: Vec::new(),
            refuse_new_unresolved: false,
            projection_subjects: Vec::new(),
            report_unused_imports: false,
            new_units: Vec::new(),
            findings: Vec::new(),
        }
    }

    /// Text of a user unit, or the empty text of a unit this batch
    /// adds. `None` for a library unit: no edit reads one.
    fn src(&self, unit: usize) -> Option<&str> {
        self.session
            .source(unit)
            .or_else(|| self.is_born(unit).then_some(""))
    }

    /// [`Self::src`] for the unit `subject` lives in — a library unit
    /// refuses with [`TransformError::NotDeclared`].
    fn user_src(&self, unit: usize, subject: ElementRef) -> Result<&str, TransformError> {
        self.src(unit).ok_or(TransformError::NotDeclared(subject))
    }

    /// Whether `unit` is a unit this batch adds — it joins the session
    /// empty at commit, after every existing unit.
    fn is_born(&self, unit: usize) -> bool {
        let first = self.session.unit_offset + self.session.sources.len();
        (first..first + self.new_units.len()).contains(&unit)
    }

    /// Name of an existing or born unit by model unit index.
    fn unit_name(&self, unit: usize) -> String {
        let local = unit - self.session.unit_offset;
        match self.session.sources.get(local) {
            Some((name, _)) => name.clone(),
            None => self.new_units[local - self.session.sources.len()].clone(),
        }
    }

    /// Model unit index of an existing or born unit by name.
    fn unit_by_name(&self, name: &str) -> Option<usize> {
        if let Some((u, _, _)) = self.session.units().find(|(_, n, _)| *n == name) {
            return Some(u);
        }
        let first = self.session.unit_offset + self.session.sources.len();
        self.new_units
            .iter()
            .position(|n| n == name)
            .map(|k| first + k)
    }

    fn plan(&mut self, op: &Op) -> Result<(), TransformError> {
        // Library elements are resolution targets only. An edit whose
        // subject lives in a library unit is refused here, before any
        // op reads the subject's text or plans a splice into its unit.
        if let Some(subject) = op.subject() {
            if self.session.resolved.is_library_element(subject) {
                return Err(TransformError::NotDeclared(subject));
            }
        }
        match op {
            Op::Rename { e, new_name } => self.plan_rename(*e, new_name),
            Op::SetFeatureValue { e, expr } => self.plan_set_value(*e, expr),
            Op::SetFeatureType { e, ty } => self.plan_set_type(*e, ty),
            Op::InsertMember { owner, text } => self.plan_insert(*owner, text),
            Op::InsertTopLevel { unit_name, text } => self.plan_insert_top(unit_name, text),
            Op::AddUnit { name } => self.plan_add_unit(name),
            Op::Remove { e } => self.plan_remove(*e),
            Op::ReplaceMember { e, text } => self.plan_replace(*e, text),
            Op::Retarget { site, to } => self.plan_retarget(site, *to),
            Op::MoveMember {
                e,
                new_owner,
                index,
            } => self.plan_move(*e, *new_owner, *index),
            Op::ExtractDefinition { usage, name } => self.plan_extract(*usage, name.as_deref()),
            Op::HoistToUnit {
                e,
                unit_name,
                new_name,
            } => self.plan_hoist(*e, unit_name, new_name.as_deref()),
            Op::InlineDefinition { definition } => self.plan_inline(*definition),
        }
    }

    /// The renames in `ops` whose new name collides with a sibling's:
    /// a name another member of the same owner still carries after the
    /// batch (its declared name unless the batch renames it away, its
    /// short name regardless, the effective name of an unnamed
    /// feature), or a name an earlier rename in the batch already gives
    /// a sibling. Two members of one namespace sharing a name make every
    /// qualified reference to either ambiguous — the commit's
    /// verification would refuse the batch at each such site, without
    /// saying which rename caused it. Returns op index → finding text;
    /// without `skip`, the first collision is a
    /// [`TransformError::NameTaken`] refusal instead.
    fn rename_collisions(
        &mut self,
        ops: &[Op],
        skip: bool,
    ) -> Result<BTreeMap<usize, String>, TransformError> {
        let renamed: HashSet<ElementRef> = ops
            .iter()
            .filter_map(|op| match op {
                Op::Rename { e, .. } => Some(*e),
                _ => None,
            })
            .collect();
        let mut out = BTreeMap::new();
        if renamed.is_empty() {
            return Ok(out);
        }
        let r = self.session.resolved();
        // Per owner (`None` = the root namespace): the names its members
        // keep, and the names the batch's renames claim, each to the
        // element carrying it.
        let mut taken: HashMap<Option<ElementRef>, HashMap<String, ElementRef>> = HashMap::new();
        let mut claimed: HashMap<Option<ElementRef>, HashMap<String, ElementRef>> = HashMap::new();
        let mut roots: Option<Vec<ElementRef>> = None;
        for (i, op) in ops.iter().enumerate() {
            let Op::Rename { e, new_name } = op else {
                continue;
            };
            let owner = r.owner(*e);
            let names = taken.entry(owner).or_insert_with(|| {
                let siblings: Vec<ElementRef> = match owner {
                    Some(o) => r.owned_members(o),
                    None => roots
                        .get_or_insert_with(|| {
                            // Owner lookups memoize, so the candidates
                            // are read out before they are filtered.
                            let mut all: Vec<ElementRef> = r.user_elements().collect();
                            all.retain(|x| r.owner(*x).is_none());
                            all
                        })
                        .clone(),
                };
                let mut names: HashMap<String, ElementRef> = HashMap::new();
                for sib in siblings {
                    if !renamed.contains(&sib) {
                        // What lookup finds the sibling by, not the
                        // specification's effective name.
                        if let Some(n) = r.element_lookup_name(sib) {
                            names.entry(n).or_insert(sib);
                        }
                    }
                    if let Some(sn) = r.element_declared_short_name(sib) {
                        names.entry(sn.to_string()).or_insert(sib);
                    }
                }
                names
            });
            let existing = names
                .get(new_name.as_str())
                .copied()
                .filter(|x| x != e)
                .map(|x| (x, false))
                .or_else(|| {
                    claimed
                        .get(&owner)
                        .and_then(|c| c.get(new_name.as_str()))
                        .copied()
                        .map(|x| (x, true))
                });
            let Some((other, by_batch)) = existing else {
                claimed
                    .entry(owner)
                    .or_default()
                    .entry(new_name.clone())
                    .or_insert(*e);
                continue;
            };
            let other_qn = r
                .element_qualified_name(other)
                .unwrap_or_else(|| format!("{other:?}"));
            if !skip {
                return Err(TransformError::NameTaken {
                    name: new_name.clone(),
                    existing: if by_batch {
                        format!("{other_qn} (renamed to `{new_name}` in the same batch)")
                    } else {
                        other_qn
                    },
                });
            }
            let old_qn = r
                .element_qualified_name(*e)
                .unwrap_or_else(|| format!("{e:?}"));
            out.insert(
                i,
                if by_batch {
                    format!(
                        "rename of `{old_qn}` to `{new_name}` skipped: the batch already renames its sibling `{other_qn}` to `{new_name}`"
                    )
                } else {
                    format!(
                        "rename of `{old_qn}` to `{new_name}` skipped: its sibling `{other_qn}` is already named `{new_name}`"
                    )
                },
            );
        }
        Ok(out)
    }

    fn plan_rename(&mut self, e: ElementRef, new_name: &str) -> Result<(), TransformError> {
        if new_name.is_empty() {
            return Err(TransformError::InvalidName(new_name.to_string()));
        }
        let r = self.session.resolved();
        let (decl_unit, decl_span) = r
            .declaration_site(e)
            .ok_or(TransformError::NotDeclared(e))?;
        let old_qn = r
            .element_qualified_name(e)
            .ok_or(TransformError::NotDeclared(e))?;
        let old_raw = decode_name(slice(self.user_src(decl_unit, e)?, decl_span));
        let spelled = spell_name(new_name);
        // Qualified-name strings follow `element_qualified_name`'s
        // convention (escape_name, reserved words unquoted) — the
        // reserved-aware quoting is for the spliced *token* only.
        let qn_seg = escape_name(new_name);
        let new_qn = match old_qn.rfind("::") {
            Some(i) => format!("{}{}", &old_qn[..i + 2], qn_seg),
            None => qn_seg,
        };
        self.correspondence.push((old_qn, new_qn.clone()));

        // The declaration is not a reference site — no expectation.
        self.splices.push(Splice {
            unit: decl_unit,
            start: decl_span.start,
            end: decl_span.end,
            text: spelled.clone(),
            expects: Vec::new(),
        });
        for site in self.session.resolved().references_to(e) {
            // Only sites written with the element's own name are
            // respelled; alias/effective-name spellings stay. (Sites
            // are recorded in user units only.)
            let Some(site_src) = self.src(site.unit) else {
                continue;
            };
            if decode_name(slice(site_src, site.name_span)) == old_raw {
                self.splices.push(Splice {
                    unit: site.unit,
                    start: site.name_span.start,
                    end: site.name_span.end,
                    text: spelled.clone(),
                    expects: vec![SpliceExpect {
                        qn: new_qn.clone(),
                        new_leaf: true,
                        offset: 0,
                        len: spelled.len() as u32,
                    }],
                });
            }
        }
        Ok(())
    }

    fn plan_set_value(&mut self, e: ElementRef, expr: &str) -> Result<(), TransformError> {
        let parsed = parse_expression(expr);
        if parsed.expr.is_none() {
            return Err(TransformError::InvalidExpression {
                text: expr.to_string(),
                message: parsed
                    .diagnostics
                    .first()
                    .map(|d| d.message.clone())
                    .unwrap_or_else(|| "not an expression".into()),
            });
        }
        let r = self.session.resolved();
        if let Some((_, old)) = r.value_expr(e) {
            let (unit, _) = r
                .declaration_site(e)
                .or_else(|| r.member_extent(e))
                .ok_or(TransformError::NoEditableValue(e))?;
            self.consumed.push((unit, old.span));
            self.splices.push(Splice {
                unit,
                start: old.span.start,
                end: old.span.end,
                text: expr.trim().to_string(),
                expects: Vec::new(),
            });
            return Ok(());
        }
        // No value: extend a `;`-terminated declaration with ` = expr`.
        let (unit, extent) = r
            .member_extent(e)
            .ok_or(TransformError::NoEditableValue(e))?;
        let src = self.user_src(unit, e)?;
        if !slice(src, extent).ends_with(';') {
            return Err(TransformError::NoEditableValue(e));
        }
        self.splices.push(Splice {
            unit,
            start: extent.end - 1,
            end: extent.end - 1,
            text: format!(" = {}", expr.trim()),
            expects: Vec::new(),
        });
        Ok(())
    }

    fn plan_set_type(&mut self, e: ElementRef, ty: &str) -> Result<(), TransformError> {
        let ty = ty.trim();
        // Validate the spelling as a typing target in a probe
        // declaration (names, qualified names, quoted names all pass;
        // stray tokens fail here instead of at reparse).
        let probe = format!("package __p {{ attribute __x : {ty}; }}");
        let parse = parse_source(&probe);
        if !parse.diagnostics.is_empty() {
            return Err(TransformError::InvalidType {
                text: ty.to_string(),
                message: parse.diagnostics[0].message.clone(),
            });
        }
        let r = self.session.resolved();
        let typings = r.typing_spans(e);
        match typings.as_slice() {
            [] => {}
            [(unit, span)] => {
                // Replace the written clause in place.
                self.consumed.push((*unit, *span));
                self.splices.push(Splice {
                    unit: *unit,
                    start: span.start,
                    end: span.end,
                    text: ty.to_string(),
                    expects: Vec::new(),
                });
                return Ok(());
            }
            _ => return Err(TransformError::AmbiguousTyping(e)),
        }
        // No written typing: add `: T` after the declared name, or after
        // the last specialization clause of an unnamed feature
        // (`attribute :>> mass = 10;` → `attribute :>> mass : T = 10;`).
        let at = r
            .declaration_site(e)
            .or_else(|| {
                r.specialization_spans(e)
                    .into_iter()
                    .max_by_key(|&(_, sp)| sp.end)
            })
            .ok_or(TransformError::NotDeclared(e))?;
        self.splices.push(Splice {
            unit: at.0,
            start: at.1.end,
            end: at.1.end,
            text: format!(" : {ty}"),
            expects: Vec::new(),
        });
        Ok(())
    }

    fn validate_member_text(text: &str) -> Result<(), TransformError> {
        let probe = format!("package __p {{ {text} }}");
        let parse = parse_source(&probe);
        if !parse.diagnostics.is_empty() {
            return Err(TransformError::InvalidMember {
                text: text.to_string(),
                message: parse.diagnostics[0].message.clone(),
            });
        }
        Ok(())
    }

    fn plan_insert(&mut self, owner: ElementRef, text: &str) -> Result<(), TransformError> {
        Self::validate_member_text(text)?;
        let (unit, extent) = self
            .session
            .resolved()
            .member_extent(owner)
            .ok_or(TransformError::NoExtent(owner))?;
        let src = self.user_src(unit, owner)?;
        let indent = line_indent(src, extent.start);
        let child = child_indent(&indent, src);
        // The member arrives in top-level form; every line is
        // re-spelled at the destination's depth in the unit's own
        // indent style, so a nested insert reads as if written there.
        let text = reindent_member_text(text, &child, indent_unit(&indent, src));
        let text = text.as_str();
        let last = extent.end - 1;
        match src.as_bytes()[last as usize] {
            b'}' => {
                // Insert before the closing brace as a PURE insertion
                // (start == end): a replacement that consumed the
                // brace's leading whitespace would overlap an identical
                // replacement from a sibling insert into the same owner
                // — pure insertions at one point stack instead, which
                // is what lets a batch append many members to one body.
                let mut at = last;
                let bytes = src.as_bytes();
                while at > extent.start && matches!(bytes[at as usize - 1], b' ' | b'\t') {
                    at -= 1;
                }
                let after_newline = at > extent.start && bytes[at as usize - 1] == b'\n';
                let (pos, text) = if after_newline {
                    // …\n[ws]} — slot in before the brace's indentation.
                    (at, format!("{child}{text}\n"))
                } else {
                    // Single-line body: break before the brace, and give
                    // the brace its owner indentation on the new line.
                    (last, format!("\n{child}{text}\n{indent}"))
                };
                self.splices.push(Splice {
                    unit,
                    start: pos,
                    end: pos,
                    text,
                    expects: Vec::new(),
                });
            }
            b';' => {
                // Grow a body: `part p : T;` → `part p : T { … }`.
                self.splices.push(Splice {
                    unit,
                    start: last,
                    end: last + 1,
                    text: format!(" {{\n{child}{text}\n{indent}}}"),
                    expects: Vec::new(),
                });
            }
            _ => return Err(TransformError::NoExtent(owner)),
        }
        Ok(())
    }

    fn plan_insert_top(&mut self, unit_name: &str, text: &str) -> Result<(), TransformError> {
        Self::validate_member_text(text)?;
        let unit = self
            .unit_by_name(unit_name)
            .ok_or_else(|| TransformError::UnknownUnit(unit_name.to_string()))?;
        let src = self
            .src(unit)
            .ok_or_else(|| TransformError::UnknownUnit(unit_name.to_string()))?;
        let src_len = src.len() as u32;
        let needs_newline = !src.is_empty() && !src.ends_with('\n');
        // Top level: no base indent, but internal levels still convert
        // to the unit's own indent style.
        let text = reindent_member_text(text, "", indent_unit("", src));
        self.splices.push(Splice {
            unit,
            start: src_len,
            end: src_len,
            text: if needs_newline {
                format!("\n{text}\n")
            } else {
                format!("{text}\n")
            },
            expects: Vec::new(),
        });
        Ok(())
    }

    fn plan_add_unit(&mut self, name: &str) -> Result<(), TransformError> {
        // A blank name would open a unit the session could not emit.
        if name.trim().is_empty() {
            return Err(TransformError::InvalidName(name.to_string()));
        }
        if self.session.units().any(|(_, n, _)| n == name)
            || self.new_units.iter().any(|n| n == name)
        {
            return Err(TransformError::UnitExists(name.to_string()));
        }
        self.new_units.push(name.to_string());
        Ok(())
    }

    fn plan_remove(&mut self, e: ElementRef) -> Result<(), TransformError> {
        let r = self.session.resolved();
        let (unit, mut extent) = r.member_extent(e).ok_or(TransformError::NoExtent(e))?;
        if r.element_type(e) == "SuccessionAsUsage" {
            // A leading `then` and its following declaration share an outer
            // source extent. Removing the relationship must retain the action.
            let source = slice(self.user_src(unit, e)?, extent);
            let parsed = parse_source(source);
            if let Some(member) = parsed.unit.members.first().filter(|m| m.leading_then) {
                let (tokens, _) = sysmlv2_syntax::lexer::tokenize(source);
                if let Some(token) = tokens.iter().find(|t| {
                    t.kind == TokenKind::Ident
                        && &source[t.span.start as usize..t.span.end as usize] == "then"
                }) {
                    let end = member
                        .leading_then_multiplicity
                        .as_ref()
                        .map_or(token.span.end, |m| m.span.end);
                    extent = Span::new(extent.start + token.span.start, extent.start + end);
                }
            }
        }
        let r = self.session.resolved();
        let element = r
            .element_qualified_name(e)
            .unwrap_or_else(|| format!("{:?}", e));
        // References from outside the removed text into it strand — fail
        // now, naming them. "Into it" = the target's own extent (or
        // declaration) lies within the removed range.
        let inside =
            |u: usize, sp: Span| u == unit && sp.start >= extent.start && sp.end <= extent.end;
        let mut broken = Vec::new();
        for site in r.reference_sites().to_vec() {
            if inside(site.unit, site.name_span) {
                continue; // the reference is removed along with the member
            }
            // A site inside a span an earlier op in this batch already
            // consumes is leaving with that op — a provenance record
            // removed alongside the member it describes must not veto
            // the member's removal. Post-state verification still rules.
            if self.consumed.iter().any(|&(u, c)| {
                u == site.unit && site.name_span.start >= c.start && site.name_span.end <= c.end
            }) {
                continue;
            }
            let target_home = r
                .member_extent(site.target)
                .or_else(|| r.declaration_site(site.target));
            if target_home.is_some_and(|(u, sp)| inside(u, sp)) {
                broken.push((site.unit, site.name_span));
            }
        }
        if !broken.is_empty() {
            return Err(TransformError::RemovalBreaksReferences {
                element,
                sites: broken,
            });
        }
        // Consume surrounding whitespace: the line's leading indentation
        // and the trailing newline, when nothing else shares the line.
        let cut = cut_whole_lines(self.user_src(unit, e)?, extent);
        let (start, end) = (cut.start, cut.end);
        self.consumed.push((unit, cut));
        self.splices.push(Splice {
            unit,
            start,
            end,
            text: String::new(),
            expects: Vec::new(),
        });
        Ok(())
    }

    fn plan_replace(&mut self, e: ElementRef, text: &str) -> Result<(), TransformError> {
        let text = text.trim();
        // Parse the replacement up front: it must be exactly one member,
        // and its declared name drives reference respelling.
        let probe = format!("package __p {{\n{text}\n}}");
        let parse = parse_source(&probe);
        if !parse.diagnostics.is_empty() {
            return Err(TransformError::InvalidMember {
                text: text.to_string(),
                message: parse.diagnostics[0].message.clone(),
            });
        }
        let inner: &[sysmlv2_syntax::ast::Member] = match parse.unit.members.as_slice() {
            [m] => match &m.kind {
                sysmlv2_syntax::ast::MemberKind::Package(p) => p.body.as_deref().unwrap_or(&[]),
                _ => unreachable!("probe wraps the text in a package"),
            },
            _ => unreachable!("probe has one root"),
        };
        if inner.len() != 1 {
            return Err(TransformError::InvalidMember {
                text: text.to_string(),
                message: format!(
                    "a replacement must contain exactly one member, found {}",
                    inner.len()
                ),
            });
        }
        let new_name: Option<String> = {
            use sysmlv2_syntax::ast::MemberKind as K;
            match &inner[0].kind {
                K::Package(p) => p.id.name.as_ref().map(|n| n.value.clone()),
                K::Definition(d) => d.id.name.as_ref().map(|n| n.value.clone()),
                K::Usage(u) => u.declaration.id.name.as_ref().map(|n| n.value.clone()),
                _ => None,
            }
        };

        let r = self.session.resolved();
        let (unit, extent) = r.member_extent(e).ok_or(TransformError::NoExtent(e))?;
        let old_qn = r.element_qualified_name(e);
        let old_raw = r
            .declaration_site(e)
            .and_then(|(u, sp)| Some(decode_name(slice(self.src(u)?, sp))));

        // The replacement arrives in top-level form; continuation lines
        // are re-spelled at the member's own depth (the splice starts
        // past the first line's indentation, which survives as-is).
        let src = self.user_src(unit, e)?;
        let base = line_indent(src, extent.start);
        let text = reindent_member_text(text, &base, indent_unit(&base, src));

        // The whole extent is consumed: references inside it vanish with
        // the old text, and untouched-site verification skips them.
        self.consumed
            .push((unit, Span::new(extent.start, extent.end)));
        self.splices.push(Splice {
            unit,
            start: extent.start,
            end: extent.end,
            text,
            expects: Vec::new(),
        });

        // Declared-name change: record the correspondence and respell
        // outside reference sites written with the old name — the
        // rename machinery, minus the declaration rewrite (the
        // replacement text already carries the new name). Sites inside
        // the replaced extent are consumed, never respelled.
        if let (Some(old_qn), Some(old_raw), Some(new_name)) =
            (old_qn, old_raw, new_name.as_deref())
        {
            if old_raw != new_name {
                let spelled = spell_name(new_name);
                let qn_seg = escape_name(new_name);
                let new_qn = match old_qn.rfind("::") {
                    Some(i) => format!("{}{}", &old_qn[..i + 2], qn_seg),
                    None => qn_seg,
                };
                self.correspondence.push((old_qn, new_qn.clone()));
                for site in self.session.resolved().references_to(e) {
                    let inside = site.unit == unit
                        && site.name_span.start >= extent.start
                        && site.name_span.end <= extent.end;
                    // A preceding operation may already replace/remove
                    // the member containing this reference (for example,
                    // a provenance record whose `about` target is being
                    // renamed in the same batch). Its explicit replacement
                    // owns that text; adding an automatic respelling splice
                    // would overlap it. Operation order remains meaningful:
                    // callers put the explicit replacement first.
                    let already_consumed = self.consumed.iter().any(|(consumed_unit, span)| {
                        *consumed_unit == site.unit
                            && site.name_span.start >= span.start
                            && site.name_span.end <= span.end
                    });
                    if inside || already_consumed {
                        continue;
                    }
                    let Some(site_src) = self.src(site.unit) else {
                        continue;
                    };
                    if decode_name(slice(site_src, site.name_span)) == old_raw {
                        self.splices.push(Splice {
                            unit: site.unit,
                            start: site.name_span.start,
                            end: site.name_span.end,
                            text: spelled.clone(),
                            expects: vec![SpliceExpect {
                                qn: new_qn.clone(),
                                new_leaf: true,
                                offset: 0,
                                len: spelled.len() as u32,
                            }],
                        });
                    }
                }
            }
        }
        Ok(())
    }

    fn plan_retarget(&mut self, site: &RefSite, to: ElementRef) -> Result<(), TransformError> {
        // The rewrite lands in the site's own unit, so that unit must be
        // one the session owns: a site handed in against a library unit
        // is refused rather than spliced into text that is read-only.
        self.user_src(site.unit, site.owner)?;
        // Spliced as reference text, so the re-resolvable spelling.
        let qn = self
            .session
            .resolved()
            .element_reference_spelling(to)
            .ok_or(TransformError::AnonymousTarget(to))?;
        let last_len = qn.rsplit("::").next().unwrap_or(&qn).len() as u32;
        self.consumed.push((site.unit, site.span));
        self.splices.push(Splice {
            unit: site.unit,
            start: site.span.start,
            end: site.span.end,
            text: qn.clone(),
            expects: vec![SpliceExpect {
                offset: qn.len() as u32 - last_len,
                len: last_len,
                qn,
                new_leaf: false,
            }],
        });
        Ok(())
    }

    fn plan_move(
        &mut self,
        e: ElementRef,
        new_owner: ElementRef,
        index: Option<usize>,
    ) -> Result<(), TransformError> {
        let unit_offset = self.session.unit_offset;
        let r = self.session.resolved();
        let (unit, extent) = r.member_extent(e).ok_or(TransformError::NoExtent(e))?;
        if unit < unit_offset {
            return Err(TransformError::NotDeclared(e));
        }
        // The destination must not sit inside the moved subtree.
        let mut cur = Some(new_owner);
        while let Some(c) = cur {
            if c == e {
                return Err(TransformError::MoveIntoOwnSubtree(e));
            }
            cur = r.owner(c);
        }
        let (dunit, dextent) = r
            .member_extent(new_owner)
            .ok_or(TransformError::NoExtent(new_owner))?;
        if dunit < unit_offset {
            return Err(TransformError::NotDeclared(new_owner));
        }
        // Ownership-path change: register it like a rename, so outside
        // references verify against the moved qualified name.
        let old_qn = r.element_qualified_name(e);
        let owner_qn = r.element_qualified_name(new_owner);
        if let (Some(old_qn), Some(owner_qn)) = (&old_qn, &owner_qn) {
            let last = old_qn.rsplit("::").next().unwrap_or(old_qn);
            let new_qn = format!("{owner_qn}::{last}");
            if *old_qn != new_qn {
                self.correspondence.push((old_qn.clone(), new_qn));
            }
        }
        // Destination's lexical members (self excluded), in source order
        // — `index` addresses this list.
        let mut sibs: Vec<Span> = r
            .owned_members(new_owner)
            .into_iter()
            .filter(|m| *m != e)
            .filter_map(|m| r.member_extent(m))
            .filter(|(u, sp)| *u == dunit && sp.start >= dextent.start && sp.end <= dextent.end)
            .map(|(_, sp)| sp)
            .collect();
        sibs.sort_by_key(|sp| sp.start);
        sibs.dedup();
        // References carried inside the moved text: recorded now (with
        // their pre-commit targets), verified at their new positions.
        let inner_sites: Vec<(u32, u32, Option<String>)> = {
            let all = r.reference_sites().to_vec();
            all.iter()
                .filter(|s| {
                    s.unit == unit
                        && s.name_span.start >= extent.start
                        && s.name_span.end <= extent.end
                })
                .map(|s| {
                    (
                        s.name_span.start - extent.start,
                        s.name_span.end - s.name_span.start,
                        r.element_qualified_name(s.target),
                    )
                })
                .collect()
        };

        // Excise, with remove's whitespace discipline (no stranding
        // check — the text comes back; verification decides what broke).
        let src = self.user_src(unit, e)?;
        let member_text = slice(src, extent).to_string();
        let cut = cut_whole_lines(src, extent);
        self.consumed.push((unit, cut));
        self.splices.push(Splice {
            unit,
            start: cut.start,
            end: cut.end,
            text: String::new(),
            expects: Vec::new(),
        });

        // Insert at the destination slot (plan_insert's composition for
        // the append shapes; before-a-sibling lands at its line start).
        let dsrc = self.user_src(dunit, new_owner)?;
        let indent = line_indent(dsrc, dextent.start);
        let child = child_indent(&indent, dsrc);
        let slot = index.unwrap_or(usize::MAX);
        let (ins_start, ins_end, ins_text) = if slot < sibs.len() {
            let sib = sibs[slot];
            let at = indent_start(dsrc.as_bytes(), sib.start);
            (at, at, format!("{child}{member_text}\n"))
        } else {
            let last = dextent.end - 1;
            match dsrc.as_bytes()[last as usize] {
                b'}' => {
                    let dbytes = dsrc.as_bytes();
                    let mut at = last;
                    while at > dextent.start && matches!(dbytes[at as usize - 1], b' ' | b'\t') {
                        at -= 1;
                    }
                    let after_newline = at > dextent.start && dbytes[at as usize - 1] == b'\n';
                    let text = if after_newline {
                        format!("{child}{member_text}\n{indent}")
                    } else {
                        format!("\n{child}{member_text}\n{indent}")
                    };
                    (at, last, text)
                }
                b';' => (
                    last,
                    last + 1,
                    format!(" {{\n{child}{member_text}\n{indent}}}"),
                ),
                _ => return Err(TransformError::NoExtent(new_owner)),
            }
        };
        if !inner_sites.is_empty() {
            let prefix = ins_text
                .find(&member_text)
                .expect("insert text is composed around the member text")
                as u32;
            self.moved_expects.push(MovedExpects {
                unit: dunit,
                at: ins_start,
                text: ins_text.clone(),
                sites: inner_sites
                    .into_iter()
                    .map(|(off, len, qn)| (off + prefix, len, qn))
                    .collect(),
            });
        }
        self.splices.push(Splice {
            unit: dunit,
            start: ins_start,
            end: ins_end,
            text: ins_text,
            expects: Vec::new(),
        });
        Ok(())
    }

    /// Extract: the eligibility gate answers *whether* and where
    /// the moved region is; this plans the three splices — retype the
    /// usage, collapse its body to `;`, insert the sibling definition
    /// carrying the body byte-preserved — plus the relocation
    /// bookkeeping (correspondence per moved member, expectation per
    /// generated target, carried-site re-verification, strict
    /// unresolved net, projection subject).
    fn plan_hoist(
        &mut self,
        e: ElementRef,
        unit_name: &str,
        new_name: Option<&str>,
    ) -> Result<(), TransformError> {
        let unit_offset = self.session.unit_offset;
        let dunit = self
            .unit_by_name(unit_name)
            .ok_or_else(|| TransformError::UnknownUnit(unit_name.to_string()))?;
        if let Some(new) = new_name {
            if new.is_empty() {
                return Err(TransformError::InvalidName(new.to_string()));
            }
        }
        let (unit, extent) = self
            .session
            .resolved()
            .member_extent(e)
            .ok_or(TransformError::NoExtent(e))?;
        if unit < unit_offset {
            return Err(TransformError::NotDeclared(e));
        }
        let source: String = self.user_src(unit, e)?.to_string();
        let r = self.session.resolved();
        let old_qn = r
            .element_qualified_name(e)
            .ok_or(TransformError::NotDeclared(e))?;
        let name = r
            .element_name(e)
            .ok_or(TransformError::NotDeclared(e))?
            .to_string();
        let top = new_name.map_or(name, str::to_string);
        self.correspondence.push((old_qn, escape_name(&top)));
        let decl = r.declaration_site(e).map(|(_, sp)| sp);
        // Every reference written inside the moved text. Those whose
        // target lies outside the moved subtree and that were written as
        // a name resolved from here (a plain lexical reference or an
        // import target) are respelled by the target's reference
        // spelling, so the text no longer depends on its old surroundings.
        // Every site is verified at its destination.
        struct Rewrite {
            start: u32,
            end: u32,
            text: String,
        }
        let mut rewrites: Vec<Rewrite> = Vec::new();
        let mut sites: Vec<(u32, u32, Option<String>, Option<usize>)> = Vec::new();
        let all: Vec<RefSite> = r
            .reference_sites()
            .iter()
            .filter(|s| s.unit == unit && s.span.start >= extent.start && s.span.end <= extent.end)
            .cloned()
            .collect();
        for site in &all {
            let mut inside = false;
            let mut cur = Some(site.target);
            while let Some(c) = cur {
                if c == e {
                    inside = true;
                    break;
                }
                cur = r.owner(c);
            }
            let qn = r.element_qualified_name(site.target);
            // A site that resolved only through imports the moved text
            // owns keeps resolving through them: leave it as written.
            let through_own_imports = !site.via_imports.is_empty()
                && site.via_imports.iter().all(|(imp, _)| {
                    r.import_extent(*imp).is_some_and(|(u, sp)| {
                        u == unit && sp.start >= extent.start && sp.end <= extent.end
                    })
                });
            let respell = !inside
                && !through_own_imports
                && site.chain_root.is_none()
                && (site.plain || site.kind.starts_with("imported"));
            let mut rewritten = None;
            // The package names itself as the first segment (`Lib::K`
            // inside `Lib`): under the new name the old one would denote
            // the colliding root element. Qualified through the owner
            // (`R::Lib::K`) it keeps resolving through the root's alias.
            let names_itself = site.target == e && site.span.start == site.name_span.start;
            if let (Some(new), true) = (new_name, names_itself) {
                rewritten = Some(rewrites.len());
                rewrites.push(Rewrite {
                    start: site.name_span.start,
                    end: site.name_span.end,
                    text: spell_name(new),
                });
            } else if respell {
                if let Some(mut spelling) = r.element_reference_spelling(site.target) {
                    let written = &source[site.span.start as usize..site.span.end as usize];
                    // A reference written from the global root stays
                    // global: the prefix escapes a nearer member of the
                    // same name, and the moved text keeps those scopes.
                    // The same prefix is added when the spelling's first
                    // segment would not denote the target's root ancestor
                    // from where the text sits: a member of the moved text
                    // (or of the vanishing owner) shadows it.
                    let shadowed = !written.starts_with("$::") && {
                        let first = sysmlv2_syntax::name::split_canonical(&spelling)
                            .into_iter()
                            .next()
                            .unwrap_or_default();
                        let probe = sysmlv2_syntax::ast::QualifiedName {
                            is_global: false,
                            segments: vec![sysmlv2_syntax::ast::Name {
                                value: first.clone(),
                                span: Span::default(),
                            }],
                            span: Span::default(),
                        };
                        // The root-level element the spelling starts from.
                        let top = r.resolve_qualified(&spell_name(&first));
                        top.is_none()
                            || r.resolve_in_excluding(site.scope, &probe, site.exclude) != top
                    };
                    if written.starts_with("$::") || shadowed {
                        spelling = format!("$::{spelling}");
                    }
                    if spelling != written {
                        rewritten = Some(rewrites.len());
                        rewrites.push(Rewrite {
                            start: site.span.start,
                            end: site.span.end,
                            text: spelling,
                        });
                    }
                }
            }
            sites.push((site.name_span.start, site.name_span.end, qn, rewritten));
        }
        if let (Some(new), Some(decl)) = (new_name, decl) {
            rewrites.push(Rewrite {
                start: decl.start,
                end: decl.end,
                text: spell_name(new),
            });
        }
        self.report_unused_imports = true;
        // Sites index `rewrites` by push order; the text is assembled in
        // source order through this permutation.
        let mut order: Vec<usize> = (0..rewrites.len()).collect();
        order.sort_by_key(|&i| (rewrites[i].start, rewrites[i].end));
        for pair in order.windows(2) {
            let (a, b) = (&rewrites[pair[0]], &rewrites[pair[1]]);
            if b.start < a.end {
                return Err(TransformError::OverlappingEdits {
                    unit,
                    at: Span::new(b.start, b.end),
                });
            }
        }
        // A site inside a respelled reference (its qualifier segments) is
        // re-derived from the new spelling; the respelled site's own
        // expectation covers it.
        let sites = sites.into_iter().filter(|(ns, ne, _, rw)| {
            rw.is_some() || !rewrites.iter().any(|w| *ns < w.end && w.start < *ne)
        });
        // The moved text: the member's extent with the rewrites applied
        // and the member's own indentation removed from every line.
        let src = self.user_src(unit, e)?;
        let indent = line_indent(src, extent.start);
        let raw = &src[extent.start as usize..extent.end as usize];
        // Position map from raw offsets (relative to the extent) to the
        // rewritten text, then through the dedent.
        let mut rewritten = String::with_capacity(raw.len());
        let mut cursor = 0u32;
        let mut deltas: Vec<(u32, i64)> = Vec::new(); // (raw offset after which delta applies, cumulative delta)
        let mut delta = 0i64;
        for w in order.iter().map(|&i| &rewrites[i]) {
            let (ws, we) = (w.start - extent.start, w.end - extent.start);
            rewritten.push_str(&raw[cursor as usize..ws as usize]);
            rewritten.push_str(&w.text);
            delta += w.text.len() as i64 - (we - ws) as i64;
            deltas.push((we, delta));
            cursor = we;
        }
        rewritten.push_str(&raw[cursor as usize..]);
        let map_rewrite = |pos: u32| -> u32 {
            let d = deltas
                .iter()
                .rev()
                .find(|(after, _)| *after <= pos)
                .map_or(0, |(_, d)| *d);
            (pos as i64 + d) as u32
        };
        let (dedented, lines) = dedent_lines(&rewritten, &indent);
        let map_dedent = |pos: u32| -> u32 {
            let (old_start, new_start) = lines
                .iter()
                .rev()
                .find(|(old_start, _)| *old_start <= pos)
                .copied()
                .unwrap_or((0, 0));
            new_start + (pos - old_start)
        };
        let expects = sites.map(|(ns, ne, qn, rw)| match rw {
            Some(i) => {
                let w = &rewrites[i];
                // The spelled last segment (a quoted one may hold `::`).
                let last_len = sysmlv2_syntax::name::split_canonical(&w.text)
                    .pop()
                    .map_or(w.text.len(), |seg| {
                        sysmlv2_syntax::name::spell_name_in(None, &seg).len()
                    }) as u32;
                let start = map_rewrite(w.start - extent.start) + w.text.len() as u32 - last_len;
                (map_dedent(start), last_len, qn)
            }
            None => {
                let start = map_rewrite(ns - extent.start);
                (map_dedent(start), ne - ns, qn)
            }
        });
        // Cut the member from its unit, whole lines when it stands alone.
        let cut = cut_whole_lines(src, extent);
        self.consumed.push((unit, cut));
        self.splices.push(Splice {
            unit,
            start: cut.start,
            end: cut.end,
            text: String::new(),
            expects: Vec::new(),
        });
        // Append at the destination's top level.
        let dsrc = self
            .src(dunit)
            .ok_or_else(|| TransformError::UnknownUnit(unit_name.to_string()))?;
        let at = dsrc.len() as u32;
        let ins_text = if dsrc.is_empty() || dsrc.ends_with('\n') {
            format!("{dedented}\n")
        } else {
            format!("\n{dedented}\n")
        };
        let prefix = ins_text
            .find(&dedented)
            .expect("insert text is composed around the member text") as u32;
        self.moved_expects.push(MovedExpects {
            unit: dunit,
            at,
            text: ins_text.clone(),
            sites: expects
                .map(|(off, len, qn)| (off + prefix, len, qn))
                .collect(),
        });
        self.splices.push(Splice {
            unit: dunit,
            start: at,
            end: at,
            text: ins_text,
            expects: Vec::new(),
        });
        Ok(())
    }

    fn plan_extract(
        &mut self,
        usage: ElementRef,
        name: Option<&str>,
    ) -> Result<(), TransformError> {
        let elig = self
            .session
            .extract_definition_eligibility(usage)
            .map_err(|reason| TransformError::ExtractIneligible { reason })?;
        let unit = elig.unit;

        // Every resolved-model read up front.
        let r = &mut self.session.resolved;
        let def_name = match name {
            Some(n) if !n.trim().is_empty() => n.trim().to_string(),
            Some(n) => return Err(TransformError::InvalidName(n.to_string())),
            None => upper_camel(
                r.element_name(usage)
                    .ok_or(TransformError::NotDeclared(usage))?,
            ),
        };
        let owner = r.owner(usage).ok_or(TransformError::NotDeclared(usage))?;
        for sib in r.owned_members(owner) {
            if r.element_lookup_name(sib).as_deref() == Some(def_name.as_str()) {
                return Err(TransformError::NameTaken {
                    existing: r
                        .element_qualified_name(sib)
                        .unwrap_or_else(|| format!("{sib:?}")),
                    name: def_name,
                });
            }
        }
        let owner_scope = r.element_scope(owner).unwrap_or_else(|| r.root_scope());
        if r.name_is_bound_in(owner_scope, &def_name) {
            return Err(TransformError::NameTaken {
                existing: format!("a visible `{def_name}` binding in the destination scope"),
                name: def_name,
            });
        }
        let usage_qn = r
            .element_qualified_name(usage)
            .ok_or(TransformError::NotDeclared(usage))?;
        let def_qn = match r.element_qualified_name(owner) {
            Some(o) => format!("{o}::{}", escape_name(&def_name)),
            None => escape_name(&def_name),
        };
        let (u2, extent) = r
            .member_extent(usage)
            .ok_or(TransformError::NoExtent(usage))?;
        debug_assert_eq!(unit, u2);
        // The usage's typing clause: the hull of its FeatureTyping target
        // spans, replaced wholesale by the new definition's name. A
        // non-typing specialization clause interleaving the hull would be
        // swallowed — refuse rather than guess.
        let typings = r.typing_spans(usage);
        let typing_range = match (
            typings.iter().map(|&(_, s)| s.start).min(),
            typings.iter().map(|&(_, s)| s.end).max(),
        ) {
            (Some(lo), Some(hi)) => {
                let hull = Span::new(lo, hi);
                for (su, sspan) in r.specialization_spans(usage) {
                    let is_typing = typings.iter().any(|&(tu, ts)| tu == su && ts == sspan);
                    if !is_typing && su == unit && sspan.start < hull.end && sspan.end > hull.start
                    {
                        return Err(TransformError::AmbiguousTyping(usage));
                    }
                }
                Some(hull)
            }
            _ => None,
        };
        let decl_end = r.declaration_site(usage).map(|(_, s)| s.end);
        // Correspondence: each named direct member's identity moves under
        // the definition; descendants ride the prefix mapping. The usage
        // itself keeps its name and must not be mapped.
        let member_moves: Vec<(String, String)> = r
            .owned_members(usage)
            .into_iter()
            .filter_map(|m| {
                let qn = r.element_qualified_name(m)?;
                let name = r.element_lookup_name(m)?;
                Some((qn, escape_name(&name)))
            })
            .collect();
        // Sites carried inside the moved interior, with their pre-commit
        // targets (offsets relative to the interior).
        let inner_sites: Vec<(u32, u32, Option<String>)> = {
            let sites = r.reference_sites().to_vec();
            sites
                .iter()
                .filter(|s| {
                    s.unit == unit
                        && s.name_span.start >= elig.body_interior.start
                        && s.name_span.end <= elig.body_interior.end
                })
                .map(|s| {
                    (
                        s.name_span.start - elig.body_interior.start,
                        s.name_span.end - s.name_span.start,
                        r.element_qualified_name(s.target),
                    )
                })
                .collect()
        };

        let spelled = spell_name(&def_name);
        let (cut, ins_at, interior_text, indent) = {
            let src = self.user_src(unit, usage)?;
            let bytes = src.as_bytes();
            // Body removal starts at the whitespace before the opening
            // brace (the brace is the byte before the interior).
            let brace = elig.body_interior.start - 1;
            debug_assert_eq!(bytes[brace as usize], b'{');
            let mut cut = brace;
            while cut > extent.start && matches!(bytes[cut as usize - 1], b' ' | b'\t') {
                cut -= 1;
            }
            // The definition inserts at the usage's line start.
            let ins_at = indent_start(bytes, extent.start);
            (
                (cut, slice(src, Span::new(cut, brace)).to_string()),
                ins_at,
                slice(src, elig.body_interior).to_string(),
                line_indent(src, extent.start),
            )
        };
        // The whitespace the usage wrote between its header and its
        // opening brace rides onto the definition, so an inline of the
        // fresh definition restores the original spelling byte-exactly
        // (`part engine{` stays braceless-tight through the round trip).
        let (cut, pre_brace_ws) = cut;

        // 1. The usage's body collapses to `;`.
        self.consumed.push((unit, Span::new(cut, extent.end)));
        self.splices.push(Splice {
            unit,
            start: cut,
            end: extent.end,
            text: ";".into(),
            expects: Vec::new(),
        });
        // 2. The usage is retyped by the new definition.
        match typing_range {
            Some(hull) => {
                self.consumed.push((unit, hull));
                self.splices.push(Splice {
                    unit,
                    start: hull.start,
                    end: hull.end,
                    text: spelled.clone(),
                    expects: vec![SpliceExpect {
                        qn: def_qn.clone(),
                        new_leaf: false,
                        offset: 0,
                        len: spelled.len() as u32,
                    }],
                });
            }
            None => {
                let at = decl_end.ok_or(TransformError::NotDeclared(usage))?;
                self.splices.push(Splice {
                    unit,
                    start: at,
                    end: at,
                    text: format!(" : {spelled}"),
                    expects: vec![SpliceExpect {
                        qn: def_qn.clone(),
                        new_leaf: false,
                        offset: 3,
                        len: spelled.len() as u32,
                    }],
                });
            }
        }
        // 3. The sibling definition, immediately before the usage's
        // line: synthesized header, byte-preserved body, one expectation
        // per generalized typing target.
        let mut def_text = format!("{indent}{} def {spelled}", elig.keyword);
        let mut def_expects = Vec::new();
        for (i, t) in elig.plain_typings.iter().enumerate() {
            def_text.push_str(if i == 0 { " :> " } else { ", " });
            let at = def_text.len() as u32;
            def_text.push_str(&t.spelling);
            let name_span = terminal_name_span(&t.spelling);
            def_expects.push(SpliceExpect {
                qn: t.target_qn.clone(),
                new_leaf: false,
                offset: at + name_span.start,
                len: name_span.len(),
            });
        }
        def_text.push_str(&pre_brace_ws);
        def_text.push('{');
        let interior_off = def_text.len() as u32;
        def_text.push_str(&interior_text);
        def_text.push_str("}\n");
        if !inner_sites.is_empty() {
            self.moved_expects.push(MovedExpects {
                unit,
                at: ins_at,
                text: def_text.clone(),
                sites: inner_sites
                    .into_iter()
                    .map(|(off, len, qn)| (off + interior_off, len, qn))
                    .collect(),
            });
        }
        self.splices.push(Splice {
            unit,
            start: ins_at,
            end: ins_at,
            text: def_text,
            expects: def_expects,
        });

        for (old_qn, last) in member_moves {
            self.correspondence
                .push((old_qn, format!("{def_qn}::{last}")));
        }
        self.refuse_new_unresolved = true;
        self.projection_subjects.push(usage_qn);
        Ok(())
    }

    /// Inline: the eligibility gate proved the sole plain typing,
    /// classified every incoming reference, resolved the definition's
    /// `:>` targets, and refused collisions; this plans the splices —
    /// retarget (or drop) the usage's typing entry, merge the
    /// definition's body members in front of the usage's own, delete
    /// the definition — plus the same relocation bookkeeping as
    /// extract, and flags the commit to report newly unused imports.
    fn plan_inline(&mut self, definition: ElementRef) -> Result<(), TransformError> {
        let elig = self
            .session
            .inline_definition_eligibility(definition)
            .map_err(|reason| TransformError::InlineIneligible { reason })?;
        let usage = elig.usage;
        let def_unit = elig.def_unit;

        // Every resolved-model read up front. (The definition's own
        // qualified name maps to nothing — it is deleted; only its
        // members correspond.)
        let r = &mut self.session.resolved;
        let usage_qn = r
            .element_qualified_name(usage)
            .ok_or(TransformError::NotDeclared(usage))?;
        let (u_unit, u_extent) = r
            .member_extent(usage)
            .ok_or(TransformError::NoExtent(usage))?;
        let typing_spans: Vec<Span> = r
            .typing_spans(usage)
            .into_iter()
            .filter(|&(tu, _)| tu == u_unit)
            .map(|(_, sp)| sp)
            .collect();
        // Correspondence: each named definition member's identity moves
        // under the usage; descendants ride the prefix mapping. The
        // definition's own name maps to nothing — it is deleted.
        let member_moves: Vec<(String, String)> = r
            .owned_members(definition)
            .into_iter()
            .filter_map(|m| {
                let qn = r.element_qualified_name(m)?;
                let name = r.element_lookup_name(m)?;
                Some((qn, escape_name(&name)))
            })
            .collect();
        // Sites carried inside the moved interior (offsets relative to
        // the interior), with their pre-commit targets.
        let inner_sites: Vec<(u32, u32, Option<String>)> = match elig.body_interior {
            Some(interior) => {
                let sites = r.reference_sites().to_vec();
                sites
                    .iter()
                    .filter(|s| {
                        s.unit == def_unit
                            && s.name_span.start >= interior.start
                            && s.name_span.end <= interior.end
                    })
                    .map(|s| {
                        (
                            s.name_span.start - interior.start,
                            s.name_span.end - s.name_span.start,
                            r.element_qualified_name(s.target),
                        )
                    })
                    .collect()
            }
            None => Vec::new(),
        };

        // ---- text geometry ----
        let def_src = self.user_src(def_unit, definition)?;
        let def_interior_text = elig.body_interior.map(|sp| slice(def_src, sp).to_string());
        // The whitespace the definition wrote between its header and
        // opening brace — reused when the usage grows a body, so
        // `inline(extract(usage))` restores the original spelling
        // byte-exactly whatever its brace style was.
        let def_pre_brace_ws: String = match elig.body_interior {
            Some(interior) => {
                let src = self.user_src(def_unit, definition)?;
                let bytes = src.as_bytes();
                let brace = interior.start - 1;
                let mut ws = brace;
                while ws > elig.def_extent.start && matches!(bytes[ws as usize - 1], b' ' | b'\t') {
                    ws -= 1;
                }
                slice(src, Span::new(ws, brace)).to_string()
            }
            None => String::new(),
        };
        // Definition removal, with remove's whitespace discipline.
        let def_cut = cut_whole_lines(self.user_src(def_unit, definition)?, elig.def_extent);
        let (def_cut_start, def_cut_end) = (def_cut.start, def_cut.end);
        let usage_text = slice(self.user_src(u_unit, usage)?, u_extent).to_string();
        let usage_interior_rel = eligibility::body_interior(&usage_text);

        // 1. The usage's typing entry: retargeted to the definition's
        // plain specializations, or dropped when it has none.
        let ts = elig.typing_site.span;
        if !elig.plain_specializations.is_empty() {
            let mut text = String::new();
            let mut expects = Vec::new();
            for (i, t) in elig.plain_specializations.iter().enumerate() {
                if i > 0 {
                    text.push_str(", ");
                }
                let at = text.len() as u32;
                text.push_str(&t.spelling);
                let name_span = terminal_name_span(&t.spelling);
                expects.push(SpliceExpect {
                    qn: t.target_qn.clone(),
                    new_leaf: false,
                    offset: at + name_span.start,
                    len: name_span.len(),
                });
            }
            self.consumed.push((u_unit, ts));
            self.splices.push(Splice {
                unit: u_unit,
                start: ts.start,
                end: ts.end,
                text,
                expects,
            });
        } else {
            let rel = Span::new(ts.start - u_extent.start, ts.end - u_extent.start);
            let entries_rel: Vec<Span> = typing_spans
                .iter()
                .map(|sp| Span::new(sp.start - u_extent.start, sp.end - u_extent.start))
                .collect();
            let removal = typing_entry_removal(&usage_text, rel, &entries_rel)
                .ok_or(TransformError::AmbiguousTyping(usage))?;
            let abs = Span::new(u_extent.start + removal.start, u_extent.start + removal.end);
            self.consumed.push((u_unit, abs));
            self.splices.push(Splice {
                unit: u_unit,
                start: abs.start,
                end: abs.end,
                text: String::new(),
                expects: Vec::new(),
            });
        }

        // 2. Body merge: the definition's members land in front of the
        // usage's pre-existing members, each region's order preserved.
        if let Some(def_int) = &def_interior_text {
            match usage_interior_rel {
                Some(u_int) => {
                    let at = u_extent.start + u_int.start;
                    let usage_int_text = &usage_text[u_int.start as usize..u_int.end as usize];
                    let mut ins = def_int.trim_end_matches([' ', '\t']).to_string();
                    if ins.ends_with('\n') && usage_int_text.starts_with('\n') {
                        ins.pop();
                    }
                    if !inner_sites.is_empty() {
                        self.moved_expects.push(MovedExpects {
                            unit: u_unit,
                            at,
                            text: ins.clone(),
                            sites: inner_sites,
                        });
                    }
                    self.splices.push(Splice {
                        unit: u_unit,
                        start: at,
                        end: at,
                        text: ins,
                        expects: Vec::new(),
                    });
                }
                None => {
                    // A `;` declaration grows the definition's body,
                    // keeping the definition's brace spacing.
                    let semi = u_extent.end - 1;
                    let text = format!("{def_pre_brace_ws}{{{def_int}}}");
                    let prefix = def_pre_brace_ws.len() as u32 + 1;
                    if !inner_sites.is_empty() {
                        self.moved_expects.push(MovedExpects {
                            unit: u_unit,
                            at: semi,
                            text: text.clone(),
                            sites: inner_sites
                                .iter()
                                .map(|(off, len, qn)| (off + prefix, *len, qn.clone()))
                                .collect(),
                        });
                    }
                    self.splices.push(Splice {
                        unit: u_unit,
                        start: semi,
                        end: u_extent.end,
                        text,
                        expects: Vec::new(),
                    });
                }
            }
        }

        // 3. The definition is deleted (the atomic pipeline means it
        // only actually disappears if every check passes).
        self.consumed
            .push((def_unit, Span::new(def_cut_start, def_cut_end)));
        self.splices.push(Splice {
            unit: def_unit,
            start: def_cut_start,
            end: def_cut_end,
            text: String::new(),
            expects: Vec::new(),
        });

        for (old_qn, last) in member_moves {
            self.correspondence
                .push((old_qn, format!("{usage_qn}::{last}")));
        }
        self.refuse_new_unresolved = true;
        self.projection_subjects.push(usage_qn);
        self.report_unused_imports = true;
        Ok(())
    }

    /// Apply, rebuild, verify, swap — or roll back by never touching the
    /// session's state. `dry_run` skips the final swap: the session is
    /// left untouched even on success (the whole pipeline runs on
    /// copies either way — this is what makes a check-only pass exact).
    fn commit(mut self, dry_run: bool) -> Result<CommitReport, TransformError> {
        // Deduplicate identical splices (two ops may legitimately produce
        // the same replacement), then reject overlaps.
        self.splices.sort_by_key(|s| (s.unit, s.start, s.end));
        self.splices.dedup_by(|a, b| {
            a.unit == b.unit && a.start == b.start && a.end == b.end && a.text == b.text
        });
        for w in self.splices.windows(2) {
            if w[0].unit == w[1].unit && w[1].start < w[0].end {
                return Err(TransformError::OverlappingEdits {
                    unit: w[1].unit,
                    at: Span::new(w[1].start, w[0].end),
                });
            }
        }

        // Pre-commit state the verification needs. Correspondence
        // entries are recorded op by op, each against pre-commit
        // ancestor spellings — a batch that renames an element AND
        // something inside it (or a deeper chain) leaves every entry's
        // ancestor segments stale relative to the committed model. The
        // mapper therefore walks segment-recursively: the nearest
        // ancestor with an entry maps first, and the mapped prefix has
        // its own ancestors mapped in turn. The depth guard only trips
        // on pathological mutually-referential move chains, where the
        // name comes back unmapped and verification refuses safely.
        fn map_through(map: &[(String, String)], qn: &str, depth: u32) -> String {
            if depth > 64 {
                return qn.to_string();
            }
            if let Some((_, new)) = map.iter().find(|(old, _)| old == qn) {
                return match new.rfind("::") {
                    Some(i) => format!(
                        "{}::{}",
                        map_through(map, &new[..i], depth + 1),
                        &new[i + 2..]
                    ),
                    None => new.clone(),
                };
            }
            match qn.rfind("::") {
                Some(i) => format!(
                    "{}::{}",
                    map_through(map, &qn[..i], depth + 1),
                    &qn[i + 2..]
                ),
                None => qn.to_string(),
            }
        }
        let rename_map = self.correspondence.clone();
        let map_qn = |qn: &str| -> String { map_through(&rename_map, qn, 0) };
        let pre_unresolved = self.session.resolved.unresolved_count();
        let pre_unresolved_refs = if self.refuse_new_unresolved {
            self.session.resolved.unresolved_references()
        } else {
            Vec::new()
        };
        let old_sites: Vec<RefSite> = self.session.resolved.reference_sites().to_vec();
        let mut old_qn_ids: Vec<(String, Uuid)> = Vec::new();
        let mut old_site_qns: HashMap<(usize, u32, u32), Option<String>> = HashMap::new();
        {
            let r = &mut self.session.resolved;
            let user: Vec<ElementRef> = r.user_elements().collect();
            for e in user {
                if let Some(qn) = r.element_qualified_name(e) {
                    old_qn_ids.push((qn, r.element_id(e)));
                }
            }
            for s in &old_sites {
                let qn = r.element_qualified_name(s.target);
                old_site_qns.insert((s.unit, s.name_span.start, s.name_span.end), qn);
            }
        }

        // Apply the splices to copies of the sources, tracking the new
        // position of every splice.
        let mut new_sources = self.session.sources.clone();
        // Born units join empty, after the existing ones — indices of
        // existing units (and every splice) are untouched, and a splice
        // may already write into a born unit.
        for name in &self.new_units {
            new_sources.push((name.clone(), String::new()));
        }
        let mut new_positions: Vec<u32> = Vec::with_capacity(self.splices.len());
        {
            let mut per_unit: HashMap<usize, Vec<usize>> = HashMap::new();
            for (i, s) in self.splices.iter().enumerate() {
                per_unit.entry(s.unit).or_default().push(i);
            }
            new_positions.resize(self.splices.len(), 0);
            for (unit, idxs) in per_unit {
                let local = unit - self.session.unit_offset;
                let src: &str = self
                    .session
                    .sources
                    .get(local)
                    .map_or("", |(_, s)| s.as_str());
                let mut out = String::with_capacity(src.len());
                let mut cursor = 0usize;
                for &i in &idxs {
                    let s = &self.splices[i];
                    out.push_str(&src[cursor..s.start as usize]);
                    new_positions[i] = out.len() as u32;
                    out.push_str(&s.text);
                    cursor = s.end as usize;
                }
                out.push_str(&src[cursor..]);
                new_sources[local].1 = out;
            }
        }
        // Reparse + rebuild (rollback = return before swapping state).
        let (new_model, mut new_resolved, unit_offset) =
            rebuild(&new_sources, self.session.lib.as_ref()).map_err(|e| match e {
                SessionError::Parse { unit, diagnostics } => {
                    TransformError::ReparseFailed { unit, diagnostics }
                }
                // rebuild() reparses text — only Io is reachable here.
                e => TransformError::ReparseFailed {
                    unit: "<library>".into(),
                    diagnostics: vec![Diagnostic::error(Span::default(), e.to_string())],
                },
            })?;
        debug_assert_eq!(unit_offset, self.session.unit_offset);

        // Offset mapping per unit: position -> post-commit position, or
        // None inside an edited range. A pure insertion (start == end)
        // sits *between* tokens: a span ending exactly there keeps its
        // end (`at_end`), while a span starting there is pushed right —
        // otherwise a name token abutting the insertion point would
        // stretch over the inserted text.
        let shift = |unit: usize, pos: u32, at_end: bool| -> Option<u32> {
            let mut delta: i64 = 0;
            for s in self.splices.iter().filter(|s| s.unit == unit) {
                let insertion = s.start == s.end;
                if pos > s.end || (pos == s.end && !(insertion && at_end)) {
                    delta += s.text.len() as i64 - (s.end - s.start) as i64;
                } else if pos > s.start {
                    return None; // inside an edited range
                }
            }
            Some((pos as i64 + delta) as u32)
        };
        let in_consumed = |unit: usize, sp: Span| {
            self.consumed
                .iter()
                .any(|&(u, c)| u == unit && sp.start >= c.start && sp.end <= c.end)
        };

        // Post-commit site index by (unit, name_span).
        let post_sites: Vec<RefSite> = new_resolved.reference_sites().to_vec();
        let mut post_by_span: HashMap<(usize, u32, u32), ElementRef> = HashMap::new();
        for s in &post_sites {
            post_by_span.insert((s.unit, s.name_span.start, s.name_span.end), s.target);
        }
        let mut post_qn = |e: ElementRef| new_resolved.element_qualified_name(e);

        // Broken-site descriptions in pre-commit coordinates: a refusal
        // rolls the commit back, so unit names, line:col, and byte spans
        // must match the text the caller still holds.
        let pre_sources = &self.session.sources;
        let pre_offset = self.session.unit_offset;
        let place = |unit: usize, pos: u32| -> String {
            match unit
                .checked_sub(pre_offset)
                .filter(|l| *l < pre_sources.len())
            {
                Some(local) => {
                    let (name, text) = &pre_sources[local];
                    let (line, col) = line_col(text, pos as usize);
                    format!("{name}:{line}:{col}")
                }
                None => match unit
                    .checked_sub(pre_offset + pre_sources.len())
                    .and_then(|k| self.new_units.get(k))
                {
                    Some(name) => format!("{name} (new)"),
                    None => format!("library unit {unit}"),
                },
            }
        };
        let spelled_at = |unit: usize, span: Span| -> &str {
            unit.checked_sub(pre_offset)
                .and_then(|l| pre_sources.get(l))
                .and_then(|(_, text)| text.get(span.start as usize..span.end as usize))
                .unwrap_or("?")
        };

        let mut broken: Vec<String> = Vec::new();
        // 1. Untouched old sites keep their (mapped) targets.
        for s in &old_sites {
            if in_consumed(s.unit, s.name_span) {
                continue;
            }
            // A splice covering exactly this span is a rename/retarget
            // rewrite — verified through its expectation below.
            if self.splices.iter().any(|sp| {
                sp.unit == s.unit && sp.start == s.name_span.start && sp.end == s.name_span.end
            }) {
                continue;
            }
            let (Some(ns), Some(ne)) = (
                shift(s.unit, s.name_span.start, false),
                shift(s.unit, s.name_span.end, true),
            ) else {
                continue; // inside an edited range — no expectation
            };
            let expected = old_site_qns
                .get(&(s.unit, s.name_span.start, s.name_span.end))
                .cloned()
                .flatten()
                .map(|qn| map_qn(&qn));
            match post_by_span.get(&(s.unit, ns, ne)) {
                None => {
                    let mut msg = format!(
                        "`{}` at {} (bytes {}..{}) would no longer resolve",
                        spelled_at(s.unit, s.name_span),
                        place(s.unit, s.name_span.start),
                        s.name_span.start,
                        s.name_span.end
                    );
                    if let Some(q) = expected.as_deref() {
                        msg.push_str(" (expected target: `");
                        msg.push_str(q);
                        msg.push_str("`)");
                    }
                    broken.push(msg);
                }
                Some(&t) => {
                    if let Some(expected) = expected {
                        let got = post_qn(t);
                        if got.as_deref() != Some(expected.as_str()) {
                            broken.push(format!(
                                "`{}` at {} (bytes {}..{}) would resolve to `{}` instead of `{}`",
                                spelled_at(s.unit, s.name_span),
                                place(s.unit, s.name_span.start),
                                s.name_span.start,
                                s.name_span.end,
                                got.as_deref().unwrap_or("<anonymous>"),
                                expected
                            ));
                        }
                    }
                }
            }
        }
        // 2. Written references (rename/retarget rewrites, synthesized
        // header targets) resolve to their declared new targets — every
        // expectation the splice carries, not just one.
        for (i, sp) in self.splices.iter().enumerate() {
            for expect in &sp.expects {
                let start = new_positions[i] + expect.offset;
                let end = start + expect.len;
                let new_name = sp
                    .text
                    .get(expect.offset as usize..(expect.offset + expect.len) as usize)
                    .unwrap_or(&sp.text);
                // Expectations are recorded in pre-commit spellings —
                // a sibling op renaming an ancestor in the same batch
                // shifts the committed qualified name without breaking
                // anything, so compare through the correspondence map.
                // A rename rewrite's final segment is already the
                // post-commit name: map only its ancestor path (the
                // full string must not match another entry's old name —
                // a batch may chain A→B, B→C).
                let expected = if expect.new_leaf {
                    match expect.qn.rfind("::") {
                        Some(i) => {
                            format!("{}::{}", map_qn(&expect.qn[..i]), &expect.qn[i + 2..])
                        }
                        None => expect.qn.clone(),
                    }
                } else {
                    map_qn(&expect.qn)
                };
                match post_by_span.get(&(sp.unit, start, end)) {
                    None => broken.push(format!(
                        "rewritten reference `{}` at {} would not resolve (expected target: `{}`)",
                        new_name,
                        place(sp.unit, sp.start),
                        expected
                    )),
                    Some(&t) => {
                        let got = post_qn(t);
                        if got.as_deref() != Some(expected.as_str()) {
                            broken.push(format!(
                                "rewritten reference `{}` at {} would resolve to `{}` instead of `{}`",
                                new_name,
                                place(sp.unit, sp.start),
                                got.as_deref().unwrap_or("<anonymous>"),
                                expected
                            ));
                        }
                    }
                }
            }
        }
        // 3. Sites carried inside moved text resolve at their new home,
        // to the (rename-mapped) targets they had before the move.
        for me in &self.moved_expects {
            let unit = me.unit;
            let Some(j) = self
                .splices
                .iter()
                .position(|s| s.unit == unit && s.start == me.at && s.text == me.text)
            else {
                continue;
            };
            let base = new_positions[j];
            for (offset, len, qn) in &me.sites {
                let (s, e2) = (base + offset, base + offset + len);
                let name = me
                    .text
                    .get(*offset as usize..(*offset + *len) as usize)
                    .unwrap_or("?");
                match post_by_span.get(&(unit, s, e2)) {
                    None => {
                        let mut msg = format!(
                            "moved reference `{name}` would no longer resolve at its destination in {}",
                            place(unit, me.at)
                        );
                        if let Some(qn) = qn {
                            msg.push_str(" (expected target: `");
                            msg.push_str(&map_qn(qn));
                            msg.push_str("`)");
                        }
                        broken.push(msg);
                    }
                    Some(&t) => {
                        if let Some(qn) = qn {
                            let expected = map_qn(qn);
                            let got = post_qn(t);
                            if got.as_deref() != Some(expected.as_str()) {
                                broken.push(format!(
                                    "moved reference `{name}` at its destination in {} would resolve to `{}` instead of `{expected}`",
                                    place(unit, me.at),
                                    got.as_deref().unwrap_or("<anonymous>")
                                ));
                            }
                        }
                    }
                }
            }
        }
        if !broken.is_empty() {
            broken.truncate(20);
            return Err(TransformError::SemanticIdentity { broken });
        }
        // Relocation discipline: any reference that resolved before the
        // commit but not after refuses it. Splice expectations catch the
        // targets the op wrote deliberately; this net catches everything
        // else a relocation can silently strand.
        if self.refuse_new_unresolved {
            let mut pre_counts: HashMap<UnresolvedSiteKey, usize> = HashMap::new();
            for reference in &pre_unresolved_refs {
                let key = unresolved_site_key(&mut self.session.resolved, reference, &map_qn);
                *pre_counts.entry(key).or_default() += 1;
            }
            let unit_name = |unit: usize| -> String {
                unit.checked_sub(pre_offset)
                    .and_then(|l| pre_sources.get(l))
                    .map(|(n, _)| n.clone())
                    .unwrap_or_else(|| format!("unit {unit}"))
            };
            let mut fresh: Vec<String> = Vec::new();
            for reference in new_resolved.unresolved_references() {
                let key = unresolved_site_key(&mut new_resolved, &reference, &|qn| qn.to_string());
                match pre_counts.get_mut(&key) {
                    Some(n) if *n > 0 => *n -= 1,
                    _ => fresh.push(format!(
                        "`{}` in {} at bytes {}..{}",
                        reference.spelling,
                        unit_name(reference.unit),
                        reference.span.start,
                        reference.span.end
                    )),
                }
            }
            if !fresh.is_empty() {
                fresh.truncate(20);
                return Err(TransformError::NewUnresolvedReferences { refs: fresh });
            }
        }
        // Relocation discipline, second net: the syntax checker's verdict
        // over every edited unit stays constant — synthesized text must
        // not introduce body-context violations `rebuild` (parse-only)
        // cannot see. Pre-existing findings are tolerated by multiset.
        if self.refuse_new_unresolved {
            let touched: HashSet<usize> = self.splices.iter().map(|s| s.unit).collect();
            let mut fresh: Vec<String> = Vec::new();
            for unit in touched {
                let local = unit - self.session.unit_offset;
                // A born unit had no text before the batch.
                let Some((unit_name, pre_text)) = self.session.sources.get(local) else {
                    continue;
                };
                let pre_diagnostics = syntax_validation(unit_name, pre_text);
                let mut pre_counts: HashMap<ValidationFindingKey, usize> = HashMap::new();
                for diagnostic in &pre_diagnostics {
                    let key = validation_finding_key(
                        &mut self.session.resolved,
                        unit,
                        diagnostic,
                        &map_qn,
                    );
                    *pre_counts.entry(key).or_default() += 1;
                }
                let post_text = &new_sources[local].1;
                let post_diagnostics = syntax_validation(unit_name, post_text);
                for diagnostic in post_diagnostics {
                    let key = validation_finding_key(&mut new_resolved, unit, &diagnostic, &|qn| {
                        qn.to_string()
                    });
                    match pre_counts.get_mut(&key) {
                        Some(n) if *n > 0 => *n -= 1,
                        _ => {
                            let (line, col) = line_col(post_text, diagnostic.span.start as usize);
                            fresh.push(format!(
                                "{} in {unit_name}:{line}:{col}",
                                diagnostic.message
                            ));
                        }
                    }
                }
            }
            if !fresh.is_empty() {
                fresh.truncate(20);
                return Err(TransformError::NewValidationFindings { findings: fresh });
            }
        }
        // Relocated subjects keep their effective-member projection
        // (the authoritative structural gate): pre-commit rows under
        // the correspondence map must equal prospective rows exactly.
        for qn in self.projection_subjects.clone() {
            let Some(pre_e) = self.session.resolved.resolve_qualified(&qn) else {
                continue;
            };
            let pre_rows = projection::Projector {
                resolved: &mut self.session.resolved,
                sources: &self.session.sources,
                unit_offset: self.session.unit_offset,
            }
            .project(pre_e, &map_qn);
            let post_rows = match new_resolved.resolve_qualified(&qn) {
                Some(post_e) => projection::Projector {
                    resolved: &mut new_resolved,
                    sources: &new_sources,
                    unit_offset,
                }
                .project(post_e, &|q: &str| q.to_string()),
                None => Vec::new(),
            };
            // Multiset comparison: global row order is not stable across
            // the owned↔inherited edge (see projection.rs) — each row's
            // content is the structural identity.
            let mut pre_rows = pre_rows;
            let mut post_rows = post_rows;
            pre_rows.sort();
            post_rows.sort();
            if pre_rows != post_rows {
                let mut broken: Vec<String> = pre_rows
                    .iter()
                    .filter(|r| !post_rows.contains(r))
                    .map(|r| format!("- {r}"))
                    .chain(
                        post_rows
                            .iter()
                            .filter(|r| !pre_rows.contains(r))
                            .map(|r| format!("+ {r}")),
                    )
                    .collect();
                if broken.is_empty() {
                    broken.push("the multiplicity of identical member rows changed".to_string());
                }
                broken.truncate(12);
                return Err(TransformError::StructuralIdentity {
                    element: qn,
                    broken,
                });
            }
        }

        // id_map: qualified-name correspondence through the rename map.
        let mut new_ids: HashMap<String, Uuid> = HashMap::new();
        {
            let user: Vec<ElementRef> = new_resolved.user_elements().collect();
            for e in user {
                if let Some(qn) = new_resolved.element_qualified_name(e) {
                    new_ids.insert(qn, new_resolved.element_id(e));
                }
            }
        }
        let mut report = CommitReport {
            findings: std::mem::take(&mut self.findings),
            ..CommitReport::default()
        };
        for (qn, old_id) in old_qn_ids {
            if let Some(&new_id) = new_ids.get(&map_qn(&qn)) {
                if new_id != old_id {
                    report.id_map.push((old_id, new_id));
                }
            }
        }
        let post_unresolved = new_resolved.unresolved_count();
        if post_unresolved != pre_unresolved {
            report.findings.push(format!(
                "unresolved references: {pre_unresolved} -> {post_unresolved}"
            ));
        }
        // Inline reports imports its deletion left unused. Match the
        // same untouched import site in prospective coordinates; text
        // alone aliases identical imports in distinct scopes.
        if self.report_unused_imports {
            let texts = |sources: &[(String, String)]| -> Vec<(usize, String)> {
                sources
                    .iter()
                    .enumerate()
                    .map(|(i, (_, t))| (self.session.unit_offset + i, t.clone()))
                    .collect()
            };
            let spelled = |texts: &[(usize, String)], unit: usize, span: Span| -> String {
                texts
                    .iter()
                    .find(|(i, _)| *i == unit)
                    .and_then(|(_, t)| t.get(span.start as usize..span.end as usize))
                    .unwrap_or("?")
                    .trim()
                    .to_string()
            };
            let pre_texts = texts(&self.session.sources);
            let post_texts = texts(&new_sources);
            let pre: HashSet<ImportSiteKey> =
                unused_private_imports_with(&mut self.session.resolved, &pre_texts)
                    .into_iter()
                    .filter_map(|(u, sp)| {
                        Some(import_site_key(
                            u,
                            Span::new(shift(u, sp.start, false)?, shift(u, sp.end, true)?),
                            spelled(&pre_texts, u, sp),
                        ))
                    })
                    .collect();
            for (u, sp) in unused_private_imports_with(&mut new_resolved, &post_texts) {
                let text = spelled(&post_texts, u, sp);
                if !pre.contains(&import_site_key(u, sp, text.clone())) {
                    report.findings.push(format!(
                        "import now unused: `{text}` in {}",
                        new_sources
                            .get(u - self.session.unit_offset)
                            .map(|(n, _)| n.as_str())
                            .unwrap_or("?")
                    ));
                }
            }
        }

        report.splices = self
            .splices
            .iter()
            .map(|s| AppliedSplice {
                unit: self.unit_name(s.unit),
                start: s.start,
                end: s.end,
                text: s.text.clone(),
            })
            .collect();
        // Announce born units as empty splices so mirroring callers
        // learn the unit exists (a mirror applying `""` at 0..0 of a
        // buffer it creates on demand is a no-op with the right
        // side effect).
        for name in &self.new_units {
            report.splices.push(AppliedSplice {
                unit: name.clone(),
                start: 0,
                end: 0,
                text: String::new(),
            });
        }

        // Success — swap the session to the new state.
        if !dry_run {
            self.session.sources = new_sources;
            apply_explicit_ids(
                &mut new_resolved,
                &mut self.session.explicit_ids,
                self.session.binds_ids,
                &mut self.session.warnings,
            );
            self.session.model = new_model;
            let policy = self.session.resolved.closure_policy();
            self.session.resolved = new_resolved;
            self.session.resolved.set_closure_policy(policy);
        }
        Ok(report)
    }
}

/// Unwrap Flexo MMS `{payload, identity}` change records when the whole
/// list is wrapped, normalizing the server's empty-string property
/// values back to null; anything else passes through.
fn unwrap_flexo(value: &serde_json::Value) -> serde_json::Value {
    fn empties_to_null(v: &mut serde_json::Value) {
        match v {
            serde_json::Value::Object(map) => {
                for (_, val) in map.iter_mut() {
                    if val.as_str() == Some("") {
                        *val = serde_json::Value::Null;
                    } else {
                        empties_to_null(val);
                    }
                }
            }
            serde_json::Value::Array(items) => items.iter_mut().for_each(empties_to_null),
            _ => {}
        }
    }
    let serde_json::Value::Array(items) = value else {
        return value.clone();
    };
    let wrapped = !items.is_empty()
        && items
            .iter()
            .all(|r| r.get("payload").is_some() && r.get("identity").is_some());
    let mut elements: Vec<serde_json::Value> = if wrapped {
        items
            .iter()
            .map(|r| r.get("payload").cloned().unwrap_or(serde_json::Value::Null))
            .collect()
    } else {
        items.clone()
    };
    elements.iter_mut().for_each(empties_to_null);
    serde_json::Value::Array(elements)
}

/// The recorded name of a single-document payload's root namespace
/// (`qualifiedName`/`declaredName` — the Flexo convention), matching
/// `split_documents`' naming for multi-document lists.
fn single_root_name(value: &serde_json::Value) -> Option<String> {
    let elements = value.as_array()?;
    elements
        .iter()
        .find(|e| {
            e.get("@type").and_then(|v| v.as_str()) == Some("Namespace")
                && e.get("owningRelationship")
                    .is_none_or(|v| v.is_null() || v.as_str() == Some(""))
        })
        .and_then(|root| {
            root.get("qualifiedName")
                .or_else(|| root.get("declaredName"))
                .and_then(|v| v.as_str())
                .map(str::to_owned)
        })
}

/// Unit name for one lifted document: the root namespace's recorded name
/// when it is a plain model file name (the Flexo convention), else a
/// numbered fallback.
fn doc_unit_name(root_name: Option<&str>, index: usize) -> String {
    if let Some(name) = root_name {
        let base = Path::new(name)
            .file_name()
            .map(|n| n.to_string_lossy().into_owned())
            .unwrap_or_default();
        let safe = !base.is_empty()
            && base
                .chars()
                .all(|c| c != ':' && c != '*' && c != '?' && c != '"');
        let model_file = Path::new(&base)
            .extension()
            .is_some_and(|e| e.eq_ignore_ascii_case("sysml") || e.eq_ignore_ascii_case("kerml"));
        if safe && model_file {
            return base;
        }
    }
    format!("document-{}.sysml", index + 1)
}

fn slice(src: &str, span: Span) -> &str {
    &src[span.start as usize..span.end as usize]
}

/// Leading whitespace of the line containing `pos`.
fn line_indent(src: &str, pos: u32) -> String {
    let bytes = src.as_bytes();
    let mut line_start = pos as usize;
    while line_start > 0 && bytes[line_start - 1] != b'\n' {
        line_start -= 1;
    }
    src[line_start..]
        .chars()
        .take_while(|c| *c == ' ' || *c == '\t')
        .collect()
}

// `indent_unit` / `reindent_member_text` live in sysmlv2-syntax::print —
// lint reproduces the planner's spelling and the two must not drift.

/// One additional indentation level under a line indented `indent`.
fn child_indent(indent: &str, src: &str) -> String {
    format!("{indent}{}", indent_unit(indent, src))
}

// ---------------------------------------------------------------------------
// Planner-internal gates: multi-expectation splices, relocation
// discipline (new unresolved references are fatal), rollback.
// ---------------------------------------------------------------------------

#[cfg(test)]
mod relocation_tests {
    use super::*;

    const SRC: &str = "package P {\n    part def A;\n    part def B;\n}\n";

    #[test]
    fn import_finding_identity_includes_the_source_site() {
        let spelling = "private import L::*;".to_string();
        let first = import_site_key(3, Span::new(10, 31), spelling.clone());
        let second = import_site_key(3, Span::new(50, 71), spelling);
        assert_ne!(first, second, "same-spelling imports must not alias");
    }

    fn session() -> Session {
        Session::from_sources(vec![("m.sysml".into(), SRC.into())]).expect("parses")
    }

    /// Append `text` at the end of the unit as one splice carrying
    /// `expects`, mirroring how a synthesized header will ship several
    /// generated targets in one replacement.
    fn append_splice(planner: &mut Planner<'_>, text: &str, expects: Vec<SpliceExpect>) {
        let at = SRC.len() as u32;
        planner.splices.push(Splice {
            unit: planner.session.unit_offset,
            start: at,
            end: at,
            text: text.to_string(),
            expects,
        });
    }

    #[test]
    fn every_expectation_on_one_splice_is_verified() {
        // "part x : P::A, P::B;\n" — two generated typing targets, one
        // splice. Offsets address each final segment.
        let mut s = session();
        let mut p = Planner::new(&mut s);
        append_splice(
            &mut p,
            "part x : P::A, P::B;\n",
            vec![
                SpliceExpect {
                    qn: "P::A".into(),
                    new_leaf: false,
                    offset: 12,
                    len: 1,
                },
                SpliceExpect {
                    qn: "P::B".into(),
                    new_leaf: false,
                    offset: 18,
                    len: 1,
                },
            ],
        );
        p.commit(false).expect("both targets verify");
        assert!(
            s.source(s.unit_offset)
                .unwrap()
                .contains("part x : P::A, P::B;")
        );
    }

    #[test]
    fn a_wrong_expectation_among_several_refuses_and_rolls_back() {
        let mut s = session();
        let mut p = Planner::new(&mut s);
        append_splice(
            &mut p,
            "part x : P::A, P::B;\n",
            vec![
                SpliceExpect {
                    qn: "P::A".into(),
                    new_leaf: false,
                    offset: 12,
                    len: 1,
                },
                // Declared expectation disagrees with what `P::B` denotes.
                SpliceExpect {
                    qn: "P::A".into(),
                    new_leaf: false,
                    offset: 18,
                    len: 1,
                },
            ],
        );
        let err = p.commit(false).expect_err("second expectation fails");
        match &err {
            TransformError::SemanticIdentity { broken } => {
                assert_eq!(broken.len(), 1, "{broken:?}");
                assert!(broken[0].contains("`B`"), "{broken:?}");
                assert!(broken[0].contains("instead of `P::A`"), "{broken:?}");
            }
            other => panic!("wrong refusal: {other}"),
        }
        assert_eq!(s.source(s.unit_offset).unwrap(), SRC, "rolled back");
    }

    #[test]
    fn an_unresolvable_expectation_refuses() {
        let mut s = session();
        let mut p = Planner::new(&mut s);
        append_splice(
            &mut p,
            "part x : P::Zed;\n",
            vec![SpliceExpect {
                qn: "P::Zed".into(),
                new_leaf: false,
                offset: 12,
                len: 3,
            }],
        );
        let err = p.commit(false).expect_err("target does not exist");
        match &err {
            TransformError::SemanticIdentity { broken } => {
                assert!(broken[0].contains("would not resolve"), "{broken:?}");
            }
            other => panic!("wrong refusal: {other}"),
        }
        assert_eq!(s.source(s.unit_offset).unwrap(), SRC, "rolled back");
    }

    #[test]
    fn relocation_mode_makes_new_unresolved_references_fatal() {
        // Without the flag: inserted text referencing nothing known is a
        // finding (the general pipeline's contract). With it: refusal +
        // rollback.
        let mut s = session();
        let mut p = Planner::new(&mut s);
        append_splice(&mut p, "part q : Nowhere;\n", Vec::new());
        let report = p.commit(false).expect("finding, not refusal");
        assert!(
            report
                .findings
                .iter()
                .any(|f| f.contains("unresolved references: 0 -> 1")),
            "{:?}",
            report.findings
        );

        let mut s = session();
        let mut p = Planner::new(&mut s);
        p.refuse_new_unresolved = true;
        append_splice(&mut p, "part q : Nowhere;\n", Vec::new());
        let err = p.commit(false).expect_err("relocation discipline");
        match &err {
            TransformError::NewUnresolvedReferences { refs } => {
                assert_eq!(refs.len(), 1, "{refs:?}");
                assert!(refs[0].contains("`Nowhere`"), "{refs:?}");
                assert!(refs[0].contains("m.sysml"), "{refs:?}");
            }
            other => panic!("wrong refusal: {other}"),
        }
        assert_eq!(s.source(s.unit_offset).unwrap(), SRC, "rolled back");
    }

    #[test]
    fn relocation_mode_tolerates_preexisting_unresolved_references() {
        // A model already carrying an unresolved spelling must not trip
        // the net when an edit leaves it exactly as unresolved as it was.
        let src = "package P {\n    part def A;\n    part u : Missing;\n}\n";
        let mut s = Session::from_sources(vec![("m.sysml".into(), src.into())]).expect("parses");
        let mut p = Planner::new(&mut s);
        p.refuse_new_unresolved = true;
        let at = src.len() as u32;
        let unit = p.session.unit_offset;
        p.splices.push(Splice {
            unit,
            start: at,
            end: at,
            text: "part x : P::A;\n".into(),
            expects: vec![SpliceExpect {
                qn: "P::A".into(),
                new_leaf: false,
                offset: 12,
                len: 1,
            }],
        });
        p.commit(false).expect("pre-existing unresolved is not new");
    }

    #[test]
    fn relocation_mode_does_not_cancel_distinct_same_spelling_sites() {
        // Removing one unresolved `Missing` and introducing `Missing` on
        // another declaration is still a newly unresolved site. A bag of
        // (unit, spelling) would incorrectly cancel these two references.
        let src = "package P {\n    part old : Missing;\n}\n";
        let mut s = Session::from_sources(vec![("m.sysml".into(), src.into())]).expect("parses");
        let mut p = Planner::new(&mut s);
        p.refuse_new_unresolved = true;
        let old = "part old : Missing;";
        let start = src.find(old).expect("old declaration") as u32;
        p.splices.push(Splice {
            unit: p.session.unit_offset,
            start,
            end: start + old.len() as u32,
            text: "part fresh : Missing;".into(),
            expects: Vec::new(),
        });
        let err = p
            .commit(false)
            .expect_err("new site must not cancel old site");
        match err {
            TransformError::NewUnresolvedReferences { refs } => {
                assert_eq!(refs.len(), 1, "{refs:?}");
                assert!(refs[0].contains("`Missing`"), "{refs:?}");
            }
            other => panic!("wrong refusal: {other}"),
        }
        assert_eq!(s.source(s.unit_offset).unwrap(), src, "rolled back");
    }

    #[test]
    fn projection_subjects_hold_structural_identity() {
        // A registered subject whose member value changes must refuse
        // even though no reference breaks and nothing goes unresolved —
        // the projection is the net that sees it.
        let src =
            "package P {\n    part def D {\n        attribute x = 1;\n    }\n    part d : D;\n}\n";
        let mut s = Session::from_sources(vec![("m.sysml".into(), src.into())]).expect("parses");
        let mut p = Planner::new(&mut s);
        p.projection_subjects.push("P::d".into());
        let at = src.find("= 1").expect("value") as u32;
        p.splices.push(Splice {
            unit: p.session.unit_offset,
            start: at,
            end: at + 3,
            text: "= 2".into(),
            expects: Vec::new(),
        });
        let err = p.commit(false).expect_err("value change is structural");
        match err {
            TransformError::StructuralIdentity { element, broken } => {
                assert_eq!(element, "P::d");
                assert!(
                    broken
                        .iter()
                        .any(|b| b.starts_with('-') && b.contains("= 1")),
                    "{broken:?}"
                );
                assert!(
                    broken
                        .iter()
                        .any(|b| b.starts_with('+') && b.contains("= 2")),
                    "{broken:?}"
                );
            }
            other => panic!("wrong refusal: {other}"),
        }
        assert_eq!(s.source(s.unit_offset).unwrap(), src, "rolled back");
    }

    #[test]
    fn relocation_mode_rides_the_public_pipeline_unchanged() {
        // The flag composes with ordinary planned ops: a rename under
        // relocation discipline commits, correspondence maps ids.
        let mut s = session();
        let a = s.resolved().resolve_qualified("P::A").expect("resolves");
        let mut p = Planner::new(&mut s);
        p.refuse_new_unresolved = true;
        p.plan(&Op::Rename {
            e: a,
            new_name: "Alpha".into(),
        })
        .expect("plans");
        let report = p.commit(false).expect("commits");
        assert!(!report.id_map.is_empty(), "rename moves ownership paths");
        assert!(s.source(s.unit_offset).unwrap().contains("part def Alpha;"));
    }
}

#[cfg(test)]
mod minimize_tests {
    use super::overlapping_candidates;

    #[test]
    fn disjoint_ranges_all_survive() {
        let ranges = [(1, 0, 5), (1, 5, 9), (1, 20, 24), (2, 0, 4)];
        assert!(overlapping_candidates(&ranges).is_empty());
    }

    #[test]
    fn a_nested_range_is_reported() {
        // The second range sits inside the first: applying both in one
        // forward sweep would slice backwards.
        let ranges = [(1, 0, 12), (1, 4, 8), (1, 14, 18)];
        assert_eq!(overlapping_candidates(&ranges), vec![1]);
    }

    #[test]
    fn a_straddling_range_is_reported() {
        let ranges = [(1, 0, 12), (1, 8, 20)];
        assert_eq!(overlapping_candidates(&ranges), vec![1]);
    }

    #[test]
    fn a_whole_overlapping_run_is_reported_against_the_first_kept_range() {
        // The third range clears the second but still reaches into the
        // first, which is the one that will be applied.
        let ranges = [(1, 0, 30), (1, 4, 8), (1, 10, 40), (1, 40, 44)];
        assert_eq!(overlapping_candidates(&ranges), vec![1, 2]);
    }

    #[test]
    fn ranges_in_different_units_never_overlap() {
        let ranges = [(1, 0, 30), (2, 4, 8), (3, 4, 8)];
        assert!(overlapping_candidates(&ranges).is_empty());
    }
}

#[cfg(test)]
mod unused_imports_tests;
