//! Navigation: hover, definition, references, highlights, rename,
//! workspace symbols — the model-backed features.
//!
//! The engine is a `sysmlv2_transform::Session` over the *workspace* —
//! every model unit under the root (or the host-seeded in-memory
//! workspace, for filesystem-less hosts) with open-document texts
//! overlaid, plus the standard library when the server was started
//! with `--lib` — rebuilt lazily whenever the open-document
//! fingerprint changes. The workspace scope matters: an import-
//! introduced name declared in a unit that is not open must still
//! resolve, or definition/references/hover die at the file boundary.
//! Requests here are user-initiated (a hover, a rename), not
//! per-keystroke, so an on-demand rebuild — sub-ms without a library,
//! ~0.15 s warm with one via the library cache — is the right cost model.
//! Everything answers off the reference-site table plus
//! `declaration_at`/`declaration_site`; rename goes through the
//! Session edit engine, so shadowing captures and reference-stranding
//! *reject atomically* and surface as request errors instead of
//! corrupting the model.

use crate::accept::Accept;
use crate::position::{Mapper, UnitMappers, offset32};
use crate::{Document, Encoding, Report};
use lsp_types::{Location, Position, Range, TextEdit, Uri, WorkspaceEdit};
use std::collections::{BTreeMap, HashMap};
use std::path::PathBuf;
use std::str::FromStr;
use std::sync::Arc;
use sysmlv2_parser::json::{ElementRef, RefSite};
use sysmlv2_parser::span::Span;
use sysmlv2_parser::visit::Visit as _;
use sysmlv2_transform::{Library, Session, SessionError};

mod namespaces;
#[cfg(test)]
pub(crate) use namespaces::WORK;
use namespaces::{Access, Links, SymbolTable};

/// The document a workspace table is layered for, and every other open
/// document's text — held, and compared by identity, so a document
/// reopened with new text never passes for the one it replaces.
struct RestKey {
    current: String,
    others: Vec<(String, Arc<str>)>,
}

impl RestKey {
    fn same(&self, other: &RestKey) -> bool {
        self.current == other.current
            && self.others.len() == other.others.len()
            && self
                .others
                .iter()
                .zip(&other.others)
                .all(|((a, x), (b, y))| a == b && Arc::ptr_eq(x, y))
    }
}

/// The session fingerprint, the package, and the actions planned for it.
type SplitCache = (Vec<(String, i32)>, ElementRef, Vec<(String, WorkspaceEdit)>);

/// The session read-only navigation answers from while the strict one
/// cannot build (see [`Nav::read_session`]): the strict session's
/// sources, the units that do not parse salvaged, for one fingerprint —
/// `None` when even that could not build.
struct Tolerant {
    fingerprint: Vec<(String, i32)>,
    session: Option<Session>,
    /// Each unit as written, in the order the session was built from:
    /// positions in the session's units are read off these. Salvage
    /// keeps every byte's offset, not every line break — it may write a
    /// `;` over one.
    written: Vec<(String, String)>,
    /// Its build (see [`Nav::built`]).
    build: u64,
}

/// A session read-only navigation answers from (see
/// [`Nav::read_session`]), with the units as written when it is the
/// tolerant one.
struct ReadSession<'a> {
    session: &'a mut Session,
    written: Option<&'a [(String, String)]>,
}

impl ReadSession<'_> {
    /// Where `span` of `unit` lies, read off the unit as written.
    fn location(&self, unit: usize, span: Span, enc: Encoding) -> Option<Location> {
        let written = self.session.units().find_map(|(i, name, _)| {
            (i == unit)
                .then(|| {
                    self.written?
                        .iter()
                        .find(|(n, _)| n == name)
                        .map(|(_, t)| (name, t))
                })
                .flatten()
        });
        match written {
            Some((name, text)) => Some(Location {
                uri: Uri::from_str(name).ok()?,
                range: Mapper::new(text, enc).range(span),
            }),
            None => Nav::location_static(self.session, unit, span, enc),
        }
    }
}

/// A statement's sources key with where it starts, a session's build,
/// and how the texts that session was built from differ from the
/// statement's (see [`Nav::cut_answer`]).
type ReusedChanges = ((u64, u32), u64, Option<Arc<crate::reuse::Changes>>);

/// What a member-access receiver reaches (see
/// `Nav::chain_member_completions`): its members as (name, kind,
/// detail), and whether it is a package or another namespace.
struct Reached {
    members: Vec<(String, lsp_types::CompletionItemKind, Option<String>)>,
    namespace: bool,
}

/// The package a split request names.
pub enum SplitTarget {
    /// The declaration whose name spans `offset` of the unit `uri`.
    Offset { uri: Uri, offset: u32 },
    /// A qualified name (quoted segments allowed) resolved from the
    /// root namespace.
    Package(String),
}

/// One planned unit of a split — see [`Nav::split_request`].
#[derive(serde::Serialize, Debug, Clone)]
#[serde(rename_all = "camelCase")]
pub struct SplitResponseEntry {
    /// Qualified name before the split.
    pub qualified_name: String,
    pub name: String,
    /// The root-level name the package takes when its own would collide.
    pub new_name: Option<String>,
    /// The package's name after the split as a request `package`
    /// spells it: its root-level name, quoted when needed.
    pub root_name: String,
    /// The new unit's uri.
    pub uri: String,
    /// Size of the package's text.
    pub bytes: usize,
    /// Directly nested packages — what a deeper level would split; a
    /// leaf has none.
    pub nested: usize,
}

/// The package a split starts from.
#[derive(serde::Serialize, Debug, Clone)]
#[serde(rename_all = "camelCase")]
pub struct SplitResponseRoot {
    pub name: String,
    pub qualified_name: String,
    /// The unit the package is declared in.
    pub uri: String,
}

/// A planned split, with its annotated edit when one was asked for.
#[derive(serde::Serialize, Debug, Clone)]
#[serde(rename_all = "camelCase")]
pub struct SplitResponse {
    pub root: SplitResponseRoot,
    /// The uri prefix the new units are named under.
    pub directory: String,
    pub entries: Vec<SplitResponseEntry>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub edit: Option<WorkspaceEdit>,
}

pub struct Nav {
    pub library: Option<Library>,
    /// Every named symbol in the standard library with its qualified
    /// path, and the library's imports — computed once per Nav from the
    /// library *texts* (a syntax-tier parse; no model build), since
    /// structure is syntactic. Feeds both the flat completion list
    /// (packages + direct members) and the qualifier-filtered
    /// import/member completions; shared with every workspace table,
    /// which layers over it.
    library_symbols: Option<Arc<SymbolTable>>,
    /// The measurement-unit types the library declares (see
    /// [`crate::kinds::unit_types`]), built with the library's table.
    library_unit_types: std::collections::HashSet<String>,
    /// Workspace root: on-disk units under it join every session build
    /// (open documents overlaid), so navigation crosses into units the
    /// client never opened. Re-read at rebuild time — the worker tier's
    /// staleness convention (off-editor changes surface on the next
    /// edit).
    root: Option<PathBuf>,
    /// In-memory workspace units for hosts without a filesystem (the
    /// push-driven WASM frontend): `(uri string, text)`, keyed by the
    /// same uri strings the client opens documents under. Takes the
    /// role of the root walk when set.
    workspace: Option<Arc<Vec<(String, String)>>>,
    /// Qualified symbols and imports of the seeded workspace units,
    /// parsed once per seed (the [`Self::library_symbols`] pattern) —
    /// import fixes and completions must see the whole workspace, not
    /// just what happens to be open, without a per-keystroke
    /// full-workspace parse. Units shadowed by an open document are
    /// filtered at query time.
    workspace_seed_symbols: Option<(Vec<QualifiedSymbol>, Links)>,
    /// The workspace below the document last completed in — every
    /// other open document and the seed units not open — kept while the
    /// key (that document, the others' texts) holds.
    workspace_rest: Option<(RestKey, Arc<SymbolTable>)>,
    session: Option<Session>,
    /// The fingerprint the strict session last failed to build for — a
    /// unit that does not parse — so a request with the same documents
    /// does not parse them all again to find that out.
    strict_failed: Option<Vec<(String, i32)>>,
    /// Read-only navigation's session while the strict one cannot build.
    tolerant: Option<Tolerant>,
    /// What the tolerant session's builds made of each unit.
    tolerant_salvage: crate::salvage::SalvageCache,
    /// Failures behind an empty answer, waiting for the server to pass
    /// them to the client ([`Nav::take_reports`]).
    reports: Vec<Report>,
    /// (uri string, version) per open doc at the last rebuild.
    fingerprint: Vec<(String, i32)>,
    /// The solverless verify pass shared by inlay hints and code
    /// lenses, cached per session build (both fire on every scroll —
    /// recomputing per request would run propagation dozens of times
    /// over an unchanged model).
    verify: Option<sysmlv2_solve::VerifyReport>,
    /// The split actions last computed for a package, keyed by the
    /// session fingerprint: the cursor rests on a package name across
    /// many code-action requests, and each plan is a whole-workspace
    /// dry run.
    split_cache: Option<SplitCache>,
    /// The lint pass over the current session, keyed by the
    /// configuration it ran with: code-action requests arrive per
    /// cursor move and must not re-lint the workspace each time.
    lint: Option<(u64, Vec<sysmlv2_lint::Finding>)>,
    /// The workspace's lint configuration, re-read only when the file
    /// changes.
    config: LintConfig,
    /// Suppress evaluated-value inlay hints that would restate the
    /// declared value expression verbatim (`x = 3.63 [kg]` needs no
    /// ` = 3.63 [kg]` hint). Default on; hosts flip it via
    /// `initializationOptions.hideRedundantValueHints` or the push
    /// server's setter.
    hide_redundant_value_hints: bool,
    /// The client declared `completionItem.snippetSupport` at
    /// `initialize`: a repair suffix riding a completion's main edit
    /// may carry a `$0` stop that parks the cursor before the
    /// auto-inserted text. Off by default — a non-snippet client
    /// would render the stop literally.
    snippet_completions: bool,
    /// The client declared `completionItem.insertReplaceSupport` at
    /// `initialize`: with the cursor inside a word, a completion's main
    /// edit carries an insert range (up to the cursor) and a replace
    /// range (through the rest of the word), and the client's own
    /// setting picks one. Off by default — other clients get the
    /// insert range alone.
    insert_replace_completions: bool,
    /// The client declared `signatureHelp.signatureInformation.
    /// parameterInformation.labelOffsetSupport` at `initialize`: a
    /// signature's parameters are sent as offsets into its label rather
    /// than as substrings the client searches for.
    signature_label_offsets: bool,
    /// Accepting a unit completion inside the quantity bracket of an
    /// *untyped* attribute declaration also declares the type the unit
    /// determines (exactly one, or nothing is inserted). Default on;
    /// hosts flip it via `initializationOptions.inferUnitTypes` or the
    /// push server's setter.
    infer_unit_types: bool,
    /// The completion tier's session: the open docs with the statement
    /// being typed blanked out — a mid-statement cursor nearly always
    /// means a parse error, which sessions refuse. Keyed by a hash of
    /// everything *outside* the blanked statement, so keystrokes
    /// within one statement reuse the build.
    completion_session: Option<(u64, Session)>,
    /// The key of the completion session build that failed last: the
    /// same sources would fail again, so they are not rebuilt until they
    /// change.
    completion_failed: Option<u64>,
    /// The key of the sources, the member the live text reads a
    /// statement in cut out whole, whose model named no members last
    /// (see [`Self::read_inherited`]): the same text would name none
    /// again, so it is not built again until it changes.
    member_cut_failed: Option<u64>,
    /// Sessions built so far, of either kind, and the count at which
    /// [`Self::session`] and [`Self::completion_session`] were built:
    /// which of the two is the most recent.
    builds: u64,
    session_build: u64,
    completion_build: u64,
    /// The sources [`Self::session`] and [`Self::completion_session`]
    /// were built from, as written (the statement being typed cut out of
    /// the latter): what their answers are current for.
    session_sources: Vec<(String, String)>,
    completion_sources: Vec<(String, String)>,
    /// The inherited members last named for enclosing elements, most
    /// recent first, by the text they depend on (see
    /// [`Self::inherited_members`]).
    member_cache: Vec<(u64, Vec<ScopeMember>)>,
    /// Each seeded unit's name and a hash of its text, taken once per
    /// seed: what a named member's key holds for the units not open (see
    /// [`Self::inherited_members`]).
    seed_hashes: Vec<(String, u64)>,
    /// The library's units in a session's model, classified once per
    /// session build (see [`crate::units::UnitEntry`]), by library symbol
    /// index, with the build they were classified in (see [`Read`]).
    library_units: Option<(u64, Vec<(usize, crate::units::UnitEntry)>)>,
    /// How the texts each of the last few sessions built was built from
    /// differ from those a build for a statement would read (see
    /// [`Self::cut_answer`]): the key of the statement's sources with
    /// where it starts, the session's build, and the changes — `None`
    /// where the check cannot place them. Most recent first.
    reused: Vec<ReusedChanges>,
    /// What the import and alias statements of the sessions built make
    /// an answer read off them depend on (see [`crate::reuse::Imports`]),
    /// by build.
    reused_imports: Vec<(u64, Arc<crate::reuse::Imports>)>,
    /// What the completion session's builds made of each workspace unit
    /// (see [`crate::salvage::SalvageCache`]).
    salvage: crate::salvage::SalvageCache,
}

impl Nav {
    pub fn new(library: Option<PathBuf>, root: Option<PathBuf>) -> Nav {
        let mut nav = Self::new_with(library.map(Library::dir));
        nav.config = LintConfig::under(root.as_deref());
        nav.root = root;
        nav
    }

    /// [`Self::new`] over any [`Library`] source — in-memory library
    /// units included (the push-driven WASM frontend's shape) — and
    /// without a workspace root (seed one with
    /// [`Self::set_workspace_sources`]).
    pub fn new_with(library: Option<Library>) -> Nav {
        Nav {
            library,
            library_symbols: None,
            library_unit_types: std::collections::HashSet::new(),
            root: None,
            workspace: None,
            workspace_seed_symbols: None,
            workspace_rest: None,
            session: None,
            fingerprint: Vec::new(),
            verify: None,
            lint: None,
            split_cache: None,
            hide_redundant_value_hints: true,
            snippet_completions: false,
            insert_replace_completions: false,
            signature_label_offsets: false,
            infer_unit_types: true,
            completion_session: None,
            completion_failed: None,
            member_cut_failed: None,
            builds: 0,
            session_build: 0,
            completion_build: 0,
            session_sources: Vec::new(),
            completion_sources: Vec::new(),
            member_cache: Vec::new(),
            seed_hashes: Vec::new(),
            library_units: None,
            reused: Vec::new(),
            reused_imports: Vec::new(),
            salvage: crate::salvage::SalvageCache::default(),
            strict_failed: None,
            tolerant: None,
            tolerant_salvage: crate::salvage::SalvageCache::default(),
            reports: Vec::new(),
            config: LintConfig::under(None),
        }
    }

    /// The workspace's lint configuration. Shared with the formatter,
    /// whose project style comes out of the same file.
    pub fn lint_config(&mut self) -> &sysmlv2_lint::Config {
        self.config.get().1
    }

    /// Set whether completion edits may use snippet syntax (`$0`
    /// cursor stops on statement-repair suffixes) — from the client's
    /// `completionItem.snippetSupport` capability at `initialize`.
    pub fn set_snippet_completions(&mut self, on: bool) {
        self.snippet_completions = on;
    }

    /// Set whether completion edits may carry insert and replace ranges
    /// both — from the client's `completionItem.insertReplaceSupport`
    /// capability at `initialize`.
    pub fn set_insert_replace_completions(&mut self, on: bool) {
        self.insert_replace_completions = on;
    }

    /// Whether completion edits may carry insert and replace ranges
    /// both (see [`Self::set_insert_replace_completions`]).
    pub fn insert_replace_completions(&self) -> bool {
        self.insert_replace_completions
    }

    /// Set whether signature help may send parameters as offsets into
    /// the signature's label — from the client's `labelOffsetSupport`
    /// capability at `initialize`.
    pub fn set_signature_label_offsets(&mut self, on: bool) {
        self.signature_label_offsets = on;
    }

    /// Whether signature help may send parameters as label offsets (see
    /// [`Self::set_signature_label_offsets`]).
    pub fn signature_label_offsets(&self) -> bool {
        self.signature_label_offsets
    }

    /// What accepting an item of a completion request in `uri` writes
    /// (see [`Accept`]), as the client's capabilities allow.
    fn accept<'a>(&self, text: &'a str, uri: &Uri, cx: &CompletionCx, enc: Encoding) -> Accept<'a> {
        Accept::new(
            text,
            enc,
            cx,
            crate::dialect_of(uri),
            self.snippet_completions,
            self.insert_replace_completions,
        )
    }

    /// Set whether evaluated-value inlay hints that restate the
    /// declared expression verbatim are suppressed (they are by
    /// default). Answers change without any source changing, so the
    /// host should ask clients to re-pull hints after a flip.
    pub fn set_hide_redundant_value_hints(&mut self, on: bool) {
        self.hide_redundant_value_hints = on;
    }

    /// Set whether accepting a unit completion inside an untyped
    /// attribute's quantity bracket also declares the type the unit
    /// determines (on by default).
    pub fn set_infer_unit_types(&mut self, on: bool) {
        self.infer_unit_types = on;
    }

    /// Replace the in-memory workspace units (filesystem-less hosts).
    /// Unit names must be the same uri strings the client opens
    /// documents under, or an open document duplicates its on-model
    /// unit instead of overlaying it.
    ///
    /// The completion tier's session stays: it is kept by the texts it
    /// was built from, so a re-seed that leaves them as they were — the
    /// host seeds every open document after each pause in typing —
    /// leaves it current, and one that changes them has the next request
    /// build another.
    pub fn set_workspace_sources(&mut self, units: Arc<Vec<(String, String)>>) {
        self.workspace = Some(units);
        self.workspace_seed_symbols = None;
        self.workspace_rest = None;
        self.seed_hashes = self
            .workspace
            .iter()
            .flat_map(|units| units.iter())
            .map(|(name, text)| {
                use std::hash::{Hash, Hasher};
                let mut hasher = std::collections::hash_map::DefaultHasher::new();
                text.hash(&mut hasher);
                (name.clone(), hasher.finish())
            })
            .collect();
        self.invalidate_navigation();
    }

    /// Drop the cached sessions (after a rename commit mutated one, the
    /// client must re-sync before answers are trustworthy again).
    pub fn invalidate(&mut self) {
        self.invalidate_navigation();
        self.completion_session = None;
        self.library_units = None;
        self.completion_sources.clear();
    }

    /// Drop the navigation session and what was derived from it: it is
    /// kept by the open documents' versions, which tell nothing of the
    /// seeded units a re-seed replaces.
    fn invalidate_navigation(&mut self) {
        self.session = None;
        self.fingerprint.clear();
        self.strict_failed = None;
        self.tolerant = None;
        self.verify = None;
        self.lint = None;
        self.split_cache = None;
        self.session_sources.clear();
    }

    /// Completions for a member access (`tank.|`, `tank.liq|`, `a.b.|`,
    /// `wheels#(1).|`, `f(x).|`): the members the receiver could reach.
    /// The receiver resolves the way the evaluator resolves it — a head
    /// name from the innermost enclosing declaration outward (inherited
    /// members included, via [`ResolvedModel::member_of`]), each step as
    /// a member of the one before it, an indexed feature as its elements
    /// (which have the feature's type), an invocation as its callee's
    /// result — and enumeration takes the reached element's own features
    /// and those it inherits through its written specializations (its
    /// declared types, conjugated port types included, and their
    /// specialization closure), nearest declaration winning a name. The
    /// inheritance is the model's own (`Type::inheritedMemberships`):
    /// a feature an owned feature redefines is not inherited, though a
    /// chain step naming it still resolves, and a protected member is
    /// listed even where a step from outside its type cannot reach it.
    /// A receiver named by a reference (`x.`, `P::x.`) also takes the
    /// `metadata` keyword of a metadata access, sorted after its members
    /// — unless it is a package, whose dot is usually a slip for `::`.
    /// `None` when the cursor does not follow a member-access dot. A
    /// receiver that does not resolve answers an empty list: after a dot
    /// the position-blind list is never what is wanted.
    ///
    /// [`ResolvedModel::member_of`]: sysmlv2_parser::json::ResolvedModel::member_of
    fn chain_member_completions(
        &mut self,
        docs: &BTreeMap<Uri, Document>,
        uri: &Uri,
        cx: &CompletionCx,
        enc: Encoding,
    ) -> Option<Vec<lsp_types::CompletionItem>> {
        let text = &docs.get(uri)?.text;
        // A member typed quoted (`q.'max|`): the receiver is read where the
        // quote opens; the accept still replaces the quoted name.
        let after_quote = cx
            .quoted
            .map(|q| q.open())
            .filter(|&open| open > 0 && text.as_bytes().get(open as usize - 1) == Some(&b'.'))
            .map(|open| completion_context(text, open, crate::dialect_of(uri)));
        let at = after_quote.as_ref().unwrap_or(cx);
        // The receiver: the name chain the context read, else — for a
        // chain ending in an index or an invocation, or one whose head is
        // qualified (`P::part.`), where that scan stops short — the
        // receiver read off the tokens.
        let chain_len: usize = at.dot_chain.iter().map(|link| link.len() + 1).sum();
        let head = (at.partial_start as usize).saturating_sub(chain_len);
        let qualified_head = text.get(..head).is_some_and(|t| t.ends_with("::"));
        let receiver = match at.dot_chain.as_slice() {
            chain if !chain.is_empty() && !qualified_head => {
                Some(crate::receiver::chain_expr(chain))
            }
            _ => {
                // A dot after a name is a member access even where the
                // tokens spell no receiver: it answers nothing, never the
                // position-blind list.
                let Some(span) =
                    crate::receiver::postfix_receiver(text, at.stmt_start, at.partial_start)
                else {
                    return (!at.dot_chain.is_empty()).then(Vec::new);
                };
                crate::receiver::parse_receiver(
                    &text[span.start as usize..span.end as usize],
                    crate::dialect_of(uri),
                )
            }
        };
        // `x.metadata` reads an element's metadata: a receiver named by a
        // reference takes the keyword once it resolves — but not a
        // package, whose dot is usually a slip for `::`, nor where a name
        // is typed quoted.
        let by_reference = after_quote.is_none()
            && receiver
                .as_ref()
                .is_some_and(|r| matches!(r.kind, sysmlv2_parser::ast::ExprKind::Ref(_)));
        let reached = receiver.and_then(|receiver| {
            self.receiver_members(docs, uri, at.stmt_start, cx.offset, &receiver)
        });
        let metadata = by_reference && reached.as_ref().is_some_and(|r| !r.namespace);
        let d = docs.get(uri)?;
        let accept = self.accept(&d.text, uri, cx, enc);
        let mut items: Vec<lsp_types::CompletionItem> = reached
            .map(|r| r.members)
            .unwrap_or_default()
            .into_iter()
            .map(|(name, kind, detail)| {
                let label = crate::outline::spell_name(&name);
                accept.name(&name).fill(
                    lsp_types::CompletionItem {
                        // The members in the order of their labels, as
                        // with no sort text; the keyword after them all.
                        sort_text: Some(format!("0{label}")),
                        label,
                        kind: Some(kind),
                        detail,
                        ..Default::default()
                    },
                    Vec::new(),
                )
            })
            .collect();
        if metadata {
            items.push(lsp_types::CompletionItem {
                label: "metadata".to_string(),
                kind: Some(lsp_types::CompletionItemKind::KEYWORD),
                sort_text: Some("1metadata".to_string()),
                ..Default::default()
            });
        }
        Some(items)
    }

    /// What `receiver` reaches (see [`Reached`] and
    /// [`Self::chain_member_completions`]), read in a model without the
    /// statement starting at `stmt_start` (see
    /// [`Self::statement_answer`]); the declarations enclosing the
    /// statement's start are the scopes a head name resolves from. `None`
    /// when no session can be built or the receiver does not resolve.
    fn receiver_members(
        &mut self,
        docs: &BTreeMap<Uri, Document>,
        uri: &Uri,
        stmt_start: u32,
        cursor: u32,
        receiver: &sysmlv2_parser::ast::Expr,
    ) -> Option<Reached> {
        self.statement_answer(docs, uri, stmt_start, cursor, |at| {
            let resolved = at.session.resolved();
            let enclosing = crate::receiver::enclosing_declarations(resolved, at.unit, at.at);
            at.needs.scopes(&enclosing);
            at.needs.expr(receiver);
            let mut reached = Vec::new();
            let target =
                crate::receiver::receiver_reached(resolved, &enclosing, receiver, &mut reached)?;
            reached.into_iter().for_each(|e| at.needs.read(e));
            let mut seen = std::collections::HashSet::new();
            let mut members = Vec::new();
            for m in resolved.effective_features(target, false) {
                let Some(name) = resolved.element_lookup_name(m) else {
                    continue;
                };
                if seen.insert(name.clone()) {
                    let kind = member_kind(resolved.element_type(m));
                    members.push((name, kind, resolved.element_qualified_name(m)));
                }
            }
            Some(Reached {
                members,
                namespace: matches!(
                    resolved.element_type(target),
                    "Package" | "LibraryPackage" | "Namespace"
                ),
            })
        })
    }

    /// Completions inside a `[` (see [`crate::units::bracket_at`]). In
    /// a quantity's unit bracket, the units: those of the quantity the
    /// value is declared as first (a `DurationValue` takes `s`, `min`,
    /// `h`, `d`) — for a value no declaration's whole, the quantity of
    /// the operand it is compared with or added to, or of the parameter
    /// it binds as an argument (see [`crate::units::unit_context`]) —
    /// each group's short symbols ahead of its long names,
    /// the other units after them — a factor of a compound unit (`m` in
    /// `[m/s]`) measures something else than the whole — each carrying
    /// its import and an untyped declaration's inferred typing like any
    /// other name. In any other bracket — a multiplicity, a filter —
    /// nothing while nothing or a number is typed there; nothing either
    /// right after a `[` that opens no bracket (one in a comment or a
    /// string) or an import's filter condition. `None` outside a
    /// bracket, after a qualifier, once a name is typed in any bracket
    /// but a unit's (a bound may name a feature, `[1..numberOfBolts]`),
    /// or in a unit bracket no model can be built for.
    fn bracket_completions(
        &mut self,
        docs: &BTreeMap<Uri, Document>,
        uri: &Uri,
        cx: &CompletionCx,
        enc: Encoding,
        unit_type_cx: Option<&UnitTypeCx>,
    ) -> Option<Vec<lsp_types::CompletionItem>> {
        let text = &docs.get(uri)?.text;
        let after_bracket = text
            .get(..cx.offset as usize)
            .is_some_and(|t| t.ends_with('['));
        // An import's filter condition (`::*[@Safe`) lists the import's
        // names once a word is typed: a `[` alone offers nothing.
        if cx.import {
            return after_bracket.then(Vec::new);
        }
        let dialect = crate::dialect_of(uri);
        // A qualified name in a unit bracket (`[SI::k`) is a unit of that
        // namespace; anywhere else in a bracket (`[1..Limits::`), a member
        // of it like any other.
        let qualified = (!cx.qualifier.is_empty()).then(|| cx.qualifier.join("::"));
        let (open, header) = match crate::units::bracket_at(text, cx, dialect) {
            Some(crate::units::Bracket::Unit { open, header }) => (open, header),
            _ if qualified.is_some() => return None,
            // A bound or a filter: quiet while nothing or a number is
            // typed; a name typed there (`[1..count`, `[@Safe`) is
            // completed like one anywhere else.
            Some(crate::units::Bracket::Other) => {
                let typed = &text.as_bytes()[cx.partial_start as usize..cx.offset as usize];
                return typed.first().is_none_or(u8::is_ascii_digit).then(Vec::new);
            }
            None => return after_bracket.then(Vec::new),
        };
        let accept = self.accept(text, uri, cx, enc);
        // Only a name accepted as the whole bracket content, not as a
        // factor of a compound unit, is measured by the declared
        // quantity: nothing but blanks between the `[` and where
        // accepting it starts replacing (a typed quote, or the typed
        // spelling of the name, it absorbs).
        let replacement = crate::accept::Replacement::new(text, cx);
        let written = qualified.as_ref().map(|path| format!("{path}::"));
        let whole = |name: &str| {
            text.get(open as usize + 1..replacement.start_for(text, name) as usize)
                .is_some_and(|s| {
                    let s = s.trim();
                    s.is_empty()
                        || written
                            .as_deref()
                            .is_some_and(|w| s == w || s.strip_prefix("$::") == Some(w))
                })
        };
        let workspace = self.all_workspace_symbols(docs, uri, enc);
        let library_table = self.library_table();
        let library: &[QualifiedSymbol] = library_table.symbols();
        let parsed = if crate::is_kerml(uri.path().as_str()) {
            sysmlv2_parser::parser::parse_kerml_source(text)
        } else {
            sysmlv2_parser::parser::parse_source(text)
        };
        let auto = crate::autoimport::AutoImport::new(
            text,
            &parsed.unit,
            cx.offset,
            Span::new(cx.partial_start, cx.offset),
        )
        .with_reexports(&workspace);
        let cut = crate::salvage::typed_statement_cut(text, cx.stmt_start, cx.offset);
        // Rank: the declared quantity's short symbols, its long names,
        // then the other units' — within a group the workspace's units
        // ahead of the library's, then by package, in declaration order.
        // A unit not visible here claims no name; after a qualifier, the
        // namespace's own units and those it re-exports are the ones,
        // needing no import.
        let reexported: std::collections::HashSet<&str> = qualified
            .as_deref()
            .map(|path| {
                workspace
                    .reexported_members(path, Access::Clients)
                    .into_iter()
                    .map(|s| s.qualified.as_str())
                    .collect()
            })
            .unwrap_or_default();
        let mut ranked = self.cut_answer(docs, uri, cut, |at| {
            let unit_of: HashMap<String, usize> = at
                .session
                .units()
                .map(|(i, name, _)| (name.to_string(), i))
                .collect();
            let resolved = at.session.resolved();
            let enclosing = crate::receiver::enclosing_declarations(resolved, at.unit, at.at);
            at.needs.scopes(&enclosing);
            at.needs.units();
            let declared = match header {
                Some(h) => {
                    let header = &text[h.start as usize..h.end as usize];
                    at.needs.declaration(resolved, &enclosing, header, dialect);
                    crate::units::declared_measure(resolved, &enclosing, header, dialect)
                }
                None => crate::units::unit_context(text, cx).and_then(|context| {
                    at.needs
                        .context(resolved, &enclosing, text, &context, dialect);
                    crate::units::context_measure(resolved, &enclosing, text, &context, dialect)
                }),
            };
            // The workspace's units, classified per request, by what their
            // declarations say; the library's, once per session build.
            let mut units = crate::units::Units::new(resolved);
            let mut tops = None;
            let mut workspace_units: Vec<(&QualifiedSymbol, crate::units::UnitEntry)> = Vec::new();
            for s in workspace.iter().filter(|s| !s.effective) {
                let site = s.site.as_ref().map(|(uri, _)| uri.as_str());
                let Some(element) =
                    declared_element(resolved, &s.qualified, site, &unit_of, &mut tops)
                else {
                    continue;
                };
                if let Some(entry) = units.entry_of(resolved, element, &s.name) {
                    at.needs.read(element);
                    workspace_units.push((s, entry));
                }
            }
            if at
                .library_units
                .as_ref()
                .is_none_or(|(build, _)| *build != at.build)
            {
                *at.library_units = Some((
                    at.build,
                    library
                        .iter()
                        .enumerate()
                        .filter(|(_, s)| s.depth <= 1)
                        .filter_map(|(i, s)| {
                            Some((i, units.entry(resolved, &s.qualified, &s.name)?))
                        })
                        .collect(),
                ));
            }
            let library_units = &at.library_units.as_ref()?.1;
            let mut seen = std::collections::HashSet::new();
            let mut ranked = Vec::new();
            for (from_library, s, entry) in workspace_units
                .iter()
                .map(|(s, entry)| (false, *s, entry))
                .chain(
                    library_units
                        .iter()
                        .map(|(i, entry)| (true, &library[*i], entry)),
                )
            {
                if seen.contains(s.name.as_str()) {
                    continue;
                }
                let import = match qualified.as_deref() {
                    Some(path)
                        if s.is_member_of(path) || reexported.contains(s.qualified.as_str()) =>
                    {
                        None
                    }
                    Some(_) => continue,
                    None => match reach(&auto, s) {
                        Some(import) => import,
                        None => continue,
                    },
                };
                seen.insert(s.name.as_str());
                let fits = whole(&s.name)
                    && declared
                        .as_ref()
                        .is_some_and(|d| crate::units::Units::fits(resolved, entry, d));
                let package = s
                    .qualified
                    .strip_suffix(s.name.as_str())
                    .unwrap_or_default();
                ranked.push((
                    (
                        u8::from(!fits) * 2 + u8::from(!entry.short),
                        from_library,
                        package,
                    ),
                    s,
                    import,
                ));
            }
            Some(ranked)
        })?;
        ranked.sort_by_key(|&(key, ..)| key);
        // Where the declared quantity puts its own units first, only they
        // keep the typed word's whole match of a symbol of one or two
        // characters (see [`unmatched_whole`]): `k` ranks `kg` ahead of
        // kelvin's `K`.
        let fitting = ranked.first().is_some_and(|((rank, ..), ..)| *rank < 2);
        let mapper = Mapper::new(text, enc);
        let mut out = Vec::with_capacity(ranked.len());
        let mut meta = Vec::with_capacity(ranked.len());
        for (i, ((rank, ..), s, import)) in ranked.into_iter().enumerate() {
            let (imports, label_details) =
                match import.and_then(|edit| import_for(&mapper, dialect, s, edit)) {
                    Some((edits, details)) => (edits, Some(details)),
                    None => (Vec::new(), None),
                };
            meta.push(offered(i, s));
            let mut edits = accept.name(&s.name);
            let label = crate::outline::spell_name(&s.name);
            if fitting && rank >= 2 && label.chars().count() <= 2 {
                edits.filter_text = Some(unmatched_whole(
                    edits.filter_text.as_deref().unwrap_or(&label),
                    s.long.as_deref().unwrap_or(&label),
                ));
            }
            out.push(edits.fill(
                lsp_types::CompletionItem {
                    label: crate::outline::spell_name(&s.name),
                    kind: Some(s.kind),
                    detail: Some(s.qualified.clone()),
                    documentation: s.documentation(),
                    label_details,
                    // A client ranks equally good matches by this: the
                    // order above.
                    sort_text: Some(format!("{i:05}")),
                    ..Default::default()
                },
                imports,
            ));
        }
        if let Some(tcx) = unit_type_cx {
            self.append_unit_type_edits(docs, uri, enc, (cx, tcx), &meta, &mut out);
        }
        Some(out)
    }

    /// The session over the current open documents, rebuilding if any
    /// version moved. `None` when a unit does not parse (see
    /// [`Self::build_session`]) — found once per fingerprint — or the
    /// library cannot be read.
    fn session(&mut self, docs: &BTreeMap<Uri, Document>) -> Option<&mut Session> {
        let fp = Self::fingerprint_of(docs);
        if self.session.is_none() || fp != self.fingerprint {
            if self.strict_failed.as_ref() == Some(&fp) {
                return None;
            }
            let sources = self.assemble_sources(docs, &fp);
            let Some(session) = self.build_session(sources.clone()) else {
                self.strict_failed = Some(fp);
                return None;
            };
            self.session = Some(session);
            self.session_sources = sources;
            self.tolerant = None;
            self.builds += 1;
            self.session_build = self.builds;
            self.fingerprint = fp;
            self.verify = None;
            self.lint = None;
            self.split_cache = None;
        }
        self.session.as_mut()
    }

    /// The models held right now: the strict session, read-only
    /// navigation's tolerant one, the completion session.
    #[cfg(test)]
    pub(crate) fn sessions_held(&self) -> usize {
        usize::from(self.session.is_some())
            + usize::from(self.tolerant.as_ref().is_some_and(|t| t.session.is_some()))
            + usize::from(self.completion_session.is_some())
    }

    /// (uri string, version) per open document, sorted: what a session
    /// is current for.
    fn fingerprint_of(docs: &BTreeMap<Uri, Document>) -> Vec<(String, i32)> {
        let mut fp: Vec<(String, i32)> = docs
            .iter()
            .map(|(u, d)| (u.to_string(), d.version))
            .collect();
        fp.sort();
        fp
    }

    /// The session read-only navigation — hover, definition, document
    /// highlights — answers from: the strict session, else, while a unit
    /// does not parse, one the units that do not parse join salvaged
    /// (see [`crate::salvage`]) or, when they cannot be, stay out of. It
    /// answers for everything outside what salvage blanks, which is
    /// enough to show and to jump; references, rename, code actions and
    /// refactors plan over every reference and keep the strict session.
    /// Built once per fingerprint, reusing what the last build made of
    /// each unit.
    fn read_session(&mut self, docs: &BTreeMap<Uri, Document>) -> Option<ReadSession<'_>> {
        if self.session(docs).is_some() {
            return self.session.as_mut().map(|session| ReadSession {
                session,
                written: None,
            });
        }
        let fp = Self::fingerprint_of(docs);
        if self.tolerant.as_ref().is_none_or(|t| t.fingerprint != fp) {
            self.tolerant = None;
            // The strict session is for versions these documents have
            // left, and answers nothing for them: let it go rather than
            // hold a third model beside this one and the completion
            // session's. The next strict build replaces it anyway.
            self.session = None;
            self.session_sources = Vec::new();
            self.verify = None;
            self.lint = None;
            self.split_cache = None;
            let sources = self.assemble_sources(docs, &fp);
            let written = sources.clone();
            let salvaged = self.tolerant_salvage.salvage_all(sources);
            let session = self.build_parsed_session(salvaged);
            self.builds += 1;
            self.tolerant = Some(Tolerant {
                fingerprint: fp,
                session,
                written,
                build: self.builds,
            });
        }
        let t = self.tolerant.as_mut()?;
        Some(ReadSession {
            session: t.session.as_mut()?,
            written: Some(&t.written),
        })
    }

    /// The session source list: workspace units first (in-memory seed,
    /// else a root walk), open documents overlaid — the worker tier's
    /// convention, so imports into units that are not open still
    /// resolve.
    fn assemble_sources(
        &self,
        docs: &BTreeMap<Uri, Document>,
        fp: &[(String, i32)],
    ) -> Vec<(String, String)> {
        let mut sources: Vec<(String, String)> = match (&self.workspace, &self.root) {
            (Some(units), _) => units.as_ref().clone(),
            (None, Some(root)) => crate::worker::root_sources(root),
            (None, None) => Vec::new(),
        };
        for (u, _) in fp {
            let uri = Uri::from_str(u).unwrap();
            crate::worker::overlay_source(&mut sources, u, &docs[&uri].text);
        }
        sources
    }

    /// A session over `sources`, the configured library loaded. `None`
    /// when any unit fails to parse (sessions refuse parse errors) —
    /// the ordinary state of a document mid-edit, and the syntax tier
    /// already shows those errors; the units are parsed ahead of the
    /// library, so that refusal costs no model build. A library that
    /// cannot be read is not ordinary and is recorded for the client:
    /// without it every model-backed answer here is silently empty.
    fn build_session(&mut self, sources: Vec<(String, String)>) -> Option<Session> {
        let parses = |(name, text): &(String, String)| {
            let parse = if crate::is_kerml(name) {
                sysmlv2_parser::parser::parse_kerml_source(text)
            } else {
                sysmlv2_parser::parser::parse_source(text)
            };
            !parse.has_errors()
        };
        if !sources.iter().all(parses) {
            return None;
        }
        self.build_parsed_session(sources)
    }

    /// [`Self::build_session`] for the completion tier, where one unit's
    /// syntax errors must not take the rest of the workspace down with
    /// them: a unit that does not parse joins salvaged — a missing `;`
    /// written, the other members in error blanked, the braces they
    /// leave open closed (see [`crate::salvage`]) — or, when it cannot
    /// be salvaged, stays out.
    /// Its errors still reach the client through the syntax tier.
    /// Navigation that plans over references keeps the strict build — a
    /// rename planned over a salvaged unit would miss the references the
    /// salvage blanked; read-only navigation falls back to a salvaged
    /// session of its own (see [`Self::read_session`]).
    fn build_tolerant_session(&mut self, sources: Vec<(String, String)>) -> Option<Session> {
        let sources = self.salvage.salvage_all(sources);
        self.build_parsed_session(sources)
    }

    /// A session over `sources`, every one of which parses, built in one
    /// pass with the configured library — resolving the units, then
    /// loading the library into the session, would resolve them twice.
    fn build_parsed_session(&mut self, sources: Vec<(String, String)>) -> Option<Session> {
        #[cfg(test)]
        SESSION_BUILDS.with(|n| n.set(n.get() + 1));
        // The outcomes the most recent session settled on: the units this
        // one shares with it start from them.
        let settled = self
            .built_by_recency()
            .first()
            .and_then(|&kind| self.built(kind))
            .and_then(|(session, _)| session.settled_outcomes());
        match Session::from_sources_settled(sources, self.library.clone(), settled) {
            Ok(session) => Some(session),
            Err(e) => {
                // With every unit parsing, what refuses the session is the
                // library — or a blank unit name.
                let library = !matches!(
                    e,
                    SessionError::Parse { .. } | SessionError::InvalidUnitName(_)
                );
                self.note_failure(&e, library);
                None
            }
        }
    }

    /// Record a session failure for the client, unless it is a unit
    /// that does not parse — see [`Self::build_session`]. `library`
    /// asks for a visible message rather than a log line.
    fn note_failure(&mut self, e: &SessionError, library: bool) {
        self.reports.extend(Report::for_session_failure(e, library));
    }

    /// Failures behind an empty answer, for the server to pass on —
    /// navigation has no channel to the client of its own.
    pub(crate) fn take_reports(&mut self) -> Vec<Report> {
        std::mem::take(&mut self.reports)
    }

    /// The kinds of session built, the most recent first.
    fn built_by_recency(&self) -> Vec<Built> {
        let mut kinds: Vec<(u64, Built)> = Built::ALL
            .into_iter()
            .filter_map(|kind| Some((self.built(kind)?.1, kind)))
            .collect();
        kinds.sort_by_key(|&(build, _)| std::cmp::Reverse(build));
        kinds.into_iter().map(|(_, kind)| kind).collect()
    }

    /// The session of `kind` built, if one is, and its build.
    fn built(&self, kind: Built) -> Option<(&Session, u64)> {
        match kind {
            Built::Navigation => Some((self.session.as_ref()?, self.session_build)),
            Built::Tolerant => {
                let t = self.tolerant.as_ref()?;
                Some((t.session.as_ref()?, t.build))
            }
            Built::Completion => {
                Some((&self.completion_session.as_ref()?.1, self.completion_build))
            }
        }
    }

    /// [`Self::built`]'s session to read, with the sources it was built
    /// from as they were read — read-only navigation's tolerant one's as
    /// written, before salvage; the completion tier's with its statement
    /// cut out.
    fn built_mut(&mut self, kind: Built) -> Option<(&mut Session, &[(String, String)])> {
        match kind {
            Built::Navigation => Some((self.session.as_mut()?, &self.session_sources)),
            Built::Tolerant => {
                let t = self.tolerant.as_mut()?;
                Some((t.session.as_mut()?, &t.written))
            }
            Built::Completion => Some((
                &mut self.completion_session.as_mut()?.1,
                &self.completion_sources,
            )),
        }
    }

    /// The answer `read` gives for the statement being typed in `uri` —
    /// it starts at `stmt_start`, the cursor at `cursor` — in a model the
    /// statement is cut out of (see [`crate::salvage::typed_statement_cut`]
    /// and [`Self::cut_answer`]).
    fn statement_answer<T>(
        &mut self,
        docs: &BTreeMap<Uri, Document>,
        uri: &Uri,
        stmt_start: u32,
        cursor: u32,
        read: impl FnMut(&mut Read<'_>) -> Option<T>,
    ) -> Option<T> {
        let cut = crate::salvage::typed_statement_cut(&docs.get(uri)?.text, stmt_start, cursor);
        self.cut_answer(docs, uri, cut, read)
    }

    /// The answer `read` gives in a model of the workspace with `cut`
    /// taken out of `uri` (see [`Self::completion_session`]): off the
    /// completion session built from exactly those texts, else off the
    /// most recent session built, of either kind, whose texts differ from
    /// them only where the answer does not look (see [`crate::reuse`]) —
    /// so the next statement builds nothing where what it reads is as it
    /// was — else off a completion session built for them now. `None`
    /// when no session can be built or `read` answers nothing.
    fn cut_answer<T>(
        &mut self,
        docs: &BTreeMap<Uri, Document>,
        uri: &Uri,
        cut: Span,
        mut read: impl FnMut(&mut Read<'_>) -> Option<T>,
    ) -> Option<T> {
        let (sources, key) = self.cut_sources(docs, uri, cut);
        if self.completion_session.as_ref().map(|(k, _)| *k) != Some(key) {
            if self.completion_failed == Some(key) {
                return None;
            }
            let mut fresh = None;
            if let Some(answer) =
                self.reused_answer(uri, cut, (&sources, key), &mut fresh, &mut read)
            {
                return Some(answer);
            }
            let fresh = fresh.unwrap_or_else(|| self.salvage.salvage_all(sources.clone()));
            let Some(session) = self.build_parsed_session(fresh) else {
                self.completion_failed = Some(key);
                return None;
            };
            self.completion_session = Some((key, session));
            self.completion_sources = sources;
            self.builds += 1;
            self.completion_build = self.builds;
        }
        let (_, session) = self.completion_session.as_mut()?;
        let unit = Self::unit_of_static(uri, session)?;
        read(&mut Read {
            session,
            unit,
            at: cut.start,
            needs: crate::reuse::Needs::default(),
            library_units: &mut self.library_units,
            build: self.completion_build,
        })
    }

    /// [`Self::cut_answer`] off a session built from other texts than
    /// `sources` (keyed `key`), the most recent first, when what the
    /// answer read there is unchanged in them (see
    /// [`crate::reuse::Changes::allow`]). `fresh` holds the texts a build
    /// for the statement would read once they are worked out.
    fn reused_answer<T>(
        &mut self,
        uri: &Uri,
        cut: Span,
        (sources, key): (&[(String, String)], u64),
        fresh: &mut Option<Vec<(String, String)>>,
        read: &mut impl FnMut(&mut Read<'_>) -> Option<T>,
    ) -> Option<T> {
        let name = uri.to_string();
        for kind in self.built_by_recency() {
            let Some((_, build)) = self.built(kind) else {
                continue;
            };
            // Worked out once per statement and session.
            let known = self
                .reused
                .iter()
                .find(|m| m.0 == (key, cut.start) && m.1 == build)
                .map(|(_, _, changes)| changes.clone());
            let changes = match known {
                Some(changes) => changes,
                None => {
                    if fresh.is_none() {
                        *fresh = Some(self.salvage.salvage_all(sources.to_vec()));
                    }
                    let (built, _) = self.built(kind)?;
                    let changes = crate::reuse::Changes::between(
                        built.units().map(|(_, n, t)| (n, t)),
                        fresh.as_deref()?,
                        &name,
                        cut.start,
                    )
                    .map(Arc::new);
                    self.reused
                        .insert(0, ((key, cut.start), build, changes.clone()));
                    self.reused.truncate(REUSED);
                    changes
                }
            };
            let Some(changes) = changes else {
                continue;
            };
            let imports = match self.reused_imports.iter().find(|(b, _)| *b == build) {
                Some((_, imports)) => Arc::clone(imports),
                None => {
                    let (session, _) = self.built_mut(kind)?;
                    let imports = Arc::new(crate::reuse::Imports::of(session));
                    self.reused_imports.insert(0, (build, Arc::clone(&imports)));
                    self.reused_imports.truncate(Built::ALL.len());
                    imports
                }
            };
            let mut library_units = self.library_units.take();
            let answer = self.built_mut(kind).and_then(|(session, _)| {
                let unit = Self::unit_of_static(uri, session)?;
                let mut at = Read {
                    session,
                    unit,
                    at: changes.at,
                    needs: crate::reuse::Needs::default(),
                    library_units: &mut library_units,
                    build,
                };
                let answer = read(&mut at);
                let Read { session, needs, .. } = at;
                answer.filter(|_| changes.allow(session, &needs, &imports))
            });
            self.library_units = library_units;
            if answer.is_some() {
                #[cfg(test)]
                REUSED_ANSWERS.with(|n| n.set(n.get() + 1));
                return answer;
            }
        }
        None
    }

    /// The completion tier's session: [`Self::assemble_sources`] with
    /// `cut` (the statement being typed, in `uri`; see
    /// [`crate::salvage::typed_statement_cut`]) removed outright —
    /// a mid-statement cursor nearly always means a parse error, which
    /// sessions refuse, and the statement itself contributes nothing a
    /// member listing needs. The reduced text is identical for every
    /// keystroke inside the statement, so the cache (keyed by a hash
    /// of the reduced sources) rebuilds only when something *outside*
    /// the statement changes. Syntax errors elsewhere — in this document
    /// or any other unit — are salvaged around
    /// ([`Self::build_tolerant_session`]), which moves no offset.
    /// Position queries against this session must use offsets at or
    /// before `cut.start` — later spans shifted. A document that cannot
    /// be salvaged is not in the session at all. A build that fails —
    /// the library's, above all — is not tried again until the sources
    /// change: every keystroke would parse them all again for nothing.
    fn completion_session(
        &mut self,
        docs: &BTreeMap<Uri, Document>,
        uri: &Uri,
        cut: Span,
    ) -> Option<&mut Session> {
        let (sources, key) = self.cut_sources(docs, uri, cut);
        if self.completion_session.as_ref().map(|(k, _)| *k) != Some(key) {
            if self.completion_failed == Some(key) {
                return None;
            }
            let Some(session) = self.build_tolerant_session(sources.clone()) else {
                self.completion_failed = Some(key);
                return None;
            };
            self.completion_session = Some((key, session));
            self.completion_sources = sources;
            self.builds += 1;
            self.completion_build = self.builds;
            self.library_units = None;
        }
        self.completion_session.as_mut().map(|(_, s)| s)
    }

    /// The sources a session for a statement in `uri` reads — every
    /// unit, with `cut` taken out of `uri`'s text outright (see
    /// [`Self::completion_session`]) — and the key they are kept under.
    fn cut_sources(
        &mut self,
        docs: &BTreeMap<Uri, Document>,
        uri: &Uri,
        cut: Span,
    ) -> (Vec<(String, String)>, u64) {
        use std::hash::{Hash, Hasher};
        let mut fp: Vec<(String, i32)> = docs
            .iter()
            .map(|(u, d)| (u.to_string(), d.version))
            .collect();
        fp.sort();
        let mut sources = self.assemble_sources(docs, &fp);
        let name = uri.to_string();
        let mut hasher = std::collections::hash_map::DefaultHasher::new();
        for (n, text) in &mut sources {
            if *n == name {
                let (start, end) = (cut.start as usize, cut.end as usize);
                if start <= end && end <= text.len() {
                    let mut reduced = String::with_capacity(text.len() - (end - start));
                    reduced.push_str(&text[..start]);
                    reduced.push_str(&text[end..]);
                    *text = reduced;
                }
            }
            n.hash(&mut hasher);
            text.hash(&mut hasher);
        }
        (sources, hasher.finish())
    }

    /// The element under `offset` in `uri`: a reference site's target
    /// (narrowest name-span match, so a qualifier segment hits the
    /// qualifier's own target) or a declared name.
    fn element_at(
        session: &mut Session,
        unit: usize,
        offset: u32,
    ) -> Option<(ElementRef, Option<RefSite>)> {
        let resolved = session.resolved();
        let site = resolved
            .reference_sites()
            .iter()
            .filter(|s| s.unit == unit && s.name_span.start <= offset && offset < s.name_span.end)
            .min_by_key(|s| s.name_span.len())
            .cloned();
        if let Some(site) = site {
            return Some((site.target, Some(site)));
        }
        resolved.declaration_at(unit, offset).map(|e| (e, None))
    }

    /// definition: the declared-name location of whatever is under the
    /// cursor.
    pub fn definition(
        &mut self,
        docs: &BTreeMap<Uri, Document>,
        uri: &Uri,
        offset: u32,
        enc: Encoding,
    ) -> Option<Location> {
        let read = self.read_session(docs)?;
        let unit = Self::unit_of_static(uri, read.session)?;
        let (target, _) = Self::element_at(read.session, unit, offset)?;
        let (dunit, dspan) = read.session.resolved().declaration_site(target)?;
        read.location(dunit, dspan, enc)
    }

    /// document highlights: where the element under the cursor is
    /// declared and referenced in `uri` — off the read-only session, so
    /// they hold while a unit does not parse (see [`Self::read_session`]).
    pub fn highlights(
        &mut self,
        docs: &BTreeMap<Uri, Document>,
        uri: &Uri,
        offset: u32,
        enc: Encoding,
    ) -> Option<Vec<lsp_types::DocumentHighlight>> {
        let read = self.read_session(docs)?;
        let unit = Self::unit_of_static(uri, read.session)?;
        let (target, _) = Self::element_at(read.session, unit, offset)?;
        let resolved = read.session.resolved();
        let spans: Vec<Span> = resolved
            .declaration_site(target)
            .filter(|(u, _)| *u == unit)
            .map(|(_, span)| span)
            .into_iter()
            .chain(
                resolved
                    .references_to(target)
                    .into_iter()
                    .filter(|s| s.unit == unit)
                    .map(|s| s.name_span),
            )
            .collect();
        let locations = spans
            .into_iter()
            .filter_map(|span| read.location(unit, span, enc))
            .collect();
        Some(highlights_in(locations, uri))
    }

    /// references (find-usages): every site resolving to the element
    /// under the cursor, optionally plus its declaration.
    pub fn references(
        &mut self,
        docs: &BTreeMap<Uri, Document>,
        uri: &Uri,
        offset: u32,
        include_declaration: bool,
        enc: Encoding,
    ) -> Option<Vec<Location>> {
        let session = self.session(docs)?;
        let unit = Self::unit_of_static(uri, session)?;
        let (target, _) = Self::element_at(session, unit, offset)?;
        let sites = session.resolved().references_to(target);
        let mut out = Vec::new();
        if include_declaration {
            if let Some((dunit, dspan)) = session.resolved().declaration_site(target) {
                out.extend(Self::location_static(session, dunit, dspan, enc));
            }
        }
        for s in sites {
            out.extend(Self::location_static(session, s.unit, s.name_span, enc));
        }
        Some(out)
    }

    /// The hovered reference as a chain member: when the site under
    /// the cursor is a `member` of a chain step (`receiver.member`),
    /// the chain up to and including that member evaluates with each
    /// receiver as featuring context — `tankMass` in
    /// `oxidizerTank.tankMass` is *oxidizerTank's* tank mass, not the
    /// declaration's own-scope value (usually indeterminate for a
    /// definition member). `None` when the site is not a chain member,
    /// the chain is not rooted in a plain resolved reference, or
    /// evaluation fails — callers fall back to the declaration value.
    fn chain_site_value(
        session: &mut Session,
        kerml: bool,
        doc_text: &str,
        site: &RefSite,
    ) -> Option<sysmlv2_parser::eval::Value> {
        use sysmlv2_parser::ast::{Expr, ExprKind, QualifiedName, TargetRef};
        let parse = if kerml {
            sysmlv2_parser::parser::parse_kerml_source(doc_text)
        } else {
            sysmlv2_parser::parser::parse_source(doc_text)
        };
        // The chain step whose member (or member-chain link) is the
        // hovered span, with the links up to and including it. Spans
        // agree with the reference-site table because the session
        // parsed this same overlaid text.
        struct Finder<'a> {
            span: Span,
            hit: Option<(&'a Expr, Vec<&'a QualifiedName>)>,
        }
        impl<'a> sysmlv2_parser::visit::Visit<'a> for Finder<'a> {
            fn visit_expr(&mut self, n: &'a Expr) {
                if self.hit.is_none() {
                    if let ExprKind::ChainStep { member, .. } = &n.kind {
                        let links: Vec<&'a QualifiedName> = match member {
                            TargetRef::Name(qn) => vec![qn],
                            TargetRef::Chain(ls) => ls.iter().collect(),
                        };
                        let hovered = |qn: &QualifiedName| {
                            qn.segments.last().is_some_and(|s| s.span == self.span)
                        };
                        if let Some(i) = links.iter().position(|qn| hovered(qn)) {
                            self.hit = Some((n, links[..=i].to_vec()));
                        }
                    }
                }
                sysmlv2_parser::visit::walk_expr(self, n);
            }
        }
        let mut f = Finder {
            span: site.name_span,
            hit: None,
        };
        f.visit_unit(&parse.unit);
        let (step, tail) = f.hit?;
        // Decompose the receiver side down to a plain reference root;
        // other shapes (invocations, indexed steps) fall back.
        let mut members: Vec<&QualifiedName> = Vec::new();
        let ExprKind::ChainStep { target, .. } = &step.kind else {
            return None;
        };
        let mut cur: &Expr = target;
        let root = loop {
            match &cur.kind {
                ExprKind::ChainStep { target, member } => {
                    match member {
                        TargetRef::Name(qn) => members.push(qn),
                        TargetRef::Chain(ls) => members.extend(ls.iter().rev()),
                    }
                    cur = target;
                }
                ExprKind::Ref(qn) => break qn,
                _ => return None,
            }
        };
        members.reverse();
        members.extend(tail);
        // The root element, through its recorded reference site — the
        // site's resolution scope, not a root-namespace lookup.
        let root_span = root.segments.last()?.span;
        let root_elem = session
            .resolved()
            .reference_sites()
            .iter()
            .find(|s| s.unit == site.unit && s.name_span == root_span)
            .map(|s| s.target)?;
        session.resolved().evaluate_chain(root_elem, &members).ok()
    }

    /// hover: qualified name + metaclass (and declared detail later).
    pub fn hover(
        &mut self,
        docs: &BTreeMap<Uri, Document>,
        uri: &Uri,
        offset: u32,
        enc: Encoding,
    ) -> Option<(String, Range)> {
        let read = self.read_session(docs)?;
        let session = &mut *read.session;
        let unit = Self::unit_of_static(uri, session)?;
        let (target, site) = Self::element_at(session, unit, offset)?;
        let resolved = session.resolved();
        let metaclass = resolved.element_type(target);
        let qn = resolved
            .element_qualified_name(target)
            .unwrap_or_else(|| "<anonymous>".to_string());
        // Anything an invocation expression can call — calc/constraint/
        // action defs and usages, KerML functions/predicates/behaviors —
        // reads as a function at its call sites, so those cards lead
        // with a signature the way a function hover does: a fenced
        // block (editor font), parameter names with their types (`in`
        // implied, `out`/`inout` spelled), and the return type after
        // `→`. Types render as the declaration spells them (a subsetted
        // feature standing in for a type not written: `in a :> isp`),
        // so the reader sees the author's qualification; parameters
        // inherited come after the callable's own (see
        // [`crate::receiver::parameters`]); a library callable's types,
        // whose text the session does not carry, are spelled from the
        // model the shortest way that resolves here (see [`SigTypes`]).
        // The fence is tagged `sysml-signature` — the notation is not
        // SysML source, so clients colorize it with a dedicated
        // signature grammar (plain monospace where none is registered).
        let at = SigAt::in_unit(resolved, unit, offset, crate::dialect_of(uri));
        let parts = def_signature(resolved, target, metaclass, &at);
        // Slicing the spelled types needs the unit texts — the resolved
        // borrow ends here and is re-acquired after.
        let sig = parts.map(|p| render_signature(p, session));
        let doc_text = docs.get(uri).map(|d| d.text.clone());
        let site_value = match (&site, &doc_text) {
            (Some(s), Some(t)) => {
                Self::chain_site_value(session, crate::is_kerml(uri.path().as_str()), t, s)
            }
            _ => None,
        };
        let resolved = session.resolved();
        let text = match sig {
            Some(sig) => format!("```sysml-signature\n{sig}\n```\n**{qn}**  \n`{metaclass}`"),
            None => format!("**{qn}**  \n`{metaclass}`"),
        };
        // The resolved value at the site (the value-inlay tier's
        // evaluator, now on hover): shown when evaluation settles it to
        // a plain value or a *named* element (enum literal, referenced
        // usage) — the element itself is the unbound case and says
        // nothing. A chain-member site prefers the chain's value — the
        // receiver establishes the featuring context, so the card
        // answers for the instance the cursor is on, not the
        // declaration in general.
        let value = match site_value {
            Some(v) => Ok(v),
            None => resolved.evaluate(target),
        };
        let text = match value {
            Ok(sysmlv2_parser::eval::Value::Element(t)) if t != target => {
                match resolved.element_name(t) {
                    Some(name) => format!("{text}  \n= `{name}`"),
                    None => text,
                }
            }
            Ok(
                sysmlv2_parser::eval::Value::Element(_)
                | sysmlv2_parser::eval::Value::Unbound(_)
                | sysmlv2_parser::eval::Value::UnboundMember(_),
            )
            | Err(_) => text,
            Ok(v) => format!("{text}  \n= `{}`", resolved.render_value_approx(&v)),
        };
        // Documentation bodies annotating the element join the card
        // under a rule, block-comment `*` gutters stripped. A named doc
        // (`doc Description /* … */`) renders its name as a heading.
        let bodies: Vec<String> = resolved
            .annotation_docs()
            .into_iter()
            .filter(|(e, _, _)| *e == target)
            .map(|(_, name, b)| {
                let body = doc_markdown(&b);
                match name {
                    Some(name) if !body.is_empty() => format!("### {name}\n{body}"),
                    _ => body,
                }
            })
            .filter(|b| !b.is_empty())
            .collect();
        // Inherited documentation: a bare usage (a metadata record's
        // `rowDigest = …`, a nested source entry) usually carries no
        // doc of its own — the vocabulary's documentation lives on the
        // defining attribute. Fall back to the same-named member of
        // the owner's typing, then to the element's own typings, each
        // attributed so the reader knows where the words come from.
        let bodies = if bodies.is_empty() {
            let mut inherited: Vec<String> = Vec::new();
            // Per-element doc lookup rather than the user-unit doc
            // sweep: the vocabulary being inherited from typically
            // lives in the library tier (a standard-library package),
            // which `annotation_docs` deliberately excludes.
            let docs_of = |resolved: &mut sysmlv2_parser::json::ResolvedModel,
                           e: ElementRef|
             -> Vec<String> {
                let qn = resolved.element_qualified_name(e);
                resolved
                    .element_docs(e)
                    .into_iter()
                    .map(|(_, b)| doc_markdown(&b))
                    .filter(|b| !b.is_empty())
                    .map(|b| match &qn {
                        Some(qn) => format!("{b}\n\n*(from `{qn}`)*"),
                        None => b,
                    })
                    .collect()
            };
            if let (Some(name), Some(owner)) = (
                resolved.element_name(target).map(str::to_string),
                resolved.owner(target),
            ) {
                // The counterpart lives among the typing's *effective*
                // features (owned + inherited): the vocabulary attribute
                // may itself be inherited within the library hierarchy.
                'outer: for ty in resolved.typings(owner) {
                    for member in resolved.effective_features(ty, true) {
                        if resolved.element_name(member) == Some(name.as_str()) {
                            inherited = docs_of(resolved, member);
                            if !inherited.is_empty() {
                                break 'outer;
                            }
                        }
                    }
                }
            }
            if inherited.is_empty() {
                for ty in resolved.typings(target) {
                    inherited = docs_of(resolved, ty);
                    if !inherited.is_empty() {
                        break;
                    }
                }
            }
            inherited
        } else {
            bodies
        };
        let text = if bodies.is_empty() {
            text
        } else {
            format!("{text}\n\n---\n{}", bodies.join("\n\n"))
        };
        let span = site.map(|s| s.name_span).or_else(|| {
            resolved
                .declaration_site(target)
                .filter(|(u, _)| *u == unit)
                .map(|(_, s)| s)
        })?;
        let range = ReadSession {
            session,
            written: read.written,
        }
        .location(unit, span, enc)?
        .range;
        Some((text, range))
    }

    /// The signature of what `callee` — a name, or a feature chain's
    /// step on its receiver (`vehicle.ke`) — invoked in the statement
    /// being typed (`cut`, see [`crate::salvage::typed_statement_cut`])
    /// in `uri`, calls — the hover card's signature line, with where each
    /// parameter sits in it — and the callable's documentation, else
    /// the nearest its written heritage carries (see
    /// [`crate::receiver::nearest_in_heritage`]). The callee resolves as
    /// the evaluator resolves an invocation's target (see
    /// [`crate::receiver::receiver_element`]), in a model with the
    /// statement cut out (see [`Self::cut_answer`]); its parameters
    /// include those it inherits (`calc c : F;`, `calc def G :> F;`, see
    /// [`crate::receiver::parameters`]), and a feature typed by a
    /// function answers with the function's, under its own name. `None`
    /// when the callee does not resolve, or not to something an
    /// invocation can call.
    pub(crate) fn invocation_signature(
        &mut self,
        docs: &BTreeMap<Uri, Document>,
        uri: &Uri,
        cut: Span,
        callee: &sysmlv2_parser::ast::Expr,
    ) -> Option<(SignatureLine, Option<String>)> {
        self.cut_answer(docs, uri, cut, |at| {
            let resolved = at.session.resolved();
            let enclosing = crate::receiver::enclosing_declarations(resolved, at.unit, at.at);
            at.needs.scopes(&enclosing);
            at.needs.expr(callee);
            let mut reached = Vec::new();
            let target =
                crate::receiver::receiver_reached(resolved, &enclosing, callee, &mut reached)?;
            reached.into_iter().for_each(|e| at.needs.read(e));
            let sig_at = SigAt::in_unit(resolved, at.unit, at.at, crate::dialect_of(uri));
            let (source, mut parts) = std::iter::once(target)
                .chain(resolved.typings(target))
                .find_map(|e| {
                    def_signature(resolved, e, resolved.element_type(e), &sig_at).map(|p| (e, p))
                })?;
            at.needs.read(source);
            // A type spelled from the model is spelled the shortest way
            // that resolves where the signature is read: by the names of
            // its owners, or under `ISQ` — the types of the parameters
            // shown, inherited ones included (declared in the general
            // types read with the source), and of the result, each with
            // what it redefines: one redefining without a type is spelled
            // with the type of what it redefines (see [`spelled_types`]).
            at.needs.name("ISQ");
            let parameters: Vec<ElementRef> = crate::receiver::parameters(resolved, source)
                .into_iter()
                .map(|(p, _)| p)
                .chain(crate::receiver::result_parameter(resolved, source))
                .collect();
            let mut seen = std::collections::HashSet::new();
            let mut chain = parameters;
            while let Some(p) = chain.pop() {
                if !seen.insert(p) {
                    continue;
                }
                chain.extend(resolved.redefinition_targets(p));
                for t in resolved.explicit_supertypes(p) {
                    let mut owner = Some(t);
                    while let Some(e) = owner {
                        if let Some(name) = resolved.element_name(e) {
                            at.needs.name(name);
                        }
                        owner = resolved.owner(e);
                    }
                }
            }
            if source != target {
                if let Some(own) = crate::receiver::feature_name(resolved, target) {
                    parts.name = own;
                }
            }
            let doc = crate::receiver::nearest_in_heritage(resolved, target, |resolved, e| {
                let bodies: Vec<String> = resolved
                    .element_docs(e)
                    .into_iter()
                    .map(|(_, b)| doc_markdown(&b))
                    .filter(|b| !b.is_empty())
                    .collect();
                (!bodies.is_empty()).then(|| bodies.join("\n\n"))
            });
            Some((signature_line(parts, at.session), doc))
        })
    }

    /// rename: through the Session edit engine (declaration + every
    /// reference site, cross-file, semantic-identity checked). Returns
    /// whole-document edits for every unit whose text changed.
    /// On success the cached session has advanced past the client's
    /// documents — the caller must `invalidate()`.
    pub fn rename(
        &mut self,
        docs: &BTreeMap<Uri, Document>,
        uri: &Uri,
        offset: u32,
        new_name: &str,
        enc: Encoding,
    ) -> Result<WorkspaceEdit, String> {
        if new_name.trim().is_empty() {
            return Err("the new name is empty".to_string());
        }
        let session = self
            .session(docs)
            .ok_or_else(|| "no model for the open documents".to_string())?;
        let unit = Self::unit_of_static(uri, session).ok_or("document is not open")?;
        let (target, _) =
            Self::element_at(session, unit, offset).ok_or("nothing renameable under the cursor")?;
        if session.resolved().declaration_site(target).is_none() {
            return Err("the target has no renameable declaration".to_string());
        }
        let before: Vec<(String, String)> = session
            .units()
            .map(|(_, n, s)| (n.to_string(), s.to_string()))
            .collect();
        let mut edit = session.edit();
        edit.rename(target, new_name);
        edit.commit().map_err(|e| e.to_string())?;
        let mut changes = HashMap::new();
        for ((name, old), (_, _, new)) in before.iter().zip(session.units()) {
            if old != new {
                let mapper = Mapper::new(old, enc);
                changes.insert(
                    Uri::from_str(name).map_err(|e| e.to_string())?,
                    vec![TextEdit {
                        range: mapper.full_range(),
                        new_text: new.to_string(),
                    }],
                );
            }
        }
        Ok(WorkspaceEdit {
            changes: Some(changes),
            ..Default::default()
        })
    }

    /// Collapse every qualified reference to its minimal spelling
    /// (per-site shortest suffix, reparse-verified with
    /// per-candidate revert). Returns whole-document edits for changed
    /// units; the caller must `invalidate()` afterward — the session
    /// advanced past the client's documents.
    pub fn minimize(
        &mut self,
        docs: &BTreeMap<Uri, Document>,
        enc: Encoding,
    ) -> Result<WorkspaceEdit, String> {
        let session = self
            .session(docs)
            .ok_or_else(|| "no model for the open documents".to_string())?;
        let before: Vec<(String, String)> = session
            .units()
            .map(|(_, n, s)| (n.to_string(), s.to_string()))
            .collect();
        session
            .minimize_qualifications()
            .map_err(|e| e.to_string())?;
        let mut changes = HashMap::new();
        for ((name, old), (_, _, new)) in before.iter().zip(session.units()) {
            if old != new {
                let mapper = Mapper::new(old, enc);
                changes.insert(
                    Uri::from_str(name).map_err(|e| e.to_string())?,
                    vec![TextEdit {
                        range: mapper.full_range(),
                        new_text: new.to_string(),
                    }],
                );
            }
        }
        Ok(WorkspaceEdit {
            changes: Some(changes),
            ..Default::default()
        })
    }

    /// "Split into files": offered when the cursor sits on the name of a
    /// package that owns nested packages. One action per file-naming
    /// scheme whose names differ. The edit creates the new units and
    /// rewrites the root, every change under one annotation naming the
    /// split (a client's refactor preview lists the files by it).
    pub fn split_actions(
        &mut self,
        docs: &BTreeMap<Uri, Document>,
        uri: &Uri,
        offset: u32,
        enc: Encoding,
    ) -> Vec<(String, WorkspaceEdit)> {
        let Some(session) = self.session(docs) else {
            return Vec::new();
        };
        let Some(unit) = Self::unit_of_static(uri, session) else {
            return Vec::new();
        };
        let Some(package) = session.resolved().declaration_at(unit, offset) else {
            return Vec::new();
        };
        if session.resolved().element_type(package) != "Package" {
            return Vec::new();
        }
        let Some(name) = session.resolved().element_name(package).map(str::to_string) else {
            return Vec::new();
        };
        if let Some((fp, cached_package, actions)) = &self.split_cache {
            if *fp == self.fingerprint && *cached_package == package {
                return actions.clone();
            }
        }
        let session = self.session.as_mut().expect("session built above");
        let mut out = Vec::new();
        let mut seen_trees: Vec<Vec<String>> = Vec::new();
        for naming in [
            sysmlv2_transform::SplitNaming::Keep,
            sysmlv2_transform::SplitNaming::Slug,
        ] {
            let options = sysmlv2_transform::SplitOptions {
                naming,
                directory: None,
                uri_units: true,
            };
            let Ok(plan) = session.split_plan(package, &options) else {
                continue;
            };
            let tree: Vec<String> = plan.entries.iter().map(|e| e.unit.clone()).collect();
            if seen_trees.contains(&tree) {
                continue;
            }
            seen_trees.push(tree.clone());
            let mut edit = session.edit();
            edit.split(&plan);
            let Ok(report) = edit.check() else {
                continue;
            };
            let Some(workspace_edit) = Self::annotated_edit(session, &plan, &report.splices, enc)
            else {
                continue;
            };
            let scheme = match naming {
                sysmlv2_transform::SplitNaming::Keep => "",
                sysmlv2_transform::SplitNaming::Slug => " (slugged file names)",
            };
            let n = plan.entries.len();
            out.push((
                format!(
                    "Split '{name}' into {n} file{} under {}/{scheme}",
                    if n == 1 { "" } else { "s" },
                    plan.directory.rsplit('/').next().unwrap_or(&plan.directory)
                ),
                workspace_edit,
            ));
        }
        self.split_cache = Some((self.fingerprint.clone(), package, out.clone()));
        out
    }

    /// The split behind an editor's wizard (`sysmlv2/splitPlan`,
    /// `sysmlv2/split`): the plan for one package under one naming
    /// scheme and directory, with the annotated workspace edit when
    /// `with_edit` (a whole-workspace dry run — the plan alone is
    /// cheap, so a wizard previews both naming schemes and asks for the
    /// edit once). The package is the declaration under a cursor
    /// offset or a qualified name resolved from the root namespace, so
    /// a deeper level can be requested by the name a hoisted package
    /// takes in its new unit. Unit names are uris here, so the
    /// options' `uri_units` is forced on. Refusals name their reason.
    pub fn split_request(
        &mut self,
        docs: &BTreeMap<Uri, Document>,
        target: &SplitTarget,
        options: sysmlv2_transform::SplitOptions,
        with_edit: bool,
        enc: Encoding,
    ) -> Result<SplitResponse, String> {
        let session = self
            .session(docs)
            .ok_or_else(|| "the model could not be built".to_string())?;
        let package = match target {
            SplitTarget::Offset { uri, offset } => {
                let unit = Self::unit_of_static(uri, session)
                    .ok_or_else(|| format!("{} is not a model unit", uri.as_str()))?;
                session
                    .resolved()
                    .declaration_at(unit, *offset)
                    .ok_or_else(|| "the position is not on a declaration's name".to_string())?
            }
            SplitTarget::Package(name) => session
                .resolved()
                .resolve_qualified(name)
                .ok_or_else(|| format!("cannot resolve `{name}`"))?,
        };
        let options = sysmlv2_transform::SplitOptions {
            uri_units: true,
            ..options
        };
        // The plan judges eligibility (a package, something nested).
        let plan = session
            .split_plan(package, &options)
            .map_err(|e| e.to_string())?;
        let edit = if with_edit {
            let mut edit = session.edit();
            edit.split(&plan);
            let report = edit.check().map_err(|e| e.to_string())?;
            Some(
                Self::annotated_edit(session, &plan, &report.splices, enc)
                    .ok_or_else(|| "the new units' names do not spell URIs".to_string())?,
            )
        } else {
            None
        };
        let resolved = session.resolved();
        let nested_packages = |e: ElementRef| {
            resolved
                .owned_members(e)
                .into_iter()
                .filter(|&m| {
                    resolved.element_type(m) == "Package" && resolved.element_name(m).is_some()
                })
                .count()
        };
        let entries = plan
            .entries
            .iter()
            .map(|e| SplitResponseEntry {
                qualified_name: e.qualified.clone(),
                name: e.name.clone(),
                new_name: e.new_name.clone(),
                root_name: sysmlv2_transform::spell_name(e.new_name.as_deref().unwrap_or(&e.name)),
                uri: e.unit.clone(),
                bytes: e.bytes,
                nested: nested_packages(e.package),
            })
            .collect();
        let name = resolved
            .element_name(plan.root)
            .unwrap_or_default()
            .to_string();
        let qualified_name = resolved
            .element_qualified_name(plan.root)
            .unwrap_or_else(|| name.clone());
        Ok(SplitResponse {
            root: SplitResponseRoot {
                name,
                qualified_name,
                uri: plan.root_unit.clone(),
            },
            directory: plan.directory,
            entries,
            edit,
        })
    }

    /// A split's splices as one annotated workspace edit: a create
    /// operation plus the full text for every new unit, ranged edits for
    /// the existing ones, all under one change annotation that names
    /// the split and its files in a client's refactor preview. The
    /// annotation does not ask for confirmation: editors take that flag
    /// as "opt in to each change" and open their preview with every
    /// change unticked, while a split is one whole.
    fn annotated_edit(
        session: &Session,
        plan: &sysmlv2_transform::SplitPlan,
        splices: &[sysmlv2_transform::AppliedSplice],
        enc: Encoding,
    ) -> Option<WorkspaceEdit> {
        const ANNOTATION: &str = "split";
        let mut ops: Vec<lsp_types::DocumentChangeOperation> = Vec::new();
        for entry in &plan.entries {
            let uri = Uri::from_str(&entry.unit).ok()?;
            ops.push(lsp_types::DocumentChangeOperation::Op(
                lsp_types::ResourceOp::Create(lsp_types::CreateFile {
                    uri: uri.clone(),
                    options: None,
                    annotation_id: Some(ANNOTATION.to_string()),
                }),
            ));
            let text: String = splices
                .iter()
                .filter(|s| s.unit == entry.unit)
                .map(|s| s.text.as_str())
                .collect();
            ops.push(lsp_types::DocumentChangeOperation::Edit(
                lsp_types::TextDocumentEdit {
                    text_document: lsp_types::OptionalVersionedTextDocumentIdentifier {
                        uri,
                        version: None,
                    },
                    edits: vec![lsp_types::OneOf::Right(lsp_types::AnnotatedTextEdit {
                        text_edit: TextEdit {
                            range: lsp_types::Range::default(),
                            new_text: text,
                        },
                        annotation_id: ANNOTATION.to_string(),
                    })],
                },
            ));
        }
        for (_, unit_name, text) in session.units() {
            let mut edits: Vec<lsp_types::OneOf<TextEdit, lsp_types::AnnotatedTextEdit>> =
                Vec::new();
            let mapper = Mapper::new(text, enc);
            let mut unit_splices: Vec<&sysmlv2_transform::AppliedSplice> =
                splices.iter().filter(|s| s.unit == unit_name).collect();
            unit_splices.sort_by_key(|s| (s.start, s.end));
            for s in unit_splices {
                edits.push(lsp_types::OneOf::Right(lsp_types::AnnotatedTextEdit {
                    text_edit: TextEdit {
                        range: mapper.range(Span::new(s.start, s.end)),
                        new_text: s.text.clone(),
                    },
                    annotation_id: ANNOTATION.to_string(),
                }));
            }
            if edits.is_empty() {
                continue;
            }
            ops.push(lsp_types::DocumentChangeOperation::Edit(
                lsp_types::TextDocumentEdit {
                    text_document: lsp_types::OptionalVersionedTextDocumentIdentifier {
                        uri: Uri::from_str(unit_name).ok()?,
                        version: None,
                    },
                    edits,
                },
            ));
        }
        let files: Vec<&str> = plan.entries.iter().map(|e| e.unit.as_str()).collect();
        let mut annotations = HashMap::new();
        annotations.insert(
            ANNOTATION.to_string(),
            lsp_types::ChangeAnnotation {
                label: format!("Split into {} new file(s)", plan.entries.len()),
                needs_confirmation: None,
                description: Some(files.join("\n")),
            },
        );
        Some(WorkspaceEdit {
            changes: None,
            document_changes: Some(lsp_types::DocumentChanges::Operations(ops)),
            change_annotations: Some(annotations),
        })
    }

    /// The lint findings of `uri`'s unit that carry a fix, with every fix
    /// rendered as a workspace edit over the session's texts. The pass
    /// runs once per session build and `sysmlint.json` text (read from
    /// the workspace root, as the push tier does).
    pub fn lint_fixes(
        &mut self,
        docs: &BTreeMap<Uri, Document>,
        uri: &Uri,
        enc: Encoding,
    ) -> Vec<LintFixSet> {
        let Some(unit) = self.lint_unit(docs, uri) else {
            return Vec::new();
        };
        self.lint_fix_sets(enc, |f| f.unit == Some(unit))
    }

    /// Every finding of `rule` across the workspace that carries a fix,
    /// as fix sets — the requesting document's among them. Behind the
    /// "fix every finding of this rule" actions.
    pub fn lint_rule_fixes(
        &mut self,
        docs: &BTreeMap<Uri, Document>,
        uri: &Uri,
        enc: Encoding,
        rule: &str,
    ) -> Vec<LintFixSet> {
        if self.lint_unit(docs, uri).is_none() {
            return Vec::new();
        }
        self.lint_fix_sets(enc, |f| f.rule == rule)
    }

    /// Builds the session and caches the lint pass (per session build and
    /// config text); the unit `uri` names, when the session holds it.
    fn lint_unit(&mut self, docs: &BTreeMap<Uri, Document>, uri: &Uri) -> Option<usize> {
        let generation = self.config.get().0;
        self.session(docs)?;
        let cached = self
            .lint
            .as_ref()
            .filter(|(g, _)| *g == generation)
            .is_some();
        if !cached {
            let config = self.config.get().1;
            let session = self.session.as_mut().expect("session built above");
            let texts: Vec<(usize, String)> = session
                .units()
                .map(|(i, _, t)| (i, t.to_string()))
                .collect();
            let sources: Vec<(usize, &str)> = texts.iter().map(|(i, t)| (*i, t.as_str())).collect();
            let findings = sysmlv2_lint::lint_with_sources(session.resolved(), config, &sources);
            self.lint = Some((generation, findings));
        }
        let session: &Session = self.session.as_ref().expect("session built above");
        Self::unit_of_static(uri, session)
    }

    /// The cached findings `keep` admits, as fix sets (findings without a
    /// fix, or whose fix names a unit the session does not hold, drop).
    fn lint_fix_sets(
        &self,
        enc: Encoding,
        keep: impl Fn(&sysmlv2_lint::Finding) -> bool,
    ) -> Vec<LintFixSet> {
        let session: &Session = self.session.as_ref().expect("session built above");
        let findings = &self.lint.as_ref().expect("lint pass cached above").1;
        // One line index per unit for every edit of every fix (see
        // `UnitMappers`).
        let mut mappers = UnitMappers::new(enc);
        findings
            .iter()
            .filter(|f| keep(f))
            .filter_map(|f| {
                let fix = f.fix.as_ref()?;
                let (unit, span) = (f.unit?, f.span?);
                let edit = Self::fix_edit(session, fix, &mut mappers)?;
                let alternatives = f
                    .alternatives
                    .iter()
                    .filter_map(|a| {
                        Self::fix_edit(session, a, &mut mappers)
                            .map(|e| (a.label.clone(), a.semantic, e))
                    })
                    .collect();
                let range = mappers.get(unit, || unit_of(session, unit))?.1.range(span);
                Some(LintFixSet {
                    rule: f.rule.id(),
                    range,
                    label: fix.label.clone(),
                    semantic: fix.semantic,
                    deletes: fix.deletes,
                    edit,
                    alternatives,
                })
            })
            .collect()
    }

    /// A lint fix's byte-offset edits over session units as a workspace
    /// edit; `None` when an edit names a unit the session does not hold.
    /// `mappers` memoizes each unit's name and line index across calls.
    fn fix_edit<'s>(
        session: &'s Session,
        fix: &sysmlv2_lint::Fix,
        mappers: &mut UnitMappers<'s, usize>,
    ) -> Option<WorkspaceEdit> {
        let mut changes: HashMap<Uri, Vec<TextEdit>> = HashMap::new();
        for e in &fix.edits {
            let (name, mapper) = mappers.get(e.unit, || unit_of(session, e.unit))?;
            changes
                .entry(Uri::from_str(name).ok()?)
                .or_default()
                .push(TextEdit {
                    range: mapper.range(e.span),
                    new_text: e.replacement.clone(),
                });
        }
        Some(WorkspaceEdit {
            changes: Some(changes),
            ..Default::default()
        })
    }

    /// Visibility advice for the import declared at `offset` in `uri`,
    /// from the workspace model (see
    /// `ResolvedModel::import_visibility_advice`).
    pub fn import_visibility_advice(
        &mut self,
        docs: &BTreeMap<Uri, Document>,
        uri: &Uri,
        offset: u32,
    ) -> Option<sysmlv2_parser::json::ImportVisibilityAdvice> {
        let session = self.session(docs)?;
        let unit = Self::unit_of_static(uri, session)?;
        let resolved = session.resolved();
        let (import, _, _) = resolved
            .imports_without_visibility()
            .into_iter()
            .find(|(_, u, span)| *u == unit && span.start <= offset && offset <= span.end)?;
        resolved.import_visibility_advice(import)
    }

    /// "Extract definition": offered when the cursor sits on the
    /// declaration of a usage the eligibility gate admits. The edit is a
    /// dry-run's splices as ranged edits (cross-file capable); the
    /// session is left untouched, so no invalidation is needed.
    pub fn refactor_extract_action(
        &mut self,
        docs: &BTreeMap<Uri, Document>,
        uri: &Uri,
        offset: u32,
        enc: Encoding,
    ) -> Option<(String, WorkspaceEdit)> {
        let session = self.session(docs)?;
        let unit = Self::unit_of_static(uri, session)?;
        let target = session.resolved().declaration_at(unit, offset)?;
        let elig = session.extract_definition_eligibility(target).ok()?;
        let name = sysmlv2_transform::synthesized_definition_name(
            session.resolved().element_name(target)?,
        );
        let spelled = sysmlv2_transform::spell_name(&name);
        let title = format!("Extract '{} def {spelled}'", elig.keyword);
        let mut edit = session.edit();
        edit.extract_definition(target, None);
        let report = edit.check().ok()?;
        let edit = Self::splice_edit(session, &report.splices, enc)?;
        Some((title, edit))
    }

    /// "Inline definition": offered when the cursor sits on a
    /// definition's declaration or on a reference to it (its sole
    /// usage's typing, most usefully) and the eligibility gate admits
    /// the inline. Same dry-run contract as extract.
    pub fn refactor_inline_action(
        &mut self,
        docs: &BTreeMap<Uri, Document>,
        uri: &Uri,
        offset: u32,
        enc: Encoding,
    ) -> Option<(String, WorkspaceEdit)> {
        let session = self.session(docs)?;
        let unit = Self::unit_of_static(uri, session)?;
        let (target, _) = Self::element_at(session, unit, offset)?;
        let metaclass = session.resolved().element_type(target);
        if !metaclass.ends_with("Definition") {
            return None;
        }
        let rule = sysmlv2_transform::eligibility::definition_kind_rule(metaclass)?;
        session.inline_definition_eligibility(target).ok()?;
        let name = session.resolved().element_name(target)?;
        let spelled = sysmlv2_transform::spell_name(name);
        let title = format!("Inline '{} def {spelled}'", rule.keyword);
        let mut edit = session.edit();
        edit.inline_definition(target);
        let report = edit.check().ok()?;
        let edit = Self::splice_edit(session, &report.splices, enc)?;
        Some((title, edit))
    }

    /// A dry-run's applied splices as an LSP `WorkspaceEdit`: ranged
    /// edits in pre-commit coordinates, grouped per unit — exactly the
    /// replacements the commit would make, cross-file included.
    fn splice_edit(
        session: &Session,
        splices: &[sysmlv2_transform::AppliedSplice],
        enc: Encoding,
    ) -> Option<WorkspaceEdit> {
        let mut changes: HashMap<Uri, Vec<TextEdit>> = HashMap::new();
        for sp in splices {
            let (_, _, text) = session.units().find(|(_, n, _)| *n == sp.unit)?;
            let mapper = Mapper::new(text, enc);
            changes
                .entry(Uri::from_str(&sp.unit).ok()?)
                .or_default()
                .push(TextEdit {
                    range: mapper.range(Span::new(sp.start, sp.end)),
                    new_text: sp.text.clone(),
                });
        }
        Some(WorkspaceEdit {
            changes: Some(changes),
            ..Default::default()
        })
    }

    /// Completion: the dialect-merged keyword vocabulary plus
    /// every name declared in the open documents, kinds mapped from the
    /// outline. Deliberately position-blind in this first cut — the
    /// body-context inversion of the validation matrix is the noted follow-up.
    /// The library's `(unit name, text)` sources.
    fn library_sources(lib: &Library) -> Vec<(String, String)> {
        match lib {
            Library::Prepared(library) => library
                .sources()
                .map(|(name, text)| (name.to_owned(), text.to_owned()))
                .collect(),
            Library::Sources { units, .. } => units.as_ref().clone(),
            Library::Dir(dir) => {
                fn walk(dir: &std::path::Path, out: &mut Vec<(String, String)>) {
                    let Ok(entries) = std::fs::read_dir(dir) else {
                        return;
                    };
                    for entry in entries.flatten() {
                        let path = entry.path();
                        if path.is_dir() {
                            walk(&path, out);
                        } else if matches!(
                            path.extension().and_then(|e| e.to_str()),
                            Some("sysml") | Some("kerml")
                        ) {
                            if let Ok(text) = std::fs::read_to_string(&path) {
                                out.push((path.display().to_string(), text));
                            }
                        }
                    }
                }
                let mut out = Vec::new();
                walk(dir, &mut out);
                out
            }
        }
    }

    /// The standard library's qualified symbols ([`Self::library_table_ref`]).
    fn library_symbols(&mut self) -> &[QualifiedSymbol] {
        self.library_table_ref().symbols()
    }

    /// The standard library's qualified symbol table, built once per Nav
    /// from a syntax-tier parse of the library texts. Model-free by
    /// design: structure is syntactic, and this must not add a
    /// per-keystroke model build.
    fn library_table_ref(&mut self) -> &SymbolTable {
        if self.library_symbols.is_none() {
            let mut symbols: Vec<QualifiedSymbol> = Vec::new();
            let mut links = Links::default();
            if let Some(lib) = &self.library {
                for (name, text) in Self::library_sources(lib) {
                    let kerml = crate::is_kerml(name.as_str());
                    collect_unit(&text, kerml, None, Encoding::Utf8, &mut symbols, &mut links);
                }
            }
            let table = SymbolTable::new(symbols, links, None);
            // The library's measurement-unit type, and the definitions
            // specializing it — aliases of them too, as the table takes
            // them.
            let root = table
                .symbols()
                .iter()
                .find(|s| {
                    s.qualified == "MeasurementReferences::MeasurementUnit"
                        && matches!(s.decl, crate::kinds::Decl::Definition(_))
                })
                .map(|s| s.name.as_str());
            self.library_unit_types = crate::kinds::unit_types(
                root,
                &std::collections::HashSet::new(),
                definitions(table.symbols()),
            );
            self.library_symbols = Some(Arc::new(table));
        }
        self.library_symbols.as_deref().expect("built above")
    }

    /// [`Self::library_symbols`]' table, shared.
    fn library_table(&mut self) -> Arc<SymbolTable> {
        self.library_table_ref();
        Arc::clone(
            self.library_symbols
                .as_ref()
                .expect("built by library_symbols"),
        )
    }

    /// Workspace symbols across BOTH tiers: fresh parses of the open
    /// documents, plus the cached seed scan for every seeded unit that
    /// is not open (an open document's live text shadows its seed
    /// copy). Everything that offers or auto-inserts an import must use
    /// this — the open-documents map alone hides most of the workspace.
    ///
    /// Layered for the request's document `uri`: that document's
    /// symbols, over the rest of the workspace, over the library. The
    /// rest is kept between requests while no other document changes,
    /// so typing in one document neither re-parses the others nor
    /// forgets what their namespaces make visible. A re-exporting import
    /// elsewhere that resolves only with `uri` taken into account has
    /// the whole workspace built as one layer instead.
    fn all_workspace_symbols(
        &mut self,
        docs: &BTreeMap<Uri, Document>,
        uri: &Uri,
        enc: Encoding,
    ) -> SymbolTable {
        let library = self.library_table();
        if self.workspace_seed_symbols.is_none() {
            if let Some(units) = &self.workspace {
                let mut seed: Vec<QualifiedSymbol> = Vec::new();
                let mut seed_links = Links::default();
                for (name, text) in units.iter() {
                    let kerml = crate::is_kerml(name);
                    collect_unit(text, kerml, Some(name), enc, &mut seed, &mut seed_links);
                }
                self.workspace_seed_symbols = Some((seed, seed_links));
            }
        }
        let current = uri.to_string();
        let key = RestKey {
            others: docs
                .iter()
                .map(|(u, d)| (u.to_string(), Arc::clone(&d.text)))
                .filter(|(u, _)| *u != current)
                .collect(),
            current,
        };
        let current = &key.current;
        let rest = match &self.workspace_rest {
            Some((known, rest)) if known.same(&key) => Arc::clone(rest),
            _ => {
                let (mut symbols, mut links) =
                    workspace_symbols(docs.iter().filter(|(u, _)| u.to_string() != *current), enc);
                if let Some((seed, seed_links)) = &self.workspace_seed_symbols {
                    let open: std::collections::HashSet<String> =
                        docs.keys().map(|u| u.to_string()).collect();
                    symbols.extend(
                        seed.iter()
                            .filter(|s| s.site.as_ref().is_none_or(|(u, _)| !open.contains(u)))
                            .cloned(),
                    );
                    links.imports.extend(
                        seed_links
                            .imports
                            .iter()
                            .filter(|i| i.unit.as_ref().is_none_or(|u| !open.contains(u)))
                            .cloned(),
                    );
                }
                let rest = Arc::new(SymbolTable::new(symbols, links, Some(Arc::clone(&library))));
                self.workspace_rest = Some((key, Arc::clone(&rest)));
                rest
            }
        };
        let (symbols, links) = workspace_symbols(docs.get_key_value(uri).into_iter(), enc);
        let table = SymbolTable::new(symbols, links, Some(Arc::clone(&rest)));
        if !rest.resolves_above(&table) {
            return table;
        }
        let (mut symbols, mut links) = table.parts();
        let (rest_symbols, rest_links) = rest.parts();
        symbols.extend(rest_symbols);
        links.imports.extend(rest_links.imports);
        SymbolTable::new(symbols, links, Some(library))
    }

    /// "Optimize imports": every provably-unused private import in
    /// `uri` is removed and nothing else changes, so the surviving
    /// imports keep their order. An import alone on its line takes
    /// the whole line with it. Read-only over the cached session —
    /// no invalidate needed.
    pub fn optimize_imports(
        &mut self,
        docs: &BTreeMap<Uri, Document>,
        uri: &Uri,
        enc: Encoding,
    ) -> Option<Vec<TextEdit>> {
        let doc_text = docs.get(uri)?.text.clone();
        let session = self.session(docs)?;
        let unit = Self::unit_of_static(uri, session)?;
        let mut spans: Vec<Span> = session
            .unused_private_imports()
            .into_iter()
            .filter(|(u, _)| *u == unit)
            .map(|(_, s)| s)
            .collect();
        spans.sort_by_key(|s| s.start);
        spans.dedup();
        let mapper = Mapper::new(&doc_text, enc);
        Some(
            spans
                .into_iter()
                .map(|s| TextEdit {
                    range: mapper.range(whole_line_removal(&doc_text, s)),
                    new_text: String::new(),
                })
                .collect(),
        )
    }

    /// Quick fixes for an `unresolved reference` diagnostic whose
    /// name starts at `offset` in `uri` — the intent-dependent family:
    ///
    /// - "Did you mean `init`?" — near-miss spellings against the
    ///   qualifier's member names (or, for bare names, every declared
    ///   workspace name), replacement edits in place;
    /// - "Add enum member `halt` to `Phase`" — when the qualifier
    ///   resolves to a workspace enum definition, an insertion into
    ///   its body (possibly in another open document).
    ///
    /// - "Add import `SI::volt`" — exact-name candidates from the
    ///   workspace and the library, inserted the auto-import way
    ///   — an unresolved bare name is most often an out-of-scope
    ///   member.
    ///
    /// Returns `(title, document, edit, preferred)`.
    pub fn unresolved_reference_fixes(
        &mut self,
        docs: &BTreeMap<Uri, Document>,
        uri: &Uri,
        offset: u32,
        enc: Encoding,
    ) -> Vec<(String, Uri, TextEdit, bool)> {
        let Some(doc) = docs.get(uri) else {
            return Vec::new();
        };
        let text = doc.text.clone();
        let token = qualified_token_at(&text, offset);
        // Quoted references (`'m/s²'`) are not identifier tokens but
        // deserve the import fix all the same.
        let quoted = match &token {
            Some(_) => None,
            None => quoted_name_at(&text, offset),
        };
        let mut out: Vec<(String, Uri, TextEdit, bool)> = Vec::new();
        let bare = match (&token, &quoted) {
            (Some((t, segs)), _) if segs.len() == 1 => Some((segs[0].clone(), offset32(t.len()))),
            (None, Some((name, len))) => Some((name.clone(), *len)),
            _ => None,
        };
        if let Some((name, len)) = bare {
            self.import_fixes(docs, uri, &text, offset, len, &name, enc, &mut out);
        }
        let Some((token, segments)) = token else {
            return out;
        };
        let (last, prefix) = match segments.split_last() {
            Some((l, p)) => (l.clone(), p.to_vec()),
            None => return out,
        };
        let Some(session) = self.session(docs) else {
            return out;
        };
        let Some(unit) = Self::unit_of_static(uri, session) else {
            return out;
        };
        let mapper = Mapper::new(&text, enc);
        // The last segment's own range (what a respelling replaces).
        let last_start = offset + offset32(token.len() - last.len());
        let last_range = mapper.range(Span::new(last_start, offset + offset32(token.len())));

        if prefix.is_empty() {
            // Bare name: suggest near-miss workspace names.
            let mut names: Vec<String> = Vec::new();
            let resolved = session.resolved();
            let all: Vec<ElementRef> = resolved.user_elements().collect();
            for e in all {
                if let Some(n) = resolved.element_name(e) {
                    names.push(n.to_string());
                }
            }
            names.sort();
            names.dedup();
            for candidate in near_misses(&last, &names, 3) {
                out.push((
                    format!("Did you mean `{candidate}`?"),
                    uri.clone(),
                    TextEdit {
                        range: last_range,
                        new_text: candidate,
                    },
                    false,
                ));
            }
            if let Some(first) = out.first_mut() {
                first.3 = true;
            }
            return out;
        }

        // Qualified: find what the qualifier resolves to. First choice:
        // the resolver's own site for the qualifier segment (recorded
        // when the qualifier resolved even though the full name did
        // not); fallback: a unique workspace element carrying the
        // qualifier's final segment as its name.
        let prefix_last = prefix.last().expect("non-empty prefix").clone();
        let prefix_end = offset + offset32(token.len() - last.len() - 2);
        let target = {
            let resolved = session.resolved();
            let by_site = resolved
                .reference_sites()
                .iter()
                .filter(|s| {
                    s.unit == unit && s.name_span.start >= offset && s.name_span.end <= prefix_end
                })
                .max_by_key(|s| s.name_span.end)
                .map(|s| s.target);
            by_site.or_else(|| {
                let named: Vec<ElementRef> = resolved
                    .user_elements()
                    .filter(|&e| resolved.element_name(e) == Some(prefix_last.as_str()))
                    .collect();
                match named.as_slice() {
                    [one] => Some(*one),
                    _ => None,
                }
            })
        };
        let Some(target) = target else {
            return out;
        };

        let members = session.resolved().namespace_member_names(target);
        for candidate in near_misses(&last, &members, 3) {
            out.push((
                format!("Did you mean `{candidate}`?"),
                uri.clone(),
                TextEdit {
                    range: last_range,
                    new_text: candidate,
                },
                false,
            ));
        }
        if let Some(first) = out.first_mut() {
            first.3 = true;
        }

        // Enum qualifier: offer to declare the missing literal. Both
        // spellings count — `enum def Phase` (EnumerationDefinition)
        // and the usage form `enum Phase { … }` (EnumerationUsage).
        if matches!(
            session.resolved().element_type(target),
            "EnumerationDefinition" | "EnumerationUsage"
        ) && is_identifier(&last)
        {
            let site = session.resolved().declaration_site(target);
            if let Some((dunit, dspan)) = site {
                let dest = session
                    .units()
                    .find(|(i, _, _)| *i == dunit)
                    .map(|(_, n, s)| (n.to_string(), s.to_string()));
                if let Some((dest_name, dest_text)) = dest {
                    if let Ok(dest_uri) = Uri::from_str(&dest_name) {
                        if let Some((at, insert)) = enum_member_insertion(&dest_text, dspan, &last)
                        {
                            let dest_mapper = Mapper::new(&dest_text, enc);
                            let enum_name = session
                                .resolved()
                                .element_name(target)
                                .unwrap_or(&prefix_last)
                                .to_string();
                            out.push((
                                format!("Add enum member `{last}` to `{enum_name}`"),
                                dest_uri,
                                TextEdit {
                                    range: dest_mapper.range(at),
                                    new_text: insert,
                                },
                                out.is_empty(),
                            ));
                        }
                    }
                }
            }
        }
        out
    }

    /// Import quick fixes for an unresolved bare reference: one per
    /// importable workspace/library symbol whose name (either
    /// spelling) matches exactly — workspace first, the completion
    /// tier's shadowing order — inserted the auto-import way.
    /// The first is preferred. Capped: past a handful the picker
    /// stops being a fix and becomes a search.
    #[allow(clippy::too_many_arguments)]
    fn import_fixes(
        &mut self,
        docs: &BTreeMap<Uri, Document>,
        uri: &Uri,
        text: &str,
        offset: u32,
        token_len: u32,
        name: &str,
        enc: Encoding,
        out: &mut Vec<(String, Uri, TextEdit, bool)>,
    ) {
        let parse = if crate::is_kerml(uri.path().as_str()) {
            sysmlv2_parser::parser::parse_kerml_source(text)
        } else {
            sysmlv2_parser::parser::parse_source(text)
        };
        // A name that failed to resolve INSIDE an import statement is
        // not an out-of-scope member — the import target itself is
        // missing from the model. Adding another import cannot fix it;
        // the respelling family (offered by the caller) still applies.
        if crate::autoimport::within_import(&parse.unit.members, offset) {
            return;
        }
        let ws = self.all_workspace_symbols(docs, uri, enc);
        let auto = crate::autoimport::AutoImport::new(
            text,
            &parse.unit,
            offset,
            Span::new(offset, offset + token_len),
        )
        .with_reexports(&ws);
        let mapper = Mapper::new(text, enc);
        let mut seen: std::collections::HashSet<String> = std::collections::HashSet::new();
        for s in ws.iter().chain(self.library_symbols()) {
            if out.len() >= 5 {
                break;
            }
            if s.name != name || s.depth == 0 || !s.importable || !seen.insert(s.qualified.clone())
            {
                continue;
            }
            let Some(Some(edit)) = reach(&auto, s) else {
                continue;
            };
            let title = format!(
                "Add import {}",
                edit.spelled(crate::dialect_of(uri), &s.qualified)
            );
            let (at, new_text) = (edit.at, edit.text);
            out.push((
                title,
                uri.clone(),
                TextEdit {
                    range: mapper.range(Span::new(at, at)),
                    new_text,
                },
                out.is_empty(),
            ));
        }
    }

    /// Attach the declare-the-type edits to unit completion items (the
    /// [`Self::set_infer_unit_types`] behavior): for each offered
    /// symbol that would constitute the *whole* bracket content once
    /// accepted and whose unit definition denotes exactly one library
    /// quantity type, accepting the completion also inserts a
    /// `: <Type>` typing after the attribute's name — spelled as the
    /// shortest reference that resolves at the declaration's scope.
    /// `meta` holds what each item was built from (see [`Offered`]).
    fn append_unit_type_edits(
        &mut self,
        docs: &BTreeMap<Uri, Document>,
        uri: &Uri,
        enc: Encoding,
        (cx, tcx): (&CompletionCx, &UnitTypeCx),
        meta: &[Offered],
        out: &mut [lsp_types::CompletionItem],
    ) {
        let Some(doc) = docs.get(uri) else { return };
        let text = &doc.text;
        let replacement = crate::accept::Replacement::new(text, cx);
        let after = (replacement.end() as usize).min(text.len());
        let line_end = text[after..]
            .find('\n')
            .map(|i| after + i)
            .unwrap_or(text.len());
        // Anything after the accepted name other than the closing
        // bracket — or the end of the line or of the statement, where the
        // accept writes that bracket behind the name — means it is only a
        // factor of a larger unit expression: its type says nothing
        // about the whole. The accept writes the bracket only where
        // nothing but blanks follows the statement's `;` on the line (see
        // [`crate::autofix::statement_repairs`]); before a `}` or a
        // comment there the bracket stays open, and a typing would
        // declare the type of a value that does not parse.
        let rest = text[after..line_end].trim_start();
        let closed = rest.is_empty()
            || rest.starts_with(']')
            || rest
                .strip_prefix(';')
                .is_some_and(|tail| tail.trim().is_empty());
        if !closed {
            return;
        }
        let mapper = Mapper::new(text, enc);
        let insert_at = mapper.range(Span::new(tcx.name_end, tcx.name_end));
        let cut = crate::salvage::typed_statement_cut(text, cx.stmt_start, cx.offset);
        let dialect = crate::dialect_of(uri);
        let spellings = self.cut_answer(docs, uri, cut, |at| {
            let unit_of: HashMap<String, usize> = at
                .session
                .units()
                .map(|(i, name, _)| (name.to_string(), i))
                .collect();
            let resolved = at.session.resolved();
            let enclosing = crate::receiver::enclosing_declarations(resolved, at.unit, at.at);
            at.needs.scopes(&enclosing);
            // The declaration's resolution scope: the innermost enclosing
            // declaration's body, the root namespace as the fallback.
            let scope = enclosing
                .iter()
                .find_map(|&e| resolved.element_scope(e))
                .unwrap_or_else(|| resolved.root_scope());
            let mut spellings = Vec::new();
            let mut tops = None;
            for (idx, name, qualified, site) in meta {
                let start = replacement.start_for(text, name);
                let interior = text
                    .get(tcx.bracket_open as usize + 1..start as usize)
                    .map(str::trim);
                if interior != Some("") {
                    continue;
                }
                let site = site.as_deref();
                let Some(elem) = declared_element(resolved, qualified, site, &unit_of, &mut tops)
                else {
                    continue;
                };
                at.needs.read(elem);
                let mut types: Vec<ElementRef> = Vec::new();
                for def in resolved.typings(elem) {
                    for t in resolved.quantity_types_for_unit_def(def) {
                        if !types.contains(&t) {
                            types.push(t);
                        }
                    }
                }
                let [target] = types[..] else { continue };
                // The spellings tried: the type's name under each of its
                // owners', and under `ISQ`.
                at.needs.read(target);
                at.needs.name("ISQ");
                let mut owner = Some(target);
                while let Some(e) = owner {
                    if let Some(name) = resolved.element_name(e) {
                        at.needs.name(name);
                    }
                    owner = resolved.owner(e);
                }
                if let Some(spelling) = resolved.type_spelling_at(Some(dialect), scope, target) {
                    spellings.push((*idx, spelling));
                }
            }
            Some(spellings)
        });
        for (idx, spelling) in spellings.unwrap_or_default() {
            out[idx]
                .additional_text_edits
                .get_or_insert_with(Vec::new)
                .push(TextEdit {
                    range: insert_at,
                    new_text: format!(" : {spelling}"),
                });
        }
    }

    /// The features in scope at the statement being completed that a
    /// position names besides the symbol tables' names (see
    /// [`crate::site::Members`]): those the enclosing element inherits —
    /// through its specializations and typings, and from the library
    /// base every element of its kind implicitly specializes — and, for
    /// [`crate::site::Members::Scope`], its own.
    ///
    /// The element's own body is read off the live text: its own
    /// features are the ones it declares now, and a feature an earlier
    /// statement redefines — explicitly, or by declaring the same name —
    /// is no inherited member any longer. What it inherits depends on
    /// the text outside its body alone (see [`Self::inherited_members`]).
    /// Empty when the statement sits in no declaration.
    fn scope_members(
        &mut self,
        docs: &BTreeMap<Uri, Document>,
        uri: &Uri,
        cx: &CompletionCx,
        members: crate::site::Members,
    ) -> Vec<ScopeMember> {
        use crate::site::Members;
        if members == Members::None {
            return Vec::new();
        }
        let Some(doc) = docs.get(uri) else {
            return Vec::new();
        };
        let text = Arc::clone(&doc.text);
        let parse = if crate::is_kerml(uri.path().as_str()) {
            sysmlv2_parser::parser::parse_kerml_source(&text)
        } else {
            sysmlv2_parser::parser::parse_source(&text)
        };
        let (around, body) = crate::kinds::enclosing(&parse.unit, cx.stmt_start);
        // At a unit's top level no type encloses the statement: nothing
        // to name, and no session to build for it.
        let Some(innermost) = around.last() else {
            return Vec::new();
        };
        // A package inherits nothing.
        let inherited = if innermost.decl == crate::kinds::Decl::Namespace {
            Vec::new()
        } else {
            // The member the live text reads the statement in.
            let statement = body
                .iter()
                .find(|m| m.span.start <= cx.stmt_start && cx.stmt_start < m.span.end)
                .map(|m| m.span);
            self.inherited_members(docs, uri, cx, &text, &around, statement)
        };
        let own = crate::kinds::body_features(body, cx.stmt_start);
        let mut out = Vec::new();
        if members == Members::Scope {
            let path: Option<Vec<&str>> = around.iter().map(|e| e.name.as_deref()).collect();
            let path = path.map(|p| p.join("::"));
            for (name, decl) in &own {
                // A redefinition declaring no kind of its own (`ref :>>
                // start`) ranks, and shows, as the feature it redefines.
                let redefined = inherited.iter().find(|m| m.name == *name);
                use sysmlv2_parser::ast::UsageKind as U;
                let kindless = matches!(
                    decl,
                    crate::kinds::Decl::Usage(U::Default | U::Ref | U::Feature)
                );
                let (decl, kind) = match redefined {
                    Some(m) if kindless => (m.decl, m.kind),
                    Some(m) => (*decl, m.kind),
                    None => (*decl, lsp_types::CompletionItemKind::PROPERTY),
                };
                out.push(ScopeMember {
                    qualified: path.as_ref().map(|p| format!("{p}::{name}")),
                    name: name.clone(),
                    decl,
                    kind,
                    library: false,
                });
            }
        }
        // What the live body redefines — explicitly, or by declaring the
        // same name — is no inherited member any longer.
        let mut redefined = crate::kinds::redefined_names(body, cx.stmt_start);
        redefined.extend(own.into_iter().map(|(name, _)| name));
        out.extend(
            inherited
                .into_iter()
                .filter(|m| !redefined.contains(&m.name)),
        );
        out
    }

    /// What the innermost of the declarations `around` the statement
    /// being completed in `uri` inherits (see [`Self::scope_members`]).
    ///
    /// That depends on the text outside the element's own body alone —
    /// its header, its supertypes wherever they are declared — so the
    /// answer is kept by that text: the other open documents', the
    /// seeded units' no open document shadows, and this one's before and
    /// after the body. Edits inside the body, session rebuilds, and a
    /// re-seed changing only open documents' copies leave it; any edit
    /// outside asks again. The units a workspace root's walk reads from
    /// disk are not in the key: a change there, made outside the editor,
    /// surfaces with the next edit elsewhere. It is
    /// read off the most recent session already built — the completion
    /// tier's or navigation's — whose text outside the body is the live
    /// one, finding the element by the qualified name the live text
    /// gives it (one with no name, or where the lookup fails, by where
    /// it is declared), else off a completion session built for the
    /// statement (see [`Self::completion_session`]), which salvages
    /// syntax errors elsewhere. Empty when that does not build either.
    fn inherited_members(
        &mut self,
        docs: &BTreeMap<Uri, Document>,
        uri: &Uri,
        cx: &CompletionCx,
        text: &str,
        around: &[crate::kinds::Enclosing],
        statement: Option<Span>,
    ) -> Vec<ScopeMember> {
        let Some(innermost) = around.last() else {
            return Vec::new();
        };
        let (before, after) = outside_body(text, innermost.span);
        let key = member_key(docs, uri, text, (before, after), around, &self.seed_hashes);
        if let Some(i) = self.member_cache.iter().position(|(k, _)| *k == key) {
            let entry = self.member_cache.remove(i);
            let found = entry.1.clone();
            self.member_cache.insert(0, entry);
            return found;
        }
        let Some(found) = self.read_inherited(docs, uri, cx, around, statement, (before, after))
        else {
            return Vec::new();
        };
        self.member_cache.insert(0, (key, found.clone()));
        self.member_cache.truncate(MEMBER_CACHE);
        found
    }

    /// [`Self::inherited_members`] off a session: a built one whose text
    /// outside the element's body — `before` and `after` bytes of this
    /// document, every other unit whole — is the live one's, the most
    /// recent first, else one built for the statement. The element is
    /// the one the live text encloses the statement in (see
    /// [`built_inherited`]).
    fn read_inherited(
        &mut self,
        docs: &BTreeMap<Uri, Document>,
        uri: &Uri,
        cx: &CompletionCx,
        around: &[crate::kinds::Enclosing],
        statement: Option<Span>,
        (before, after): (usize, usize),
    ) -> Option<Vec<ScopeMember>> {
        let mut fp: Vec<(String, i32)> = docs
            .iter()
            .map(|(u, d)| (u.to_string(), d.version))
            .collect();
        fp.sort();
        let now = self.assemble_sources(docs, &fp);
        let name = uri.to_string();
        // The text outside the body tells nothing of a statement salvaged
        // into the body itself.
        for kind in self
            .built_by_recency()
            .into_iter()
            .filter(|kind| !kind.salvages_statements())
        {
            let Some((session, built)) = self.built_mut(kind) else {
                continue;
            };
            if !outside_unchanged(built, &now, &name, before, after) {
                continue;
            }
            let unit = Self::unit_of_static(uri, session);
            if let Some(found) = built_inherited(session.resolved(), around, unit) {
                return Some(found);
            }
        }
        let typed =
            crate::salvage::typed_statement_cut(&docs.get(uri)?.text, cx.stmt_start, cx.offset);
        // A build that fails is not tried again with another cut: what
        // failed it is elsewhere.
        let session = self.completion_session(docs, uri, typed)?;
        if let Some(unit) = Self::unit_of_static(uri, session) {
            if let Some(found) = built_inherited(session.resolved(), around, Some(unit)) {
                return Some(found);
            }
        }
        // Cut where its tokens end it, the statement can leave the rest of
        // the document past salvaging, out of the model — a transition's
        // `then` after the `}` of its `do` action reads as a statement of
        // its own, and the transition is left without it — or the element
        // out of it: then the member the live text reads the statement in
        // goes whole, in a session of its own, for the statement's stays
        // where the other tiers read it; and where that one names nothing
        // either, it is not built again for the same text.
        let member = statement.filter(|&s| s != typed)?;
        let (sources, key) = self.cut_sources(docs, uri, member);
        if self.member_cut_failed == Some(key) {
            return None;
        }
        let found = self
            .build_tolerant_session(sources)
            .and_then(|mut session| {
                let unit = Self::unit_of_static(uri, &session)?;
                built_inherited(session.resolved(), around, Some(unit))
            });
        if found.is_none() {
            self.member_cut_failed = Some(key);
        }
        found
    }

    /// Completion. Position-aware where it matters:
    /// - nothing inside a comment, a note, a documentation body, or a
    ///   string literal, nor inside a number or at a range bound
    ///   (`5.`, `[0..`) — not even when a trigger character opened the
    ///   request;
    /// - where the word being typed is a name the statement declares
    ///   (`part def Boat`, `in item fuel`, an enumeration literal),
    ///   only the keywords that may stand in its place (`part` →
    ///   `def`), never an existing element's name;
    /// - after a member-access dot (`tank.`, `wheels#(1).`, `f(x).`),
    ///   only the members the receiver reaches — none when it does not
    ///   resolve (see [`Self::chain_member_completions`]);
    /// - inside a quantity's unit bracket (`5.5 [`), only units, those of
    ///   the declared quantity first; inside any other bracket, a
    ///   multiplicity above all, nothing until a name is typed (see
    ///   [`Self::bracket_completions`]);
    /// - elsewhere the position decides which keywords of the
    ///   document's dialect and which kinds of element are offered, and
    ///   ranks them (`sortText`): after `part p :` the part definitions,
    ///   then the other structures, then namespaces; after `=` features,
    ///   invocable definitions, and literal keywords, measurement units
    ///   last — first where the statement's type is a unit type; at a
    ///   statement's start the keywords its body takes (see
    ///   [`crate::site`]); where it names the enclosing element's
    ///   features — a redefinition, a succession, a usage's subsetting, a
    ///   metadata body — those first: its body read off the live text,
    ///   what it inherits off a model current outside that body (see
    ///   [`Self::scope_members`]); within a group, shorter names first;
    /// - after a qualifier (`Foo::`), only the members of `Foo`
    ///   (workspace and library), matched by qualified-path suffix;
    /// - inside an `import` statement's path, symbols at any depth are
    ///   offered by simple name and accepting one inserts its full
    ///   qualified path over the typed partial word (a `textEdit`), so
    ///   the import actually resolves;
    /// - a position the statement does not tell apart takes every
    ///   keyword of the dialect, every workspace name, and the library's
    ///   packages and their direct members.
    ///
    /// Multi-word library names — units and the like, see
    /// [`QualifiedSymbol::is_multiword_library_name`] — are offered
    /// only inside an open bracket, where a unit is written; never in
    /// an import path. A qualifier (`Foo::`) still lists them.
    ///
    /// Operator functions (`'+'`, `'not'`, see
    /// [`QualifiedSymbol::is_operator_function`]) are written as
    /// operators, never by name: only a qualifier lists them.
    ///
    /// With the items comes whether the list is to be sent incomplete,
    /// for the client to ask again as the user types: in a quantity's
    /// unit bracket, a list read with a `]` right after the cursor
    /// closing the bracket, since what its accepts write depends on that
    /// `]` — the bracket's repair, whether a unit is the bracket's whole
    /// content. Editors add the `]` with the `[`, and the user may delete
    /// it and type on; a client refiltering the list it has would accept
    /// an item read with the `]` still there.
    pub fn completions(
        &mut self,
        docs: &BTreeMap<Uri, Document>,
        uri: &Uri,
        offset: Option<u32>,
        enc: Encoding,
    ) -> (Vec<lsp_types::CompletionItem>, bool) {
        let dialect = crate::dialect_of(uri);
        let cx = offset.and_then(|o| {
            docs.get(uri)
                .map(|d| completion_context(&d.text, o, dialect))
        });
        // Only a quantity's unit bracket: a name typed into a bound or a
        // filter would ask again for the flat list — thousands of names —
        // at every keystroke.
        let incomplete = cx.as_ref().zip(docs.get(uri)).is_some_and(|(cx, d)| {
            cx.in_bracket
                && {
                    let end = crate::accept::Replacement::new(&d.text, cx).end() as usize;
                    d.text
                        .get(end..)
                        .is_some_and(|rest| rest.trim_start_matches([' ', '\t']).starts_with(']'))
                }
                && matches!(
                    crate::units::bracket_at(&d.text, cx, dialect),
                    Some(crate::units::Bracket::Unit { .. })
                )
        });
        (self.completion_items(docs, uri, cx, enc), incomplete)
    }

    /// The items [`Self::completions`] offers with the cursor where `cx`
    /// reads it.
    fn completion_items(
        &mut self,
        docs: &BTreeMap<Uri, Document>,
        uri: &Uri,
        cx: Option<CompletionCx>,
        enc: Encoding,
    ) -> Vec<lsp_types::CompletionItem> {
        use lsp_types::{CompletionItem, CompletionItemKind};
        let dialect = crate::dialect_of(uri);
        // What the position takes: the default list below offers only
        // these keywords and names, in this order.
        let open = crate::site::Want::open(dialect);
        let want = match cx.as_ref().map(|cx| &cx.slot) {
            Some(crate::site::Slot::Quiet) => return Vec::new(),
            Some(crate::site::Slot::Declared(keywords)) => {
                return keywords
                    .iter()
                    .map(|kw| CompletionItem {
                        label: kw.to_string(),
                        kind: Some(CompletionItemKind::KEYWORD),
                        ..Default::default()
                    })
                    .collect();
            }
            Some(crate::site::Slot::Want(want)) => want,
            Some(crate::site::Slot::Open) | None => &open,
        };
        // Unit-typing context (see `append_unit_type_edits`), decided
        // once per request.
        let unit_type_cx = self
            .infer_unit_types
            .then(|| {
                cx.as_ref()
                    .zip(docs.get(uri))
                    .and_then(|(cx, d)| untyped_attribute_unit_context(&d.text, cx))
            })
            .flatten();

        // The word being completed, as a position: the incomplete
        // statement can parse as a declaration of that very word (a
        // phantom symbol), which both member and import completions
        // must not offer back.
        let partial_pos = cx.as_ref().and_then(|cx| {
            docs.get(uri)
                .map(|d| Mapper::new(&d.text, enc).position(cx.partial_start))
        });
        let uri_str = uri.to_string();
        let is_phantom =
            |s: &QualifiedSymbol| partial_pos.is_some_and(|pos| s.declared_at(&uri_str, pos));

        // Member access (`tank.` / `tank.liq` / `wheels#(1).` / `f(x).`):
        // the members the receiver could actually reach, from the
        // semantic session — nothing when it reaches none.
        if let Some(items) = cx
            .as_ref()
            .and_then(|cx| self.chain_member_completions(docs, uri, cx, enc))
        {
            return items;
        }

        // Inside a `[`: a quantity's unit bracket lists units, the
        // declared quantity's first; a multiplicity lists nothing.
        if let Some(items) = cx
            .as_ref()
            .and_then(|cx| self.bracket_completions(docs, uri, cx, enc, unit_type_cx.as_ref()))
        {
            return items;
        }

        // Qualifier context: the members the qualified namespace makes
        // visible — its own first, since they hide what an import
        // brings in under the same name, then what its public imports
        // bring in (`ISQ::` lists `MassValue`, which `ISQ` re-exports
        // from `ISQBase`). A re-exported member carries no documentation
        // here — a facade re-exports thousands, and each is documented
        // where its own namespace lists it.
        if let Some(cx) = cx.as_ref().filter(|cx| !cx.qualifier.is_empty()) {
            let path = cx.qualifier.join("::");
            let accept = docs.get(uri).map(|d| self.accept(&d.text, uri, cx, enc));
            let mut out: Vec<CompletionItem> = Vec::new();
            let mut meta: Vec<Offered> = Vec::new();
            let mut seen: std::collections::HashSet<String> = std::collections::HashSet::new();
            let ws = self.all_workspace_symbols(docs, uri, enc);
            // An `import all` names the members whatever their visibility,
            // and what every import of the namespace brings in.
            let import_all = docs
                .get(uri)
                .is_some_and(|d| imports_all(&d.text, cx.partial_start));
            // A private member only from inside its namespace, and a
            // member of a private one only from inside the namespace
            // owning that: the document is read for that only when one
            // comes up.
            let parsed = std::cell::OnceCell::new();
            let inside = |ns: &str| {
                let Some(doc) = docs.get(uri) else {
                    return false;
                };
                let parse = parsed.get_or_init(|| {
                    if crate::is_kerml(uri.path().as_str()) {
                        sysmlv2_parser::parser::parse_kerml_source(&doc.text)
                    } else {
                        sysmlv2_parser::parser::parse_source(&doc.text)
                    }
                });
                let partial = Span::new(cx.partial_start, cx.offset);
                crate::autoimport::AutoImport::new(&doc.text, &parse.unit, cx.offset, partial)
                    .inside(ns)
            };
            let visible = |s: &QualifiedSymbol| {
                if s.enclosed().is_some_and(|ns| !inside(ns)) {
                    return false;
                }
                if s.public || import_all {
                    return true;
                }
                s.site.is_some() && s.parent().is_some_and(inside)
            };
            self.library_symbols();
            let unit_types =
                crate::kinds::unit_types(None, &self.library_unit_types, definitions(ws.iter()));
            let unit_group = want.unit_group(&unit_types);
            let owned = ws
                .iter()
                .chain(self.library_symbols())
                .filter(|s| s.is_member_of(&path) && visible(s))
                .map(|s| (s, true));
            let access = if import_all {
                Access::Inside
            } else {
                Access::Clients
            };
            let reexported = ws
                .reexported_members(&path, access)
                .into_iter()
                .map(|s| (s, false));
            // Ranked as names anywhere else, the position read off the
            // text ahead of the qualified name: by its groups — measurement
            // units by the statement's type at an operand — what it does
            // not take after everything it does, then the workspace's
            // ahead of the library's, then shorter labels first
            // (`attribute x : ISQ::` puts `MassValue` among the first, its
            // quantity features after every definition). A qualifier names
            // the namespace: none of its members is left out.
            let mut ranked: Vec<(u8, Option<&str>)> = Vec::new();
            for (s, own) in owned.chain(reexported) {
                if is_phantom(s) {
                    continue;
                }
                let workspace = s.site.is_some();
                let group = want
                    .group(s.decl, workspace)
                    .map_or(9, |group| match unit_group {
                        Some(units) if s.is_unit(&unit_types) => units,
                        _ => group,
                    });
                if seen.insert(s.name.clone()) {
                    let edits = accept.as_ref().map(|a| a.name(&s.name)).unwrap_or_default();
                    meta.push(offered(out.len(), s));
                    let source = if workspace { 0 } else { 2 };
                    let label = crate::outline::spell_name(&s.name);
                    ranked.push((group, s.long.as_deref()));
                    out.push(edits.fill(
                        CompletionItem {
                            sort_text: Some(crate::site::sort_text(
                                crate::site::name_key(group, source, want.tier(s.decl)),
                                &label,
                            )),
                            label,
                            kind: Some(s.kind),
                            detail: Some(s.qualified.clone()),
                            documentation: own.then(|| s.documentation()).flatten(),
                            ..Default::default()
                        },
                        Vec::new(),
                    ));
                }
            }
            // Only the best group keeps the typed word's whole match of a
            // label of one or two characters (see [`unmatched_whole`]).
            if let Some(best) = ranked.iter().map(|&(group, _)| group).min() {
                for (item, &(group, long)) in out.iter_mut().zip(&ranked) {
                    if group > best && item.label.chars().count() <= 2 {
                        item.filter_text = Some(unmatched_whole(
                            item.filter_text.as_deref().unwrap_or(&item.label),
                            long.unwrap_or(&item.label),
                        ));
                    }
                }
            }
            // An import or expose path can name the members themselves:
            // `*`, and `**` for everything below them.
            let path_statement = docs
                .get(uri)
                .is_some_and(|d| in_import_path(&d.text, cx.partial_start));
            if path_statement && !out.is_empty() {
                for (wildcard, detail) in [
                    ("*", format!("every member of {path}")),
                    ("**", format!("every member of {path}, recursively")),
                ] {
                    let edits = accept
                        .as_ref()
                        .map(|a| a.spelled(wildcard, wildcard.to_string()))
                        .unwrap_or_default();
                    out.push(edits.fill(
                        CompletionItem {
                            label: wildcard.to_string(),
                            kind: Some(CompletionItemKind::OPERATOR),
                            detail: Some(detail),
                            ..Default::default()
                        },
                        Vec::new(),
                    ));
                }
            }
            if let Some(tcx) = unit_type_cx.as_ref() {
                self.append_unit_type_edits(docs, uri, enc, (cx, tcx), &meta, &mut out);
            }
            return out;
        }

        // Import context: everything importable, inserted as its full
        // qualified path so the reference resolves from the root — the
        // path the symbol tables choose, which may run through a
        // re-exporting package (`ISQ::MassValue`).
        if let (Some(cx), Some(doc)) = (cx.as_ref().filter(|cx| cx.import), docs.get(uri)) {
            let accept = self.accept(&doc.text, uri, cx, enc);
            let mut out: Vec<CompletionItem> = Vec::new();
            let mut seen: std::collections::HashSet<String> = std::collections::HashSet::new();
            let ws = self.all_workspace_symbols(docs, uri, enc);
            for s in ws.iter().chain(self.library_symbols()) {
                // Depth cap: packages, their members, and one level
                // below — deeper targets are reached by typing the
                // qualifier (the branch above). Keeps the unfiltered
                // import list from carrying the whole stdlib tree.
                // Only what packages own: a definition's features are
                // not imported by path.
                if is_phantom(s)
                    || s.depth > 2
                    || !s.importable
                    || s.is_multiword_library_name()
                    || s.is_operator_function()
                {
                    continue;
                }
                // A symbol its own or an ancestor's visibility confines
                // only through a package re-exporting it.
                let path = ws.import_path(&s.name, &s.qualified);
                if (s.confined().is_some() && path == s.qualified)
                    || !seen.insert(s.qualified.clone())
                {
                    continue;
                }
                let qualified = crate::autoimport::escape_qualified(crate::dialect_of(uri), &path);
                let label = crate::outline::spell_name(&s.name);
                // An import path usually names a package: packages sort
                // ahead of the members the same word matches.
                let package = s.kind == CompletionItemKind::MODULE;
                out.push(accept.spelled(&s.name, qualified).fill(
                    CompletionItem {
                        sort_text: Some(format!("{}{label}", if package { 0 } else { 1 })),
                        label,
                        kind: Some(s.kind),
                        detail: match (s.depth, &s.site) {
                            (0, None) => Some("standard library".to_string()),
                            (0, Some(_)) => None,
                            _ => Some(path),
                        },
                        documentation: s.documentation(),
                        ..Default::default()
                    },
                    Vec::new(),
                ));
            }
            return out;
        }

        // A position taking keywords alone — a statement's start in a
        // body that takes no names — needs no symbol table.
        if want.names.is_none() {
            return want
                .keywords
                .iter()
                .map(|&(kw, key)| CompletionItem {
                    label: kw.to_string(),
                    kind: Some(CompletionItemKind::KEYWORD),
                    sort_text: Some(crate::site::sort_text(key, kw)),
                    ..Default::default()
                })
                .collect();
        }

        // Position-blind default, with an auto-import tier: a
        // syntax parse of the current document tells which offered
        // names would not resolve at the cursor, and those items carry
        // the `import` insertion as an additional edit — accepting the
        // completion also makes it resolve. Suppressed by anything on
        // the scope chain that already provides the name (a
        // declaration, an admitting import).
        let doc = docs.get(uri);
        let parsed = match (cx.as_ref(), doc) {
            (Some(_), Some(d)) => Some(if crate::is_kerml(uri.path().as_str()) {
                sysmlv2_parser::parser::parse_kerml_source(&d.text)
            } else {
                sysmlv2_parser::parser::parse_source(&d.text)
            }),
            _ => None,
        };
        let ws = self.all_workspace_symbols(docs, uri, enc);
        let auto = match (cx.as_ref(), parsed.as_ref().zip(doc)) {
            (Some(cx), Some((p, d))) => Some(
                crate::autoimport::AutoImport::new(
                    &d.text,
                    &p.unit,
                    cx.offset,
                    Span::new(cx.partial_start, cx.offset),
                )
                .with_reexports(&ws),
            ),
            _ => None,
        };
        let mapper = doc.map(|d| Mapper::new(&d.text, enc));
        // The names the statement being typed declares ahead of the
        // cursor (`attribute zz = `): none is what it names itself.
        let statement = cx
            .as_ref()
            .zip(mapper.as_ref())
            .map(|(cx, m)| (m.position(cx.stmt_start), m.position(cx.offset)));
        let own_statement = |s: &QualifiedSymbol| {
            statement.is_some_and(|(from, to)| s.declared_within(&uri_str, from, to))
        };
        // What accepting a symbol offered by simple name takes to resolve
        // (see [`reach`]): `None` when nothing inserted gives it, so it
        // is not offered; nothing to tell without a cursor.
        let reached = |s: &QualifiedSymbol| match auto.as_ref() {
            Some(auto) => reach(auto, s),
            None => Some(None),
        };
        // Restricted names insert quoted, replacing the typed spelling.
        // The main edit (quoting + repair suffix) and the repair
        // insertion, per item, with the import edit ahead of the repair.
        let accept = cx
            .as_ref()
            .zip(doc)
            .map(|(cx, d)| self.accept(&d.text, uri, cx, enc));
        let assemble = |s: &QualifiedSymbol,
                        import: Option<crate::autoimport::ImportEdit>,
                        item: CompletionItem| {
            let edits = accept.as_ref().map(|a| a.name(&s.name)).unwrap_or_default();
            let extras = import
                .zip(mapper.as_ref())
                .and_then(|(edit, mapper)| import_for(mapper, crate::dialect_of(uri), s, edit));
            let (imports, label_details) = match extras {
                Some((e, d)) => (e, Some(d)),
                None => (Vec::new(), None),
            };
            edits.fill(
                CompletionItem {
                    label_details,
                    ..item
                },
                imports,
            )
        };
        // The position's keywords and names only, ranked by the
        // position's groups (`sortText`), then by source: workspace
        // names before the library's, and among each, names that
        // resolve as they stand before those needing an import.
        let mut out: Vec<CompletionItem> = want
            .keywords
            .iter()
            .map(|&(kw, key)| CompletionItem {
                label: kw.to_string(),
                kind: Some(CompletionItemKind::KEYWORD),
                sort_text: Some(crate::site::sort_text(key, kw)),
                ..Default::default()
            })
            .collect();
        let mut meta: Vec<Offered> = Vec::new();
        let mut seen: std::collections::HashSet<String> = std::collections::HashSet::new();
        // Measurement units rank by the statement's type at an
        // expression operand (see `Want::unit_group`); the unit types are
        // the library's and those the workspace derives from them.
        self.library_symbols();
        let unit_types =
            crate::kinds::unit_types(None, &self.library_unit_types, definitions(ws.iter()));
        let unit_group = want.unit_group(&unit_types);
        let group_of = |s: &QualifiedSymbol, workspace: bool| {
            let group = want.group(s.decl, workspace)?;
            Some(match unit_group {
                Some(units) if s.is_unit(&unit_types) => units,
                _ => group,
            })
        };
        // The enclosing element's features the position names, those of
        // the kinds it prefers ahead of every other name: names in
        // scope, needing no import.
        let members = match cx.as_ref() {
            Some(cx) => self.scope_members(docs, uri, cx, want.members()),
            None => Vec::new(),
        };
        // A member the symbol tables hold too takes their documentation
        // and kind, as the same name offered from them would: the
        // workspace's table finds the library's symbols as well.
        let tabled = |m: &ScopeMember| ws.symbol_at(m.qualified.as_deref()?);
        let before_members = out.len();
        for m in &members {
            if want.group(m.decl, !m.library) != Some(1) || !seen.insert(m.name.clone()) {
                continue;
            }
            let edits = accept.as_ref().map(|a| a.name(&m.name)).unwrap_or_default();
            let source = if m.library { 2 } else { 0 };
            let label = crate::outline::spell_name(&m.name);
            let known = tabled(m);
            out.push(edits.fill(
                CompletionItem {
                    sort_text: Some(crate::site::sort_text(
                        crate::site::name_key(0, source, want.tier(m.decl)),
                        &label,
                    )),
                    label,
                    kind: Some(known.map_or(m.kind, |s| s.kind)),
                    detail: m.qualified.clone(),
                    documentation: known.and_then(QualifiedSymbol::documentation),
                    ..Default::default()
                },
                Vec::new(),
            ));
        }
        // An editor ranks a label the typed word matches whole ahead of
        // every other (`m` for `m`, ahead of `mass`), whatever the order
        // given: where the enclosing element's features are named, only
        // they keep that for a label of one or two characters, which a
        // letter or two typed matches whole by chance — every other such
        // name is filtered by more than its label (see
        // [`unmatched_whole`]). A longer name typed whole keeps its match
        // (`mass` at `attribute m :> mass`, ahead of `massFlow`).
        let members_named = out.len() > before_members;
        let unit_position = cx.as_ref().zip(doc).is_some_and(|(cx, d)| {
            matches!(
                crate::units::bracket_at(&d.text, cx, crate::dialect_of(uri)),
                Some(crate::units::Bracket::Unit { .. })
            )
        });
        // An expression's operand outside a unit bracket takes no unit
        // spelled apart from the names around it, one only a quoted name
        // writes (`m/s`, `m²/(V⋅s)`): a `)` or an operator typed after a
        // name matches its symbol, and would accept it. Its plain symbols
        // (`kg`, `N`) stay, and while a quoted name is typed every unit
        // does: a derived unit's definition names them so (`Btu_IT/'°F'`,
        // `referenceUnit = 'm⋅s⁻²'`).
        let operand = matches!(want.names, Some(crate::site::Names::Operands { .. }));
        let typing_quoted = cx.as_ref().is_some_and(|cx| cx.quoted.is_some());
        let spelled_apart = |s: &QualifiedSymbol| {
            operand
                && !unit_position
                && !typing_quoted
                && s.is_unit(&unit_types)
                && sysmlv2_parser::ast::escape_name(&s.name).starts_with('\'')
        };
        let outranked = |s: &QualifiedSymbol, item: CompletionItem| {
            if !members_named || item.label.chars().count() > 2 {
                return item;
            }
            let filter_text = unmatched_whole(
                item.filter_text.as_deref().unwrap_or(&item.label),
                s.long.as_deref().unwrap_or(&item.label),
            );
            CompletionItem {
                filter_text: Some(filter_text),
                ..item
            }
        };
        for s in ws.iter() {
            let Some(group) = group_of(s, true) else {
                continue;
            };
            // The statement being typed names an unnamed usage by the
            // word typed (`satisfy Max`): that one is no candidate.
            if seen.contains(&s.name)
                || (s.effective && auto.is_none())
                || is_phantom(s)
                || own_statement(s)
                || s.is_operator_function()
                || spelled_apart(s)
            {
                continue;
            }
            let Some(import) = reached(s) else {
                continue;
            };
            if seen.insert(s.name.clone()) {
                meta.push(offered(out.len(), s));
                let item = assemble(
                    s,
                    import,
                    CompletionItem {
                        label: crate::outline::spell_name(&s.name),
                        kind: Some(s.kind),
                        detail: (!s.qualified.eq(&s.name)).then(|| s.qualified.clone()),
                        documentation: s.documentation(),
                        ..Default::default()
                    },
                );
                let source = u8::from(item.label_details.is_some());
                let item = outranked(s, item);
                out.push(CompletionItem {
                    sort_text: Some(crate::site::sort_text(
                        crate::site::name_key(group, source, want.tier(s.decl)),
                        &item.label,
                    )),
                    ..item
                });
            }
        }
        // Standard-library names last: workspace names shadow them. Kept
        // to packages + direct members — the full table would flood the
        // unfiltered list. Multi-word names only where a unit is written:
        // inside a quantity's unit bracket the statement leaves open
        // ahead of the word being completed — not a multiplicity's.
        // Operator functions never.
        for s in self.library_symbols() {
            // The cheap tests first: most symbols are deeper members,
            // and many a name is offered already.
            if s.depth > 1 || seen.contains(&s.name) {
                continue;
            }
            let Some(group) = group_of(s, false) else {
                continue;
            };
            if spelled_apart(s)
                || (!unit_position && s.is_multiword_library_name())
                || s.is_operator_function()
                || (auto.is_none() && s.is_private_library_member())
            {
                continue;
            }
            let Some(import) = reached(s) else {
                continue;
            };
            seen.insert(s.name.clone());
            meta.push(offered(out.len(), s));
            let item = assemble(
                s,
                import,
                CompletionItem {
                    label: crate::outline::spell_name(&s.name),
                    kind: Some(s.kind),
                    detail: Some(if s.depth == 0 {
                        "standard library".to_string()
                    } else {
                        s.qualified.clone()
                    }),
                    documentation: s.documentation(),
                    ..Default::default()
                },
            );
            let source = 2 + u8::from(item.label_details.is_some());
            let item = outranked(s, item);
            out.push(CompletionItem {
                sort_text: Some(crate::site::sort_text(
                    crate::site::name_key(group, source, want.tier(s.decl)),
                    &item.label,
                )),
                ..item
            });
        }
        if let (Some(cx), Some(tcx)) = (cx.as_ref(), unit_type_cx.as_ref()) {
            self.append_unit_type_edits(docs, uri, enc, (cx, tcx), &meta, &mut out);
        }
        out
    }

    /// Inlay hints: evaluated feature values (`= 42` after a
    /// non-literal value expression the evaluator settles) and
    /// propagated ranges (`∈ [10, +∞] [m]` after the declared name of a
    /// feature whose domain the asserted constraints narrow).
    pub fn inlay_hints(
        &mut self,
        docs: &BTreeMap<Uri, Document>,
        uri: &Uri,
        enc: Encoding,
    ) -> Vec<lsp_types::InlayHint> {
        use sysmlv2_parser::ast::ExprKind;
        let hide_redundant = self.hide_redundant_value_hints;
        let Some(doc_text) = docs.get(uri).map(|d| d.text.clone()) else {
            return Vec::new();
        };
        let Some(session) = self.session(docs) else {
            return Vec::new();
        };
        let Some(unit) = Self::unit_of_static(uri, session) else {
            return Vec::new();
        };
        let mapper = Mapper::new(&doc_text, enc);
        let mut out = Vec::new();

        // Evaluated values: every declared feature whose value expression
        // is not already a literal and whose value the evaluator settles.
        let parse = if crate::is_kerml(uri.path().as_str()) {
            sysmlv2_parser::parser::parse_kerml_source(&doc_text)
        } else {
            sysmlv2_parser::parser::parse_source(&doc_text)
        };
        struct Values<'a> {
            sites: Vec<(sysmlv2_parser::span::Span, sysmlv2_parser::span::Span, bool)>,
            _p: std::marker::PhantomData<&'a ()>,
        }
        impl<'a> sysmlv2_parser::visit::Visit<'a> for Values<'a> {
            fn visit_usage(&mut self, u: &'a sysmlv2_parser::ast::Usage) {
                if let (Some(name), Some(value)) = (
                    u.declaration
                        .id
                        .name
                        .as_ref()
                        .or(u.declaration.id.short_name.as_ref()),
                    u.value.as_ref(),
                ) {
                    if !matches!(value.expr.kind, ExprKind::Literal(_) | ExprKind::Null) {
                        let bare_ref = matches!(value.expr.kind, ExprKind::Ref(_));
                        self.sites.push((name.span, value.expr.span, bare_ref));
                    }
                }
                sysmlv2_parser::visit::walk_usage(self, u);
            }
        }
        let mut v = Values {
            sites: Vec::new(),
            _p: std::marker::PhantomData,
        };
        v.visit_unit(&parse.unit);
        for (name_span, expr_span, bare_ref) in v.sites.into_iter().take(200) {
            let Some(e) = session.resolved().declaration_at(unit, name_span.start) else {
                continue;
            };
            let Ok(value) = session.resolved().evaluate(e) else {
                continue;
            };
            // Element results (enum literals, referenced usages) hint by
            // name — except after a bare reference, which already spells
            // the same element, and for the unbound self-result.
            let rendered = match value {
                sysmlv2_parser::eval::Value::Unbound(_)
                | sysmlv2_parser::eval::Value::UnboundMember(_) => continue,
                sysmlv2_parser::eval::Value::Element(t) => {
                    if bare_ref || t == e {
                        continue;
                    }
                    match session.resolved().element_name(t) {
                        Some(n) => n.to_string(),
                        None => continue,
                    }
                }
                // Editor hints favour a glanceable decimal over an exact
                // fraction (`≈0.3333333333333333`, not `1/3`).
                v => session.resolved().render_value_approx(&v),
            };
            // A hint that restates the declared expression token for
            // token (`x = 3.63 [kg]` ⇒ ` = 3.63 [kg]`) adds nothing.
            if hide_redundant
                && expr_span
                    .slice(&doc_text)
                    .split_whitespace()
                    .eq(rendered.split_whitespace())
            {
                continue;
            }
            let label = format!(" = {rendered}");
            out.push(lsp_types::InlayHint {
                position: mapper.position(expr_span.end),
                label: lsp_types::InlayHintLabel::String(label),
                kind: None,
                text_edits: None,
                tooltip: None,
                padding_left: None,
                padding_right: None,
                data: None,
            });
        }

        // Propagated ranges: the cached solverless verify pass; hints go
        // after the declared name of each narrowed feature here.
        if self.verify.is_none() {
            self.verify = sysmlv2_solve::verify_constraints(
                self.session.as_ref().expect("session built above").model(),
                None,
                &sysmlv2_solve::PropagateConfig::default(),
            )
            .ok();
        }
        let session = self.session.as_mut().expect("session built above");
        if let Some(report) = self.verify.clone() {
            for r in report.ranges.iter().filter(|r| r.narrowed).take(200) {
                // The solver names features by display spelling, not by a
                // root-resolvable path. Map through the unit's reference
                // sites: the constraint that narrowed the feature also
                // references it, so a site spelling the same final
                // segment points at the declaration. Ambiguous spellings
                // (several distinct targets) and instance-path variables
                // (`ws#2.r`) are skipped.
                if r.feature.contains('#') || r.feature.contains('.') {
                    continue;
                }
                let last = r.feature.rsplit("::").next().unwrap_or(&r.feature);
                let e = match session.resolved().resolve_qualified(&r.feature) {
                    Some(e) => Some(e),
                    None => {
                        let targets: Vec<ElementRef> = session
                            .resolved()
                            .reference_sites()
                            .iter()
                            .filter(|s| s.unit == unit && s.name_span.slice(&doc_text) == last)
                            .map(|s| s.target)
                            .collect();
                        match targets.split_first() {
                            Some((first, rest)) if rest.iter().all(|t| t == first) => Some(*first),
                            _ => None, // absent or ambiguous
                        }
                    }
                };
                let Some(e) = e else {
                    continue;
                };
                let Some((dunit, dspan)) = session.resolved().declaration_site(e) else {
                    continue;
                };
                if dunit != unit {
                    continue;
                }
                // Editor hints take the glanceable spelling: a bound
                // without a terminating decimal expansion shows as an
                // approximate decimal rather than a fraction.
                let label = match &r.unit {
                    Some(u) => format!(" ∈ {} [{u}]", r.range_approx),
                    None => format!(" ∈ {}", r.range_approx),
                };
                out.push(lsp_types::InlayHint {
                    position: mapper.position(dspan.end),
                    label: lsp_types::InlayHintLabel::String(label),
                    kind: None,
                    text_edits: None,
                    tooltip: None,
                    padding_left: None,
                    padding_right: None,
                    data: None,
                });
            }
        }
        out
    }

    /// Code lenses: every constraint/requirement/invariant body in
    /// the document carries its verify verdict inline — evaluation first,
    /// then interval propagation (solverless; Z3 stays a CLI concern).
    pub fn code_lenses(
        &mut self,
        docs: &BTreeMap<Uri, Document>,
        uri: &Uri,
        enc: Encoding,
    ) -> Vec<lsp_types::CodeLens> {
        use sysmlv2_parser::check::ConstraintVerdict;
        use sysmlv2_solve::PropagateOutcome;
        let Some(doc_text) = docs.get(uri).map(|d| d.text.clone()) else {
            return Vec::new();
        };
        let Some(session) = self.session(docs) else {
            return Vec::new();
        };
        let Some(unit) = Self::unit_of_static(uri, session) else {
            return Vec::new();
        };
        let _ = session; // built the model; the cached report answers
        if self.verify.is_none() {
            self.verify = sysmlv2_solve::verify_constraints(
                self.session.as_ref().expect("session built above").model(),
                None,
                &sysmlv2_solve::PropagateConfig::default(),
            )
            .ok();
        }
        let Some(report) = self.verify.clone() else {
            return Vec::new();
        };
        let mapper = Mapper::new(&doc_text, enc);
        report
            .constraints
            .iter()
            .filter(|c| c.unit == unit)
            .map(|c| {
                // The evaluated feature values behind a violated verdict
                // (`a = 5, limit = 3`) — code lenses render unstyled, so
                // the ✗/✓ glyphs carry the at-a-glance signal.
                let why = || {
                    let vals: Vec<String> = c
                        .bindings
                        .iter()
                        .filter_map(|b| b.value.as_ref().map(|v| format!("{} = {v}", b.feature)))
                        .collect();
                    if vals.is_empty() {
                        String::new()
                    } else {
                        format!(" (with {})", vals.join(", "))
                    }
                };
                let title = match (&c.verdict, &c.propagate) {
                    (ConstraintVerdict::Satisfied, _) => "✓ satisfied".to_string(),
                    (ConstraintVerdict::Violated, _) => format!("✗ VIOLATED{}", why()),
                    (_, Some(PropagateOutcome::Satisfied)) => {
                        "✓ satisfied (propagation)".to_string()
                    }
                    (_, Some(PropagateOutcome::Violated | PropagateOutcome::Unsatisfiable)) => {
                        format!("✗ VIOLATED (propagation){}", why())
                    }
                    (ConstraintVerdict::Undecided(why), _) => format!("undecided ({why})"),
                };
                lsp_types::CodeLens {
                    range: mapper.range(c.span),
                    command: Some(lsp_types::Command {
                        title,
                        command: String::new(),
                        arguments: None,
                    }),
                    data: None,
                }
            })
            .collect()
    }

    // Static shims: `element_at` needs `&mut Session` while `self`
    // methods hold the borrow — route everything through associated fns.
    fn unit_of_static(uri: &Uri, session: &Session) -> Option<usize> {
        let name = uri.to_string();
        session
            .units()
            .find(|(_, n, _)| **n == *name.as_str())
            .map(|(i, _, _)| i)
    }

    fn location_static(
        session: &Session,
        unit: usize,
        span: Span,
        enc: Encoding,
    ) -> Option<Location> {
        if let Some((_, name, text)) = session.units().find(|(i, _, _)| *i == unit) {
            let mapper = Mapper::new(text, enc);
            return Some(Location {
                uri: Uri::from_str(name).ok()?,
                range: mapper.range(span),
            });
        }
        Self::library_location(session, unit, span, enc)
    }

    /// A location inside a *library* unit — definitions of standard-
    /// library symbols land here. In-memory libraries get the
    /// `sysmlv2-lib:/<unit name>` scheme (hosts serve the text as a
    /// read-only virtual document; browser hosts ship the same bundle
    /// the server was seeded with); directory libraries get real
    /// `file://` uris.
    fn library_location(
        session: &Session,
        unit: usize,
        span: Span,
        enc: Encoding,
    ) -> Option<Location> {
        if let Some((name, text)) = session.library_unit(unit) {
            let uri = format!("sysmlv2-lib:/{}", crate::worker::encode_uri_path(name));
            let mapper = Mapper::new(text, enc);
            return Some(Location {
                uri: Uri::from_str(&uri).ok()?,
                range: mapper.range(span),
            });
        }
        let path = session.library_unit_path(unit)?;
        let text = std::fs::read_to_string(&path).ok()?;
        let mapper = Mapper::new(&text, enc);
        Some(Location {
            uri: Uri::from_str(&crate::worker::uri_for_path(&path)).ok()?,
            range: mapper.range(span),
        })
    }
}

/// The workspace's `sysmlint.json`, read from disk only when it
/// changes. Formatting and every code-action request consult it, both
/// of which fire per keystroke or per cursor move, and each consult
/// used to be a directory read, a file read and a JSON parse.
struct LintConfig {
    path: Option<PathBuf>,
    /// The file's `(modified, len)` at the last read, `None` for no
    /// readable file — a file written twice inside one clock tick, at
    /// the same length, is the one change this misses.
    stamp: Option<(std::time::SystemTime, u64)>,
    /// Bumped whenever the configuration changes, so a cache built on
    /// it can tell one from another without keeping its text.
    generation: u64,
    config: sysmlv2_lint::Config,
    read: bool,
}

impl LintConfig {
    fn under(root: Option<&std::path::Path>) -> LintConfig {
        LintConfig {
            path: root.map(|r| r.join("sysmlint.json")),
            stamp: None,
            generation: 0,
            config: sysmlv2_lint::Config::default(),
            read: false,
        }
    }

    /// The configuration and the generation it belongs to, re-reading
    /// the file when its timestamp or size moved. An absent or
    /// unparseable file is every rule at its default severity — the
    /// worker publishes the parse error on the file itself.
    fn get(&mut self) -> (u64, &sysmlv2_lint::Config) {
        let stamp = self
            .path
            .as_ref()
            .and_then(|p| std::fs::metadata(p).ok())
            .and_then(|m| Some((m.modified().ok()?, m.len())));
        if self.read && stamp == self.stamp {
            return (self.generation, &self.config);
        }
        self.stamp = stamp;
        self.read = true;
        self.generation += 1;
        self.config = self
            .path
            .as_ref()
            .and_then(|p| std::fs::read_to_string(p).ok())
            .and_then(|text| sysmlv2_lint::Config::from_json(&text).ok())
            .unwrap_or_default();
        (self.generation, &self.config)
    }
}

/// The name and text of a session's user unit by model unit index.
fn unit_of(session: &Session, unit: usize) -> Option<(&str, &str)> {
    session
        .units()
        .find(|(i, _, _)| *i == unit)
        .map(|(_, name, text)| (name, text))
}

/// One lint finding's fixes, ready for a code-action response: the
/// finding's rule and range identify the diagnostic it rides, `edit` is
/// the preferred fix and `alternatives` the equally valid ones (label,
/// semantic, edit).
pub struct LintFixSet {
    pub rule: &'static str,
    pub range: lsp_types::Range,
    pub label: String,
    /// The fix changes what a declaration means: its own quick fix,
    /// never part of fix-all.
    pub semantic: bool,
    /// The fix deletes model text: never part of fix-all.
    pub deletes: bool,
    pub edit: WorkspaceEdit,
    pub alternatives: Vec<(String, bool, WorkspaceEdit)>,
}

/// Flatten one document's outline into (name, kind, range) triples for
/// `workspace/symbol`. The `import` and `expose` members (`imports`, by
/// start; see [`crate::outline::Plumbing`]) declare nothing and are
/// left out, and so are anonymous members (`«part»`), which have no
/// name to search for — the named members inside them stay. The
/// outline keeps both.
pub fn flatten_symbols(
    symbols: &[lsp_types::DocumentSymbol],
    uri: &Uri,
    query: &str,
    imports: &std::collections::HashSet<Position>,
    out: &mut Vec<lsp_types::SymbolInformation>,
) {
    for s in symbols {
        if imports.contains(&s.range.start) {
            continue;
        }
        let named = !s.name.starts_with('«');
        if named && (query.is_empty() || s.name.to_lowercase().contains(&query.to_lowercase())) {
            #[allow(deprecated)]
            out.push(lsp_types::SymbolInformation {
                name: crate::outline::spell_name(&s.name),
                kind: s.kind,
                tags: None,
                deprecated: None,
                location: Location {
                    uri: uri.clone(),
                    range: s.selection_range,
                },
                container_name: None,
            });
        }
        if let Some(children) = &s.children {
            flatten_symbols(children, uri, query, imports, out);
        }
    }
}

/// documentHighlight: references within one document only.
pub fn highlights_in(locations: Vec<Location>, uri: &Uri) -> Vec<lsp_types::DocumentHighlight> {
    locations
        .into_iter()
        .filter(|l| l.uri == *uri)
        .map(|l| lsp_types::DocumentHighlight {
            range: l.range,
            kind: Some(lsp_types::DocumentHighlightKind::TEXT),
        })
        .collect()
}

/// A position's byte offset in a document under `enc`.
pub fn offset_in(text: &str, pos: Position, enc: Encoding) -> u32 {
    Mapper::new(text, enc).offset(pos)
}

/// The `::`-qualified name token starting at `offset`: its full text
/// and its segments. `None` when `offset` does not start an
/// identifier.
fn qualified_token_at(text: &str, offset: u32) -> Option<(String, Vec<String>)> {
    let bytes = text.as_bytes();
    let start = offset as usize;
    if start >= bytes.len() || !is_ident_byte(bytes[start]) {
        return None;
    }
    let mut i = start;
    while i < bytes.len() {
        if is_ident_byte(bytes[i]) {
            i += 1;
        } else if bytes[i] == b':'
            && i + 2 < bytes.len()
            && bytes[i + 1] == b':'
            && is_ident_byte(bytes[i + 2])
        {
            i += 2;
        } else {
            break;
        }
    }
    let token = text[start..i].to_string();
    let segments = token.split("::").map(str::to_string).collect();
    Some((token, segments))
}

fn is_ident_byte(b: u8) -> bool {
    b.is_ascii_alphanumeric() || b == b'_'
}

/// A quoted restricted name starting at `offset` (`'m/s²'`): its inner
/// text and full token length. Names carrying escape sequences are
/// skipped rather than unescaped — good enough for the exact-name
/// candidate match.
fn quoted_name_at(text: &str, offset: u32) -> Option<(String, u32)> {
    let rest = text.get(offset as usize..)?;
    let inner = rest.strip_prefix('\'')?;
    let end = inner.find('\'')?;
    let name = &inner[..end];
    (!name.is_empty() && !name.contains('\\')).then(|| (name.to_string(), offset32(end) + 2))
}

fn is_identifier(s: &str) -> bool {
    !s.is_empty() && s.bytes().all(is_ident_byte) && !s.as_bytes()[0].is_ascii_digit()
}

/// Candidates within a small edit distance of `name`, best first —
/// distance 1 for short names, up to 2 for longer ones, matched
/// case-insensitively and never the name itself.
fn near_misses(name: &str, candidates: &[String], cap: usize) -> Vec<String> {
    let lower = name.to_lowercase();
    let budget = if name.len() <= 4 { 1 } else { 2 };
    let mut scored: Vec<(usize, String)> = candidates
        .iter()
        .filter(|c| !c.is_empty() && c.as_str() != name)
        .filter_map(|c| {
            let d = levenshtein(&lower, &c.to_lowercase());
            (d > 0 && d <= budget).then(|| (d, c.clone()))
        })
        .collect();
    scored.sort();
    scored.dedup_by(|a, b| a.1 == b.1);
    scored.into_iter().take(cap).map(|(_, c)| c).collect()
}

fn levenshtein(a: &str, b: &str) -> usize {
    let (a, b): (Vec<char>, Vec<char>) = (a.chars().collect(), b.chars().collect());
    let mut row: Vec<usize> = (0..=b.len()).collect();
    for (i, &ca) in a.iter().enumerate() {
        let mut prev = row[0];
        row[0] = i + 1;
        for (j, &cb) in b.iter().enumerate() {
            let cur = row[j + 1];
            row[j + 1] = if ca == cb {
                prev
            } else {
                1 + prev.min(cur).min(row[j])
            };
            prev = cur;
        }
    }
    row[b.len()]
}

/// Where and what to insert to declare a new member named `name` in
/// the body of the definition whose declared-name span is `decl`.
/// Multi-line bodies get an indented member line above the closing
/// brace; single-line bodies squeeze it in before the brace. `None`
/// when the declaration has no body.
fn enum_member_insertion(text: &str, decl: Span, name: &str) -> Option<(Span, String)> {
    let bytes = text.as_bytes();
    let mut i = decl.end as usize;
    while i < bytes.len() && bytes[i] != b'{' && bytes[i] != b';' {
        i += 1;
    }
    if i >= bytes.len() || bytes[i] != b'{' {
        return None;
    }
    let open = i;
    let mut depth = 0usize;
    let mut close = None;
    for (j, &b) in bytes.iter().enumerate().skip(open) {
        match b {
            b'{' => depth += 1,
            b'}' => {
                depth -= 1;
                if depth == 0 {
                    close = Some(j);
                    break;
                }
            }
            _ => {}
        }
    }
    let close = close?;
    let line_start = text[..close].rfind('\n').map(|k| k + 1).unwrap_or(0);
    if line_start > open && text[line_start..close].trim().is_empty() {
        let decl_line = text[..decl.start as usize]
            .rfind('\n')
            .map(|k| k + 1)
            .unwrap_or(0);
        let indent: String = text[decl_line..]
            .chars()
            .take_while(|c| *c == ' ' || *c == '\t')
            .collect();
        Some((
            Span::new(offset32(line_start), offset32(line_start)),
            format!("{indent}    {name};\n"),
        ))
    } else {
        let insert = if close > 0 && bytes[close - 1].is_ascii_whitespace() {
            format!("{name}; ")
        } else {
            format!(" {name}; ")
        };
        Some((Span::new(offset32(close), offset32(close)), insert))
    }
}

/// Extend a member's removal span to its whole line when the member
/// sits alone on it: leading indentation, trailing spaces, and the
/// newline all go, so removal leaves no blank line behind. A member
/// sharing its line with other text removes only itself.
fn whole_line_removal(text: &str, span: Span) -> Span {
    let bytes = text.as_bytes();
    let start = (span.start as usize).min(bytes.len());
    let end = (span.end as usize).min(bytes.len());
    let ls = text[..start].rfind('\n').map(|i| i + 1).unwrap_or(0);
    let indent_only = text[ls..start].bytes().all(|b| b == b' ' || b == b'\t');
    let mut le = end;
    while le < bytes.len() && matches!(bytes[le], b' ' | b'\t' | b'\r') {
        le += 1;
    }
    if indent_only && le < bytes.len() && bytes[le] == b'\n' {
        return Span::new(offset32(ls), offset32(le + 1));
    }
    if indent_only && le == bytes.len() {
        return Span::new(offset32(ls), offset32(le));
    }
    Span::new(offset32(start), offset32(end))
}

/// "Sort imports": alphabetize each contiguous run of import
/// statements (same body, nothing but blank space between consecutive
/// members) by imported path, case-insensitive. Statements move as
/// whole member texts, so visibility prefixes, filters, and
/// `::*`/`::**` suffixes ride along. Syntax-tier: a parse, no model.
pub fn sort_import_edits(text: &str, kerml: bool, enc: Encoding) -> Vec<TextEdit> {
    let parse = if kerml {
        sysmlv2_parser::parser::parse_kerml_source(text)
    } else {
        sysmlv2_parser::parser::parse_source(text)
    };
    let mut runs: Vec<Vec<(Span, String)>> = Vec::new();
    collect_import_runs(&parse.unit.members, text, &mut runs);
    let mapper = Mapper::new(text, enc);
    let mut edits = Vec::new();
    for run in runs {
        if run.len() < 2 {
            continue;
        }
        let original: Vec<&str> = run.iter().map(|(s, _)| s.slice(text)).collect();
        let mut order: Vec<usize> = (0..run.len()).collect();
        order.sort_by(|&a, &b| run[a].1.cmp(&run[b].1));
        for (pos, &src) in order.iter().enumerate() {
            if src != pos {
                edits.push(TextEdit {
                    range: mapper.range(run[pos].0),
                    new_text: original[src].to_string(),
                });
            }
        }
    }
    edits
}

/// Collect maximal runs of consecutive import members per body —
/// consecutive meaning nothing but whitespace between the members'
/// spans (a comment or any other member breaks the run, and each
/// side sorts independently).
fn collect_import_runs(
    members: &[sysmlv2_parser::ast::Member],
    text: &str,
    out: &mut Vec<Vec<(Span, String)>>,
) {
    use sysmlv2_parser::ast::MemberKind;
    let mut run: Vec<(Span, String)> = Vec::new();
    for m in members {
        let mut close = |run: &mut Vec<(Span, String)>| {
            if run.len() > 1 {
                out.push(std::mem::take(run));
            } else {
                run.clear();
            }
        };
        match &m.kind {
            MemberKind::Import(imp) => {
                let contiguous = run.last().is_none_or(|(prev, _)| {
                    text[prev.end as usize..m.span.start as usize]
                        .chars()
                        .all(char::is_whitespace)
                });
                if !contiguous {
                    close(&mut run);
                }
                let suffix = if imp.is_recursive {
                    "::**"
                } else if imp.is_namespace {
                    "::*"
                } else {
                    ""
                };
                let key = format!("{}{suffix}", imp.target.to_display_string()).to_lowercase();
                run.push((m.span, key));
            }
            kind => {
                close(&mut run);
                let body = match kind {
                    MemberKind::Package(p) => p.body.as_deref(),
                    MemberKind::Definition(d) => d.body.as_deref(),
                    MemberKind::Usage(u) => u.body.as_deref(),
                    _ => None,
                };
                if let Some(body) = body {
                    collect_import_runs(body, text, out);
                }
            }
        }
    }
    if run.len() > 1 {
        out.push(run);
    }
}

/// The filter text of an item ranked below the best group a list holds:
/// `filter` — its label, or the text it is filtered by already — then
/// `_` and `tail`, the name it is spelled for (`K_kelvin`, `m_metre`) or
/// its label again. An editor ranks a label the typed word matches whole
/// ahead of every other (`K` for `k`, ahead of `kg`), whatever the order
/// the server gives; this one the word matches no more than in part, so
/// the order given decides. No whitespace: a typed space still closes
/// the list.
fn unmatched_whole(filter: &str, tail: &str) -> String {
    format!("{filter}_{}", tail.replace(char::is_whitespace, "_"))
}

/// A named symbol with its `::`-qualified path, flattened from an
/// outline tree. `depth` counts nesting from the unit root (0 = a
/// top-level package). Workspace symbols carry their declaration site
/// (`uri` + name span) so the import and qualifier branches of
/// completion can drop the phantom symbol the half-typed statement
/// itself declares — an import missing its `;` runs on into the next
/// statement (`private import Kit::*` ⏎ `part def Widg|;`), which
/// declares the very word being typed, and offering that back
/// (qualified into its accidental owner) would outrank the real
/// target.
#[derive(Clone)]
pub(crate) struct QualifiedSymbol {
    name: String,
    qualified: String,
    kind: lsp_types::CompletionItemKind,
    depth: usize,
    /// Every ancestor is a package/namespace — the symbol is sensibly
    /// importable by its qualified path (a type's feature is not: it
    /// is either inherited into scope already or not meant for
    /// namespace import).
    importable: bool,
    /// Declaration site for workspace symbols; `None` for the library.
    site: Option<(String, lsp_types::Range)>,
    /// The declaration's `doc` body, display-normalized.
    doc: Option<String>,
    /// Named by an operator and naming a function
    /// ([`Self::is_operator_function`]).
    operator: bool,
    /// Declared without `private` or `protected`: a member of its
    /// namespace for clients outside it too, which a public import of
    /// the namespace re-exports.
    public: bool,
    /// What the declaration is: completion admits and ranks candidates
    /// by it.
    decl: crate::kinds::Decl,
    /// The types the declaration names, last segment only (see
    /// [`crate::kinds::Declared::types`]).
    types: Vec<String>,
    /// The declared name, for an entry spelled by its short name (`m`
    /// for `metre`).
    long: Option<String>,
    /// What an alias names, as written: the symbol table it is indexed
    /// in takes it as its target (see [`SymbolTable`]).
    alias: Option<Box<crate::outline::Written>>,
    /// The length of the path, a prefix of `qualified`, of the
    /// namespace owning the innermost of the symbol's ancestors that is
    /// private or protected: outside it, no path through that ancestor
    /// names the symbol (see [`Self::enclosed`]).
    enclosed: Option<u32>,
    /// A usage without a name of its own, found by the name of the
    /// feature it redefines or references (see
    /// [`crate::outline::Plumbing::effective`]): a recursive import
    /// brings it in, but nothing it holds.
    effective: bool,
}

impl QualifiedSymbol {
    /// Does this symbol name a measurement unit — a usage typed by one
    /// of `unit_types` (see [`crate::kinds::unit_types`]), or an alias
    /// of one?
    fn is_unit(&self, unit_types: &std::collections::HashSet<String>) -> bool {
        matches!(self.decl, crate::kinds::Decl::Usage(_))
            && self.types.iter().any(|t| unit_types.contains(t))
    }

    /// The symbol's doc body as completion-item documentation.
    fn documentation(&self) -> Option<lsp_types::Documentation> {
        self.doc.as_ref().map(|d| {
            lsp_types::Documentation::MarkupContent(lsp_types::MarkupContent {
                kind: lsp_types::MarkupKind::Markdown,
                value: d.clone(),
            })
        })
    }

    /// A library name containing whitespace. In the standard library
    /// these are measurement vocabulary: units and their aliases
    /// (`'metric ton'`), measurement scales, and the systems of units
    /// and quantities; a library a host supplies is held to the same
    /// rule. Offered only where a unit is written: anywhere else they
    /// are noise, some 380 labels in every response.
    fn is_multiword_library_name(&self) -> bool {
        self.site.is_none() && self.name.chars().any(char::is_whitespace)
    }

    /// The qualified path of the namespace owning the symbol; `None` at
    /// the root.
    fn parent(&self) -> Option<&str> {
        self.qualified
            .strip_suffix(self.name.as_str())?
            .strip_suffix("::")
    }

    /// The namespace outside which an ancestor's visibility keeps the
    /// symbol from being named by its path: the one owning the innermost
    /// ancestor that is private or protected. `None` when none is.
    fn enclosed(&self) -> Option<&str> {
        self.enclosed.map(|n| &self.qualified[..n as usize])
    }

    /// The namespace outside which the symbol cannot be named by its
    /// path: its own when it is private or protected, else the one its
    /// ancestors keep it in ([`Self::enclosed`]). `None` when it can be
    /// named anywhere.
    fn confined(&self) -> Option<&str> {
        if self.public {
            self.enclosed()
        } else {
            Some(self.parent().unwrap_or_default())
        }
    }

    /// A private or protected member of a library namespace: no name a
    /// model can use.
    fn is_private_library_member(&self) -> bool {
        self.site.is_none() && !self.public
    }

    /// A function named by an operator of the expression notation —
    /// a run of punctuation (`'+'`, `'['`, `'..'`) or a reserved word
    /// (`'not'`, `'xor'`, `'implies'`) — or an alias naming one
    /// (`alias '*' for scalarVectorMult;`). The notation writes it as
    /// that operator and never by name, so only a qualifier offers it.
    /// The element decides, not the spelling: a unit spelled with a
    /// symbol is no function, and a function whose quoted name holds a
    /// word (`'cartesian+'`) is a name like any other.
    fn is_operator_function(&self) -> bool {
        self.operator
    }
}

impl QualifiedSymbol {
    /// Is this symbol declared exactly at the word being completed in
    /// `uri` (the phantom the incomplete statement itself introduces)?
    fn declared_at(&self, uri: &str, pos: lsp_types::Position) -> bool {
        match &self.site {
            Some((u, range)) => u == uri && range.start <= pos && pos <= range.end,
            None => false,
        }
    }

    /// Is the symbol declared in `uri` between `from` and `to`?
    fn declared_within(
        &self,
        uri: &str,
        from: lsp_types::Position,
        to: lsp_types::Position,
    ) -> bool {
        match &self.site {
            Some((u, range)) => u == uri && from <= range.start && range.end <= to,
            None => false,
        }
    }
}

impl QualifiedSymbol {
    /// Is this symbol a direct member of `path`? Suffix-matched — the
    /// syntax tier cannot resolve aliases or relative scopes, so `Sub`
    /// also matches members of `Outer::Sub`.
    fn is_member_of(&self, path: &str) -> bool {
        let Some(parent) = self
            .qualified
            .strip_suffix(self.name.as_str())
            .and_then(|p| p.strip_suffix("::"))
        else {
            return false;
        };
        parent
            .strip_suffix(path)
            .is_some_and(|rest| rest.is_empty() || rest.ends_with("::"))
    }
}

fn completion_kind(k: lsp_types::SymbolKind) -> lsp_types::CompletionItemKind {
    use lsp_types::{CompletionItemKind, SymbolKind};
    match k {
        SymbolKind::NAMESPACE | SymbolKind::PACKAGE | SymbolKind::MODULE => {
            CompletionItemKind::MODULE
        }
        SymbolKind::CLASS => CompletionItemKind::CLASS,
        SymbolKind::STRUCT => CompletionItemKind::STRUCT,
        SymbolKind::TYPE_PARAMETER => CompletionItemKind::TYPE_PARAMETER,
        SymbolKind::INTERFACE => CompletionItemKind::INTERFACE,
        SymbolKind::CONSTRUCTOR => CompletionItemKind::CONSTRUCTOR,
        SymbolKind::ENUM => CompletionItemKind::ENUM,
        SymbolKind::ENUM_MEMBER => CompletionItemKind::ENUM_MEMBER,
        SymbolKind::PROPERTY => CompletionItemKind::PROPERTY,
        SymbolKind::FUNCTION => CompletionItemKind::FUNCTION,
        SymbolKind::NUMBER => CompletionItemKind::CLASS,
        SymbolKind::METHOD => CompletionItemKind::METHOD,
        SymbolKind::EVENT => CompletionItemKind::EVENT,
        SymbolKind::OPERATOR | SymbolKind::BOOLEAN => CompletionItemKind::OPERATOR,
        SymbolKind::FIELD => CompletionItemKind::FIELD,
        SymbolKind::CONSTANT => CompletionItemKind::CONSTANT,
        SymbolKind::FILE => CompletionItemKind::FILE,
        // Metadata definitions and usages: keywords alone carry the
        // keyword kind, and no other symbol completes as a reference.
        SymbolKind::KEY => CompletionItemKind::REFERENCE,
        SymbolKind::OBJECT | SymbolKind::STRING => CompletionItemKind::VALUE,
        _ => CompletionItemKind::VARIABLE,
    }
}

/// Flatten an outline tree into qualified symbols, the nodes at this
/// level kept by their ancestors inside the namespace `enclosed` gives
/// the length of (see [`QualifiedSymbol::enclosed`]). Anonymous
/// (`«keyword»`) members have no referenceable name — their subtrees
/// are skipped, since a qualified path through them would not resolve.
/// Neither are the `import` and `expose` members (see
/// [`crate::outline::Plumbing`]): the outline lists them under their
/// target's spelling, but they declare nothing — an `import SI::m;` in
/// `P` is no member `P::SI::m`. The imports are recorded in `links`
/// instead, against the namespace they sit in.
#[allow(clippy::too_many_arguments)] // one recursive walk, one context set
fn collect_qualified(
    nodes: &[lsp_types::DocumentSymbol],
    prefix: &str,
    depth: usize,
    in_packages: bool,
    uri: Option<&str>,
    docs: &HashMap<lsp_types::Position, String>,
    shorts: &HashMap<lsp_types::Position, String>,
    plumbing: &mut crate::outline::Plumbing,
    links: &mut Links,
    decls: &HashMap<lsp_types::Position, crate::kinds::Declared>,
    enclosed: Option<u32>,
    out: &mut Vec<QualifiedSymbol>,
) {
    for s in nodes {
        // An unnamed usage is found by the name of what it redefines or
        // references, and what it holds by paths through that name.
        let effective = plumbing.effective.get(&s.range.start);
        if s.name.starts_with('«') && effective.is_none() {
            continue;
        }
        // Such a usage's name is where the text spells what names it.
        let (name, spelled) = effective.map_or((&s.name, s.selection_range), |(n, r)| (n, *r));
        if plumbing.imports.contains(&s.range.start) {
            if let Some(form) = plumbing.import_forms.get(&s.range.start) {
                links.import(prefix, form, uri);
            }
            continue;
        }
        // What completion shows, admits, and ranks the symbol as. An
        // alias is what it names, which the symbol table it is indexed in
        // finds; until then, and when the target does not resolve, it
        // keeps the module kind of its outline node and may name
        // anything.
        let alias = plumbing.aliases.get(&s.range.start).cloned().map(Box::new);
        let kind = completion_kind(s.kind);
        let function = alias.is_none()
            && matches!(
                s.kind,
                lsp_types::SymbolKind::FUNCTION
                    | lsp_types::SymbolKind::OPERATOR
                    | lsp_types::SymbolKind::BOOLEAN
            );
        let qualified = if prefix.is_empty() {
            name.clone()
        } else {
            format!("{prefix}::{name}")
        };
        let decl = decl_at(decls, s.selection_range.start);
        let types = types_at(decls, s.selection_range.start);
        out.push(QualifiedSymbol {
            name: name.clone(),
            qualified: qualified.clone(),
            kind,
            depth,
            importable: in_packages,
            site: uri.map(|u| (u.to_string(), spelled)),
            doc: docs.get(&s.selection_range.start).cloned(),
            operator: is_operator_spelling(name) && function,
            public: !plumbing.hidden.contains(&s.range.start),
            decl,
            types: types.clone(),
            long: None,
            alias: alias.clone(),
            enclosed,
            effective: effective.is_some(),
        });
        // What it specializes, as written, goes to the links, the short
        // symbol below sharing it.
        let bases = plumbing.bases.remove(&s.range.start);
        // A short symbol (`<'m/s²'>`) alongside the regular name is its
        // own referenceable spelling — its own entry, same everything
        // else. Nothing nests under it: children path through the
        // regular name.
        if let Some(short) = shorts.get(&s.selection_range.start) {
            let path = if prefix.is_empty() {
                short.clone()
            } else {
                format!("{prefix}::{short}")
            };
            if let Some(bases) = &bases {
                links.bases.push((path.clone(), bases.clone()));
            }
            out.push(QualifiedSymbol {
                name: short.clone(),
                qualified: path,
                kind,
                depth,
                importable: in_packages,
                site: uri.map(|u| (u.to_string(), s.selection_range)),
                doc: docs.get(&s.selection_range.start).cloned(),
                operator: is_operator_spelling(short) && function,
                public: !plumbing.hidden.contains(&s.range.start),
                decl,
                types,
                long: Some(s.name.clone()),
                alias,
                enclosed,
                effective: false,
            });
        }
        if let Some(bases) = bases {
            links.bases.push((qualified.clone(), bases));
        }
        if let Some(children) = &s.children {
            let nested = in_packages
                && matches!(
                    s.kind,
                    lsp_types::SymbolKind::NAMESPACE | lsp_types::SymbolKind::PACKAGE
                );
            collect_qualified(
                children,
                &qualified,
                depth + 1,
                nested,
                uri,
                docs,
                shorts,
                plumbing,
                links,
                decls,
                // A private or protected member keeps what it holds
                // inside the namespace owning it.
                if plumbing.hidden.contains(&s.range.start) {
                    Some(u32::try_from(prefix.len()).unwrap_or(u32::MAX))
                } else {
                    enclosed
                },
                out,
            );
        }
    }
}

/// A name the expression notation spells as an operator: a run of
/// punctuation (`+`, `[`, `..`) or a reserved word (`not`, `xor`) of
/// the kernel language, whose expression notation both dialects share.
fn is_operator_spelling(name: &str) -> bool {
    let punctuation =
        !name.is_empty() && name.chars().all(|c| c.is_ascii_punctuation() && c != '_');
    punctuation || sysmlv2_parser::parser::is_reserved(sysmlv2_parser::ast::Dialect::Kerml, name)
}

/// The definitions among `symbols`, with the names they specialize.
fn definitions<'a>(
    symbols: impl IntoIterator<Item = &'a QualifiedSymbol>,
) -> impl Iterator<Item = (&'a str, &'a [String])> {
    symbols
        .into_iter()
        .filter(|s| matches!(s.decl, crate::kinds::Decl::Definition(_)))
        .map(|s| (s.name.as_str(), s.types.as_slice()))
}

/// The declaration kind recorded at an outline selection position.
fn decl_at(
    decls: &HashMap<lsp_types::Position, crate::kinds::Declared>,
    at: lsp_types::Position,
) -> crate::kinds::Decl {
    decls.get(&at).map_or(crate::kinds::Decl::Other, |d| d.decl)
}

/// The types the declaration at an outline selection position names.
fn types_at(
    decls: &HashMap<lsp_types::Position, crate::kinds::Declared>,
    at: lsp_types::Position,
) -> Vec<String> {
    decls.get(&at).map(|d| d.types.clone()).unwrap_or_default()
}

/// Open documents' outlines, flattened to qualified symbols, and the
/// documents' imports.
fn workspace_symbols<'d>(
    docs: impl Iterator<Item = (&'d Uri, &'d Document)>,
    enc: Encoding,
) -> (Vec<QualifiedSymbol>, Links) {
    let mut out = Vec::new();
    let mut links = Links::default();
    for (uri, doc) in docs {
        let kerml = crate::is_kerml(uri.path().as_str());
        let uri = uri.to_string();
        collect_unit(&doc.text, kerml, Some(&uri), enc, &mut out, &mut links);
    }
    (out, links)
}

/// Flatten one unit's outline into `symbols` and record its imports in
/// `links`. `uri` is the declaration site of a workspace unit's symbols.
fn collect_unit(
    text: &str,
    kerml: bool,
    uri: Option<&str>,
    enc: Encoding,
    symbols: &mut Vec<QualifiedSymbol>,
    links: &mut Links,
) {
    let parse = if kerml {
        sysmlv2_parser::parser::parse_kerml_source(text)
    } else {
        sysmlv2_parser::parser::parse_source(text)
    };
    let mapper = Mapper::new(text, enc);
    let roots = crate::document_symbols(&parse.unit, text, &mapper);
    let bodies = crate::outline::doc_bodies(&parse.unit, &mapper);
    let shorts = crate::outline::short_names(&parse.unit, &mapper);
    let mut plumbing = crate::outline::plumbing(&parse.unit, &mapper);
    let decls = crate::kinds::declarations(&parse.unit, &mapper);
    collect_qualified(
        &roots,
        "",
        0,
        true,
        uri,
        &bodies,
        &shorts,
        &mut plumbing,
        links,
        &decls,
        None,
        symbols,
    );
}

/// What `owner` inherits (see [`Nav::inherited_members`]), whatever
/// its body holds. The model's inheritance leaves out what the owner's
/// own features redefine — explicitly, by position (a parameter, an
/// end, a calculation's `return`, a `subject`), or by declaring the same
/// name — and the body the model was built from need not be the live
/// one (see [`Nav::scope_members`]): the statement being typed is cut
/// out of it, which moves the parameters after it. So what it left out
/// comes back: the features of the types the element is typed by,
/// specializes, subsets, or redefines, and of the library bases it
/// specializes implicitly (an action's `Actions::Action`, whose `start`
/// and `done` every action has), each as its type has them — but for
/// those another feature of the heritage redefines and those private to
/// their type. A redefinition's target may be more general than the
/// feature inherited (`:>> elements` names a collection's), and one not
/// inherited at all stays out. The live body then takes out what it
/// redefines by name; what it redefines by position alone stays
/// offered, whichever of its statements was typed first. A metadata
/// usage inherits nothing in the model: its body names the features of
/// the metadata definition it is typed by.
fn inherited_of(
    resolved: &mut sysmlv2_parser::json::ResolvedModel,
    owner: ElementRef,
) -> Vec<ScopeMember> {
    use std::collections::HashSet;
    let mut features = resolved.inherited_features(owner, true);
    // With no feature of its own, the owner loses nothing to its body —
    // and one inheriting nothing then is a metadata usage, whose members
    // are its definition's.
    if resolved.owned_features(owner).is_empty() {
        if features.is_empty() {
            for t in resolved.typings(owner) {
                features.extend(resolved.effective_features(t, true));
            }
        }
        return scope_members_of(resolved, features);
    }
    let mut general = resolved.typings(owner);
    for g in resolved.explicit_supertypes(owner) {
        if !general.contains(&g) {
            general.push(g);
        }
    }
    // The features of the general types, each once.
    let mut candidates = Vec::new();
    let mut seen = HashSet::new();
    for &g in &general {
        for f in resolved.effective_features(g, true) {
            if seen.insert(f) {
                candidates.push(f);
            }
        }
    }
    // The implied library bases, which no written relationship names:
    // the types the inherited features beyond those come from.
    let mut implied = Vec::new();
    for &f in &features {
        if seen.contains(&f) {
            continue;
        }
        if let Some(t) = resolved.owner(f) {
            if !general.contains(&t) && !implied.contains(&t) {
                implied.push(t);
            }
        }
    }
    for t in implied {
        for f in resolved.effective_features(t, true) {
            if seen.insert(f) {
                candidates.push(f);
            }
        }
    }
    // What a feature of the heritage redefines, directly or not, is not
    // inherited.
    let mut covered = HashSet::new();
    for &f in features.iter().chain(&candidates) {
        covered.extend(redefined_closure(resolved, f));
    }
    let inherited: HashSet<ElementRef> = features.iter().copied().collect();
    for f in candidates {
        if !inherited.contains(&f)
            && !covered.contains(&f)
            && resolved.member_visibility(f) != Some("private")
        {
            features.push(f);
        }
    }
    scope_members_of(resolved, features)
}

/// What `f` redefines, directly or through the features it redefines.
fn redefined_closure(
    resolved: &mut sysmlv2_parser::json::ResolvedModel,
    f: ElementRef,
) -> std::collections::HashSet<ElementRef> {
    let mut out = std::collections::HashSet::new();
    let mut walk = vec![f];
    while let Some(g) = walk.pop() {
        for t in resolved.redefinition_targets(g) {
            if out.insert(t) {
                walk.push(t);
            }
        }
    }
    out
}

/// The element declared where `innermost` is, in `unit` of a model built
/// from a text whose part ahead of its body is the live one: an element
/// with no name of its own, or where the qualified-name lookup fails —
/// not the innermost element holding the statement, which may be deeper
/// than it (a feature whose value holds an expression's body, `?{in p :>
/// …}`), and whose members would be kept for the element's. A statement
/// led by `then` records its succession over the same text, ahead of
/// what it declares: the last is the declaration.
fn declared_where(
    resolved: &sysmlv2_parser::json::ResolvedModel,
    unit: usize,
    innermost: &crate::kinds::Enclosing,
) -> Option<ElementRef> {
    let start = innermost.span.start;
    resolved
        .user_elements()
        .filter(|&e| {
            resolved
                .member_extent(e)
                .is_some_and(|(u, span)| u == unit && span.start == start)
        })
        .last()
}

/// [`inherited_of`] in a model built from an earlier text, of the
/// innermost of the declarations `around` a statement (see
/// [`crate::kinds::enclosing`]): found by their qualified name, else —
/// an element with no name (`@Safety { … }`, `part :> slot : Q { … }`),
/// or where the lookup fails — by where it is declared in `unit`, the
/// document's unit in that model (see [`declared_where`]). `None` when
/// the model holds no such element.
fn built_inherited(
    resolved: &mut sysmlv2_parser::json::ResolvedModel,
    around: &[crate::kinds::Enclosing],
    unit: Option<usize>,
) -> Option<Vec<ScopeMember>> {
    let qualified: Option<Vec<String>> = around
        .iter()
        .map(|e| e.name.as_deref().map(sysmlv2_parser::ast::escape_name))
        .collect();
    let owner = qualified
        .and_then(|names| resolved.resolve_qualified(&names.join("::")))
        .or_else(|| declared_where(resolved, unit?, around.last()?))?;
    Some(inherited_of(resolved, owner))
}

/// How many enclosing elements' inherited members are kept (see
/// [`Nav::inherited_members`]).
const MEMBER_CACHE: usize = 8;

/// How many statements' changes against the sessions built are kept
/// (see [`Nav::cut_answer`]).
const REUSED: usize = 4;

/// A kind of session built (see [`Nav::built`]). An answer read off
/// one is checked against the texts that one was built from — salvaged,
/// or with a statement cut out, as they are — so any of them serves the
/// completion tier, which reads a salvaged model of its own; what plans
/// edits over every reference, and read-only navigation, read only the
/// sessions [`Nav::session`] and [`Nav::read_session`] give them.
#[derive(Clone, Copy)]
enum Built {
    /// Navigation's, over the documents as written.
    Navigation,
    /// Read-only navigation's while the strict one cannot build, the
    /// units that do not parse salvaged.
    Tolerant,
    /// The completion tier's, the statement it was built for cut out.
    Completion,
}

impl Built {
    /// Every kind: one session of each is kept.
    const ALL: [Built; 3] = [Built::Navigation, Built::Tolerant, Built::Completion];

    /// Whether the session's model may hold the statement being typed as
    /// something else: the tolerant session salvages a statement left
    /// unfinished into the declaration it reads as, which the members an
    /// element inherits — read off any session whose text outside the
    /// element's body is the live one (see [`Nav::inherited_members`]) —
    /// would be named after.
    fn salvages_statements(self) -> bool {
        matches!(self, Built::Tolerant)
    }
}

/// A model a statement's answer is read off (see [`Nav::cut_answer`]).
pub(crate) struct Read<'a> {
    pub session: &'a mut Session,
    /// The session's unit for the document.
    pub unit: usize,
    /// Where the statement starts in the session's text of that unit —
    /// the text before it is the document's own when the session was
    /// built for the statement, and holds the same declarations around
    /// it otherwise.
    pub at: u32,
    /// What the answer read there (see [`crate::reuse::Needs`]).
    pub needs: crate::reuse::Needs,
    /// The library's units as last classified, with the build of the
    /// session they were classified in (see [`Nav::library_units`]).
    pub library_units: &'a mut Option<(u64, Vec<(usize, crate::units::UnitEntry)>)>,
    /// This session's build.
    pub build: u64,
}

/// The lengths of `text` ahead of and behind the body of the member
/// spanning `span`: through its opening brace, and from its closing one
/// — the whole rest of the text when the body is not closed.
fn outside_body(text: &str, span: Span) -> (usize, usize) {
    use sysmlv2_parser::token::TokenKind;
    let start = (span.start as usize).min(text.len());
    let end = (span.end as usize).clamp(start, text.len());
    let member = &text[start..end];
    let tokens = sysmlv2_parser::lexer::tokenize(member).0;
    let open = tokens
        .iter()
        .find(|t| t.kind == TokenKind::LBrace)
        .map_or(end, |t| start + t.span.end as usize);
    let close = tokens
        .iter()
        .rev()
        .find(|t| t.kind != TokenKind::Eof && !t.kind.is_trivia())
        .filter(|t| t.kind == TokenKind::RBrace && start + t.span.start as usize >= open)
        .map_or(end, |t| start + t.span.start as usize);
    (open, text.len() - close)
}

/// The key the inherited members of the innermost of `around` are kept
/// under (see [`Nav::inherited_members`]): the declarations around it,
/// the text of `uri` outside its body — `before` and `after` bytes —
/// every other open document's text, and the text hashes of the seeded
/// units no open document shadows, taken once per `seed`.
fn member_key(
    docs: &BTreeMap<Uri, Document>,
    uri: &Uri,
    text: &str,
    (before, after): (usize, usize),
    around: &[crate::kinds::Enclosing],
    seed: &[(String, u64)],
) -> u64 {
    use std::hash::{Hash, Hasher};
    let mut hasher = std::collections::hash_map::DefaultHasher::new();
    for e in around {
        e.name.hash(&mut hasher);
        for t in &e.types {
            t.is_global.hash(&mut hasher);
            for segment in &t.segments {
                segment.value.hash(&mut hasher);
            }
        }
    }
    let bytes = text.as_bytes();
    uri.to_string().hash(&mut hasher);
    bytes[..before].hash(&mut hasher);
    bytes[bytes.len() - after..].hash(&mut hasher);
    let mut open = std::collections::HashSet::new();
    for (u, d) in docs {
        let name = u.to_string();
        if u != uri {
            name.hash(&mut hasher);
            d.text.hash(&mut hasher);
        }
        open.insert(name);
    }
    // The seeded units no open document shadows, as of the last seed.
    for (name, text) in seed {
        if !open.contains(name) {
            name.hash(&mut hasher);
            text.hash(&mut hasher);
        }
    }
    hasher.finish()
}

/// Is the text a session was built from (`built`) the same as the text
/// now (`now`) outside the body of an element of the unit `uri` — its
/// first `before` and last `after` bytes there, every other unit whole?
fn outside_unchanged(
    built: &[(String, String)],
    now: &[(String, String)],
    uri: &str,
    before: usize,
    after: usize,
) -> bool {
    built.len() == now.len()
        && built.iter().zip(now).all(|((bn, bt), (nn, nt))| {
            if bn != nn {
                return false;
            }
            if bn != uri {
                return bt == nt;
            }
            let (b, n) = (bt.as_bytes(), nt.as_bytes());
            b.len() >= before + after
                && n.len() >= before + after
                && b[..before] == n[..before]
                && b[b.len() - after..] == n[n.len() - after..]
        })
}

/// `features` as [`ScopeMember`]s, each name once — a feature's lookup
/// name, so a redefinition declaring no name of its own counts under
/// the name of the feature it redefines.
fn scope_members_of(
    resolved: &mut sysmlv2_parser::json::ResolvedModel,
    features: Vec<ElementRef>,
) -> Vec<ScopeMember> {
    #[cfg(test)]
    MEMBER_READS.with(|n| n.set(n.get() + 1));
    let mut seen = std::collections::HashSet::new();
    let mut out = Vec::new();
    for m in features {
        let Some(name) = resolved.element_lookup_name(m) else {
            continue;
        };
        if !seen.insert(name.clone()) {
            continue;
        }
        let meta = resolved.element_type(m);
        out.push(ScopeMember {
            name,
            qualified: resolved.element_qualified_name(m),
            decl: crate::kinds::feature_decl(meta),
            kind: member_kind(meta),
            library: resolved.is_library_element(m),
        });
    }
    out
}

/// A feature in scope at a statement, from the completion tier's session
/// (see [`Nav::scope_members`]).
#[derive(Clone)]
struct ScopeMember {
    name: String,
    qualified: Option<String>,
    decl: crate::kinds::Decl,
    kind: lsp_types::CompletionItemKind,
    /// Declared in the library, not the workspace.
    library: bool,
}

/// What the cursor is completing: the partial word being typed, the
/// `::`-chained qualifier before it, and the statement it belongs to,
/// read off the toolkit's tokens of the text ahead of the cursor (see
/// [`crate::site`]).
pub(crate) struct CompletionCx {
    pub qualifier: Vec<String>,
    /// The `.`-chained feature path before the partial word
    /// (`fuelTank.` → `["fuelTank"]`, `a.b.` → `["a", "b"]`), empty
    /// when the cursor is not on a feature-chain step. A number before
    /// the dot (`9.8`) is a literal's decimal point, never a chain.
    pub dot_chain: Vec<String>,
    /// Byte range of the partial word: `partial_start..offset`.
    pub partial_start: u32,
    pub offset: u32,
    /// The statement is an `import`.
    pub import: bool,
    /// Statement start: its first token after the last `;`, `{`, `}`,
    /// or comment body token ahead of the cursor, the cursor when it has
    /// none yet — never inside a comment, note, string, or quoted name.
    /// The autofix tier's scan anchor.
    pub stmt_start: u32,
    /// The quoted name the cursor is typing, if any (see
    /// [`crate::accept`]): found by the token pass that reads the rest
    /// of the context, once per request, since each completion tier's
    /// accepts start from it.
    pub quoted: Option<crate::accept::Quoted>,
    /// The statement leaves a `[` open ahead of the partial word: the
    /// cursor sits where a quantity's unit is written (`9.8 [m`), or in
    /// a multiplicity (`[0..*]`), which the tokens cannot tell apart.
    /// The completion's own opening quote (`['deg`) leaves the bracket
    /// open. Read once per request, for the tiers that offer multi-word
    /// unit names and for the accepts that take such a name typed word
    /// by word.
    pub in_bracket: bool,
    /// What the partial word fills: nothing, a declared name, or a
    /// position taking some keywords and kinds of element.
    pub slot: crate::site::Slot,
}

/// Does the statement being typed at byte offset `at` import or expose
/// — is an `import` or `expose` keyword among its tokens? Read on the
/// toolkit's tokens of the text up to `at`, starting over at every `;`,
/// `{`, and `}` token and at a `[`, which opens an import's filter
/// condition, so the words in strings, quoted names, comments, notes,
/// and filter expressions never count.
pub(crate) fn in_import_path(text: &str, at: u32) -> bool {
    use sysmlv2_parser::token::TokenKind;
    let Some(prefix) = text.get(..at as usize) else {
        return false;
    };
    let mut keyword = false;
    for token in sysmlv2_parser::lexer::tokenize(prefix).0 {
        match token.kind {
            // A `[` opens an import's filter condition: an expression,
            // no longer the path.
            TokenKind::Semi | TokenKind::LBrace | TokenKind::RBrace | TokenKind::LBracket => {
                keyword = false;
            }
            TokenKind::Ident => {
                keyword |= matches!(token.span.slice(prefix), "import" | "expose");
            }
            _ => {}
        }
    }
    keyword
}

/// Does the statement being typed at byte offset `at` import with `all`
/// — is `import all` among its tokens, read as [`in_import_path`] reads
/// them? Such an import names a namespace's members whatever their
/// visibility.
pub(crate) fn imports_all(text: &str, at: u32) -> bool {
    use sysmlv2_parser::token::TokenKind;
    let Some(prefix) = text.get(..at as usize) else {
        return false;
    };
    let (mut after_import, mut all) = (false, false);
    for token in sysmlv2_parser::lexer::tokenize(prefix).0 {
        match token.kind {
            TokenKind::Whitespace | TokenKind::LineNote | TokenKind::BlockNote => {}
            TokenKind::Semi | TokenKind::LBrace | TokenKind::RBrace | TokenKind::LBracket => {
                (after_import, all) = (false, false);
            }
            TokenKind::Ident => {
                let word = token.span.slice(prefix);
                all |= after_import && word == "all";
                after_import = word == "import";
            }
            _ => after_import = false,
        }
    }
    all
}

/// The declare-the-type context for unit completions: the cursor sits
/// inside a quantity bracket in the value of an `attribute`
/// declaration that has a name and a `=` but no typing or
/// specialization clause. Carries the insertion point for a ` : T`
/// typing (right after the declared name) and the opening bracket.
pub(crate) struct UnitTypeCx {
    pub name_end: u32,
    pub bracket_open: u32,
}

/// Detect [`UnitTypeCx`] on the live document's tokens — the statement
/// being typed rarely parses, so the model cannot answer (see
/// [`crate::units::untyped_attribute`]). Conservative: a typing or
/// specialization between the name and the `=` bails, as does a cursor
/// not inside an open `[` of the value.
pub(crate) fn untyped_attribute_unit_context(text: &str, cx: &CompletionCx) -> Option<UnitTypeCx> {
    let (name_end, bracket_open) = crate::units::untyped_attribute(text, cx)?;
    Some(UnitTypeCx {
        name_end,
        bracket_open,
    })
}

/// A doc/comment body as hover Markdown — the model's shared
/// normalization (gutters stripped, blank edges trimmed).
pub(crate) fn doc_markdown(body: &str) -> String {
    sysmlv2_parser::json::doc_display_text(body)
}

/// A parameter's (or return's) types as a signature line spells them.
enum SigTypes {
    /// The written typings of a declaration in the workspace, failing
    /// those its other specialization clauses (subsetting, redefinition)
    /// — the qualified name spans as the author spelled them — sliced
    /// out of its unit, and its declared multiplicity as
    /// [`multiplicity_suffix`] spells it.
    Written(Vec<(usize, Span)>, String),
    /// Spelled from the model: a library declaration, whose text the
    /// session does not carry, or one with nothing written
    /// (interchange-lifted units) — see [`model_types`].
    Spelled(String),
}

/// Where a signature is read, for the types spelled from the model: the
/// document's dialect and the scope names resolve from there.
struct SigAt {
    dialect: sysmlv2_parser::ast::Dialect,
    scope: sysmlv2_parser::json::ScopeRef,
}

impl SigAt {
    /// The innermost of the user declarations in `unit` enclosing byte
    /// `at` that has a scope, the root namespace as the fallback.
    fn in_unit(
        resolved: &sysmlv2_parser::json::ResolvedModel,
        unit: usize,
        at: u32,
        dialect: sysmlv2_parser::ast::Dialect,
    ) -> SigAt {
        let scope = crate::receiver::enclosing_declarations(resolved, unit, at)
            .into_iter()
            .find_map(|e| resolved.element_scope(e))
            .unwrap_or_else(|| resolved.root_scope());
        SigAt { dialect, scope }
    }
}

/// One rendered-signature parameter: direction prefix (`in` is implied
/// and empty), name, types, and whether an argument binds it (see
/// [`crate::receiver::binds_argument`]).
struct SigParam {
    prefix: String,
    name: String,
    types: SigTypes,
    input: bool,
}

/// A callable's signature before type-spelling extraction.
struct SigParts {
    name: String,
    params: Vec<SigParam>,
    ret: Option<SigTypes>,
    /// The return parameter's own name — the `→` fallback when it
    /// declares no type (`return dv = …;`).
    ret_name: Option<String>,
}

/// The types of a feature's declaration (see [`SigTypes`]): as written
/// where the workspace declares it, else spelled from the model — its
/// typings either way, failing those what it subsets or redefines
/// (`in a :> isp`), so `in :>> m : Heavy` reads `m: Heavy`. A feature
/// that only redefines, writing no type, reads with the type of what it
/// redefines: `in :>> m` is `m: Mass`, not `m: m`.
fn spelled_types(
    resolved: &mut sysmlv2_parser::json::ResolvedModel,
    e: ElementRef,
    at: &SigAt,
) -> SigTypes {
    let mut e = e;
    let multiplicity = multiplicity_suffix(resolved, e);
    for _ in 0..8 {
        let redefined = resolved.redefinition_targets(e);
        let only_redefines = resolved.typing_spans(e).is_empty()
            && !redefined.is_empty()
            && resolved
                .explicit_supertypes(e)
                .iter()
                .all(|t| redefined.contains(t));
        match redefined.first() {
            Some(&next) if only_redefines => e = next,
            _ => break,
        }
    }
    let mut refs = resolved.typing_spans(e);
    if refs.is_empty() {
        refs = resolved.specialization_spans(e);
    }
    // The multiplicity the parameter declares, else what it redefines.
    let multiplicity = if multiplicity.is_empty() {
        multiplicity_suffix(resolved, e)
    } else {
        multiplicity
    };
    if refs.is_empty() || resolved.is_library_element(e) {
        SigTypes::Spelled(model_types(resolved, e, at, &multiplicity))
    } else {
        SigTypes::Written(refs, multiplicity)
    }
}

/// A feature's declared multiplicity as a signature line appends it to
/// the types (`[0..*]`, `[2]`), empty when it declares none or exactly
/// one.
fn multiplicity_suffix(
    resolved: &mut sysmlv2_parser::json::ResolvedModel,
    e: ElementRef,
) -> String {
    let bound = |b: f64| {
        if b.is_infinite() {
            "*".to_string()
        } else {
            format!("{b}")
        }
    };
    match resolved.declared_multiplicity(e) {
        Some((lo, hi)) if (lo, hi) != (1.0, 1.0) => {
            if lo == hi {
                format!("[{}]", bound(hi))
            } else {
                format!("[{}..{}]", bound(lo), bound(hi))
            }
        }
        _ => String::new(),
    }
}

/// A feature's types spelled from the model where `at` reads them: its
/// typings, or failing those its other written specializations, each
/// spelled the shortest way that resolves there — the fully qualified
/// name when nothing does — followed by `multiplicity` (see
/// [`multiplicity_suffix`], `Real[0..*]`). Empty when the feature
/// declares no type.
fn model_types(
    resolved: &mut sysmlv2_parser::json::ResolvedModel,
    e: ElementRef,
    at: &SigAt,
    multiplicity: &str,
) -> String {
    let mut targets = resolved.typings(e);
    if targets.is_empty() {
        targets = resolved.explicit_supertypes(e);
    }
    let dialect = Some(at.dialect);
    let names: Vec<String> = targets
        .into_iter()
        .filter_map(|t| {
            resolved
                .type_spelling_at(dialect, at.scope, t)
                .or_else(|| resolved.full_spelling(dialect, t))
        })
        .collect();
    if names.is_empty() {
        return String::new();
    }
    let mut spelled = names.join(", ");
    spelled.push_str(multiplicity);
    spelled
}

/// Assemble the signature line, slicing each type's written spelling
/// out of its unit's source.
fn render_signature(parts: SigParts, session: &Session) -> String {
    signature_line(parts, session).label
}

/// A rendered signature line, with each parameter's name and the byte
/// range its text takes in the line, and the parameters arguments bind,
/// in order, by their index in `params`: the inputs, outputs passed over.
pub(crate) struct SignatureLine {
    pub label: String,
    pub params: Vec<(String, std::ops::Range<usize>)>,
    pub inputs: Vec<usize>,
}

/// [`render_signature`], keeping where each parameter's text lands.
fn signature_line(parts: SigParts, session: &Session) -> SignatureLine {
    let types = |t: &SigTypes| -> Vec<String> {
        match t {
            SigTypes::Written(refs, multiplicity) => {
                let mut written: Vec<String> = refs
                    .iter()
                    .filter_map(|(unit, span)| {
                        let (_, _, src) = session.units().find(|(i, _, _)| i == unit)?;
                        src.get(span.start as usize..span.end as usize)
                            .map(|s| s.trim().to_string())
                    })
                    .filter(|s| !s.is_empty())
                    .collect();
                // The multiplicity follows the last type, as a declaration
                // writes it (`Mass[0..*]`).
                if let Some(last) = written.last_mut() {
                    last.push_str(multiplicity);
                }
                written
            }
            SigTypes::Spelled(spelled) if spelled.is_empty() => Vec::new(),
            SigTypes::Spelled(spelled) => vec![spelled.clone()],
        }
    };
    let mut label = format!("{}(", parts.name);
    let mut params = Vec::new();
    let mut inputs = Vec::new();
    for (i, p) in parts.params.iter().enumerate() {
        if i > 0 {
            label.push_str(", ");
        }
        let start = label.len();
        let ts = types(&p.types);
        if ts.is_empty() {
            label.push_str(&format!("{}{}", p.prefix, p.name));
        } else {
            label.push_str(&format!("{}{}: {}", p.prefix, p.name, ts.join(", ")));
        }
        if p.input {
            inputs.push(params.len());
        }
        params.push((p.name.clone(), start..label.len()));
    }
    label.push(')');
    let ret = parts
        .ret
        .as_ref()
        .map(&types)
        .filter(|ts| !ts.is_empty())
        .map(|ts| ts.join(", "))
        .or(parts.ret_name);
    if let Some(r) = ret {
        label.push_str(&format!(" → {r}"));
    }
    SignatureLine {
        label,
        params,
        inputs,
    }
}

/// A callable's function signature —
/// `calculateDeltaV(isp: specificImpulse, g0: ISQ::acceleration) →
/// ISQ::speed` — from the parameters it owns or inherits (see
/// [`crate::receiver::parameters`]) and the closest return parameter
/// (see [`crate::receiver::result_parameter`]), for every metaclass an
/// invocation expression can call: the SysML calc/constraint/action
/// definitions AND usages (a package-level `calc <ln> naturalLogarithm
/// { … }` is a CalculationUsage), and the KerML behavioral classifiers
/// (`function`, `predicate`, `behavior`).
/// `in` is the implied direction and stays silent; `out`/`inout` are
/// spelled. Types read as `at` sees them (see [`SigTypes`]). `None` for
/// other metaclasses and for callables with neither parameters nor a
/// result, own or inherited (the bare card already says everything).
fn def_signature(
    resolved: &mut sysmlv2_parser::json::ResolvedModel,
    target: ElementRef,
    metaclass: &str,
    at: &SigAt,
) -> Option<SigParts> {
    if !matches!(
        metaclass,
        "CalculationDefinition"
            | "ConstraintDefinition"
            | "ActionDefinition"
            | "CalculationUsage"
            | "ConstraintUsage"
            | "ActionUsage"
            | "Function"
            | "Predicate"
            | "Behavior"
    ) {
        return None;
    }
    let ret = crate::receiver::result_parameter(resolved, target);
    let params = crate::receiver::parameters(resolved, target);
    if params.is_empty() && ret.is_none() {
        return None;
    }
    // `calc :>> ke { … }` is called by what it redefines.
    let name = crate::receiver::feature_name(resolved, target)
        .unwrap_or_else(|| "<anonymous>".to_string());
    let params: Vec<SigParam> = params
        .into_iter()
        .map(|(p, name)| SigParam {
            prefix: match resolved.declared_direction(p) {
                Some("in") | None => String::new(),
                Some(dir) => format!("{dir} "),
            },
            name: name.unwrap_or_else(|| "_".to_string()),
            types: spelled_types(resolved, p, at),
            input: crate::receiver::binds_argument(resolved, p),
        })
        .collect();
    Some(SigParts {
        name,
        ret: ret.map(|r| spelled_types(resolved, r, at)),
        ret_name: ret.and_then(|r| resolved.element_name(r).map(str::to_string)),
        params,
    })
}

/// An item a list offers by simple name, as the declare-the-type edits
/// read it: its index in the list, the symbol's name and path, and the
/// document declaring it (`None`: the library).
type Offered = (usize, String, String, Option<String>);

/// What the item at `index` offering `s` was built from.
fn offered(index: usize, s: &QualifiedSymbol) -> Offered {
    let site = s.site.as_ref().map(|(uri, _)| uri.clone());
    (index, s.name.clone(), s.qualified.clone(), site)
}

/// The element the symbol at `qualified`, declared in the document
/// `site` (`None`: the library), stands for in a session whose units
/// are `unit_of` by name: the one its path names from the root, unless
/// another document declares the path's top-level package too and the
/// path finds that one's — then the one it names inside the top-level
/// package of the document declaring it. `tops` holds the top-level
/// elements by unit and name, once a symbol needed them.
fn declared_element(
    resolved: &mut sysmlv2_parser::json::ResolvedModel,
    qualified: &str,
    site: Option<&str>,
    unit_of: &HashMap<String, usize>,
    tops: &mut Option<HashMap<(usize, String), ElementRef>>,
) -> Option<ElementRef> {
    let by_path = resolved.resolve_qualified(qualified);
    let Some(unit) = site.and_then(|uri| unit_of.get(uri)).copied() else {
        return by_path;
    };
    let declared_here = |resolved: &sysmlv2_parser::json::ResolvedModel, e: ElementRef| {
        resolved.member_extent(e).is_some_and(|(u, _)| u == unit)
    };
    if by_path.is_some_and(|e| declared_here(resolved, e)) {
        return by_path;
    }
    let mut segments = qualified.split("::");
    let first = segments.next()?;
    let tops = tops.get_or_insert_with(|| {
        let elements: Vec<ElementRef> = resolved.user_elements().collect();
        let mut out = HashMap::new();
        for e in elements {
            let top = resolved
                .owner(e)
                .is_some_and(|root| resolved.owner(root).is_none());
            let site = resolved.member_extent(e).map(|(u, _)| u);
            if let (true, Some(u), Some(name)) = (top, site, resolved.element_name(e)) {
                out.entry((u, name.to_string())).or_insert(e);
            }
        }
        out
    });
    let top = *tops.get(&(unit, first.to_string()))?;
    let rest: Vec<sysmlv2_parser::ast::Name> = segments
        .map(|value| sysmlv2_parser::ast::Name {
            value: value.to_string(),
            span: Span::default(),
        })
        .collect();
    if rest.is_empty() {
        return Some(top);
    }
    let path = sysmlv2_parser::ast::QualifiedName {
        is_global: false,
        segments: rest,
        span: Span::default(),
    };
    resolved.member_of(top, &path).map(|(e, _)| e)
}

/// What accepting `s` by simple name takes to resolve at the cursor
/// `auto` describes: `Some(None)` nothing, `Some(Some(edit))` the import
/// `edit`, `None` when no import gives it — a member of a type, or a
/// usage without a name of its own, outside its owner, a name that finds
/// something else at the cursor (see
/// [`crate::autoimport::AutoImport::needs`]), or a symbol its own or an
/// ancestor's visibility keeps from being named here by its path, which
/// only an existing import the symbol tables follow, or one through a
/// package re-exporting it, brings in.
fn reach(
    auto: &crate::autoimport::AutoImport<'_>,
    s: &QualifiedSymbol,
) -> Option<Option<crate::autoimport::ImportEdit>> {
    use crate::autoimport::Needs;
    if s.depth == 0 {
        return Some(None);
    }
    // A member of a type, or of something a type holds, has no path an
    // import could name: it is offered by its simple name where that
    // name finds it — inside its owner, inside what inherits it, and
    // where an import in scope brings it in. So is a usage without a
    // name of its own, by the name it is found by: elsewhere that name
    // is the feature's own, or another member's.
    if !s.importable || s.effective {
        let found = s
            .parent()
            .is_some_and(|owner| auto.may_find(&s.name, &s.qualified, owner))
            && matches!(auto.needs(&s.name, &s.qualified), Needs::Nothing);
        return found.then_some(None);
    }
    let seen = if !s.public {
        auto.sees_hidden(&s.name, &s.qualified)
    } else if s.enclosed().is_some_and(|ns| !auto.inside(ns)) {
        auto.sees_enclosed(&s.name, &s.qualified)
    } else {
        return match auto.needs(&s.name, &s.qualified) {
            Needs::Nothing => Some(None),
            Needs::Import(edit) => Some(Some(edit)),
            Needs::Qualifier => None,
        };
    };
    if seen {
        return Some(None);
    }
    match auto.needs(&s.name, &s.qualified) {
        Needs::Import(edit) if edit.route.is_some() => Some(Some(edit)),
        Needs::Nothing | Needs::Import(_) | Needs::Qualifier => None,
    }
}

/// The text edit and source annotation of the import `edit` accepting
/// `s` by simple name needs: the annotation names the package the import
/// runs through, spelled as the statement spells it in `dialect`.
fn import_for(
    mapper: &Mapper<'_>,
    dialect: sysmlv2_parser::ast::Dialect,
    s: &QualifiedSymbol,
    edit: crate::autoimport::ImportEdit,
) -> Option<(Vec<TextEdit>, lsp_types::CompletionItemLabelDetails)> {
    let parent = edit
        .route
        .as_deref()
        .unwrap_or(&s.qualified)
        .strip_suffix(s.name.as_str())?
        .strip_suffix("::")?;
    // Most paths need no quote: those are taken as they are.
    let plain = parent.split("::").all(|segment| {
        segment
            .chars()
            .next()
            .is_some_and(|c| c.is_ascii_alphabetic() || c == '_')
            && segment
                .chars()
                .all(|c| c.is_ascii_alphanumeric() || c == '_')
            && !sysmlv2_parser::parser::is_reserved(dialect, segment)
    });
    let parent: std::borrow::Cow<'_, str> = if plain {
        parent.into()
    } else {
        crate::autoimport::escape_qualified(dialect, parent).into()
    };
    let description = if edit.global {
        format!("import $::{parent}")
    } else {
        format!("import {parent}")
    };
    Some((
        vec![TextEdit {
            range: mapper.range(Span::new(edit.at, edit.at)),
            new_text: edit.text,
        }],
        lsp_types::CompletionItemLabelDetails {
            detail: None,
            description: Some(description),
        },
    ))
}

/// A member's completion-item kind from its abstract-syntax metaclass
/// name — coarse buckets, enough for distinct icons.
fn member_kind(meta: &str) -> lsp_types::CompletionItemKind {
    use lsp_types::CompletionItemKind as K;
    if meta.contains("Enumeration") {
        K::ENUM_MEMBER
    } else if meta.contains("Calculation") || meta.contains("Action") || meta.contains("Function") {
        K::METHOD
    } else if meta.contains("Port") {
        K::INTERFACE
    } else if meta.contains("Attribute") {
        K::FIELD
    } else {
        K::PROPERTY
    }
}

pub(crate) fn completion_context(
    text: &str,
    offset: u32,
    dialect: sysmlv2_parser::ast::Dialect,
) -> CompletionCx {
    let bytes = text.as_bytes();
    let is_ident = |b: u8| b.is_ascii_alphanumeric() || b == b'_';
    let offset = (offset as usize).min(bytes.len());
    let mut partial_start = offset;
    while partial_start > 0 && is_ident(bytes[partial_start - 1]) {
        partial_start -= 1;
    }
    let mut qualifier = Vec::new();
    let mut j = partial_start;
    while j >= 2 && &bytes[j - 2..j] == b"::" {
        let end = j - 2;
        let mut start = end;
        while start > 0 && is_ident(bytes[start - 1]) {
            start -= 1;
        }
        if start == end {
            break;
        }
        qualifier.push(text[start..end].to_string());
        j = start;
    }
    qualifier.reverse();
    // A feature-chain prefix (`fuelTank.` / `a.b.`) — only where no
    // `::` qualifier claimed the position, and never after a number
    // (`9.8` is a literal, its dot no chain step).
    let mut dot_chain = Vec::new();
    if qualifier.is_empty() {
        let mut k = partial_start;
        while k >= 1 && bytes[k - 1] == b'.' {
            let end = k - 1;
            let mut start = end;
            while start > 0 && is_ident(bytes[start - 1]) {
                start -= 1;
            }
            if start == end || bytes[start].is_ascii_digit() {
                dot_chain.clear();
                break;
            }
            dot_chain.push(text[start..end].to_string());
            k = start;
        }
        dot_chain.reverse();
    }
    // A qualified name stands where its first segment does: the position
    // is read off the text ahead of it (`attribute x : ISQ::Mas` takes
    // what a typing takes), a global `$::` included.
    let word_start = if qualifier.is_empty() {
        partial_start
    } else if text[..j].ends_with("$::") {
        j - 3
    } else {
        j
    };
    let scan = crate::site::scan(text, offset32(word_start), offset32(offset), dialect);
    CompletionCx {
        qualifier,
        dot_chain,
        partial_start: offset32(partial_start),
        offset: offset32(offset),
        import: scan.import,
        stmt_start: scan.stmt_start,
        quoted: scan
            .quote
            .and_then(|open| crate::accept::quoted_from(text, open, offset32(offset))),
        in_bracket: scan.in_bracket,
        slot: scan.slot,
    }
}

#[cfg(test)]
thread_local! {
    /// Answers read off a session built from other texts on this thread
    /// (see [`Nav::cut_answer`]), so a test can pin where one was.
    pub(crate) static REUSED_ANSWERS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

#[cfg(test)]
thread_local! {
    /// Session builds on this thread, so a test can pin what a request
    /// costs.
    pub(crate) static SESSION_BUILDS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
    /// Enclosing elements' member lists read off a model on this thread.
    pub(crate) static MEMBER_READS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

#[cfg(test)]
mod context_tests {
    use super::{completion_context, offset32};
    use sysmlv2_parser::ast::Dialect;

    #[test]
    fn open_bracket_detection() {
        for (stmt, open) in [
            ("attribute g = 9.8 [", true),
            ("attribute g = 9.8 [m/", true),
            // the completion's own opening quote keeps it open
            ("attribute g = 9.8 ['", true),
            // closed again: an expression continues
            ("attribute g = 9.8 [m] + ", false),
            ("attribute g : ", false),
            // a multiplicity counts, nested brackets count once open
            ("part w : Wheel [0..", true),
            ("attribute a = b[c[d]", true),
            // brackets in strings, quoted names, and comments do not
            ("attribute s = \"[\" + ", false),
            ("attribute s = 'a[' + ", false),
            ("attribute s /* [ */ = ", false),
            ("attribute s // [\n = ", false),
            // an unterminated string or comment is not a bracket
            ("attribute s = \"a [", false),
            ("attribute s /* [", false),
            // a note runs to its `*/`, across lines
            ("attribute g = 9.8 //* see\n [ */ + ", false),
            ("attribute g = 9.8 [ //* see\n ] */ + ", true),
            // statement boundaries count only as tokens: a `;` inside a
            // comment neither ends the statement nor exposes the text
            // after it
            (
                "part def V {\n doc /* mass; it's wet */\n attribute a = 9.8 [",
                true,
            ),
            ("part def V {\n /* note; [draft */\n attribute x : ", false),
            // a statement boundary closes what the statement left open
            ("attribute a = 9.8 [m;\n attribute b : ", false),
        ] {
            assert_eq!(
                completion_context(stmt, offset32(stmt.len()), Dialect::Sysml).in_bracket,
                open,
                "{stmt:?}"
            );
        }
    }

    #[test]
    fn qualifier_and_import_detection() {
        let text = "package P { private import ScalarFunctions:: }";
        let cx = completion_context(text, 44, Dialect::Sysml);
        assert_eq!(cx.qualifier, vec!["ScalarFunctions"]);
        assert!(cx.import);

        let text = "package P { private import Real }";
        let cx = completion_context(text, 31, Dialect::Sysml);
        assert!(cx.qualifier.is_empty());
        assert!(cx.import);
        assert_eq!(&text[cx.partial_start as usize..cx.offset as usize], "Real");

        let text = "package P { part x : ISQ::Torque }";
        let cx = completion_context(text, 32, Dialect::Sysml);
        assert_eq!(cx.qualifier, vec!["ISQ"]);
        assert!(!cx.import);

        let text = "package P { import A::B:: }";
        let cx = completion_context(text, 25, Dialect::Sysml);
        assert_eq!(cx.qualifier, vec!["A", "B"]);
        assert!(cx.import);

        let text = "part w : ";
        let cx = completion_context(text, 9, Dialect::Sysml);
        assert!(cx.qualifier.is_empty());
        assert!(!cx.import);
    }

    #[test]
    fn dot_chain_detection() {
        // Bare dot, and a partial after it.
        let text = "package P { attribute t = fuelTank. }";
        let cx = completion_context(text, 35, Dialect::Sysml);
        assert_eq!(cx.dot_chain, vec!["fuelTank"]);
        let text = "package P { attribute t = fuelTank.vol }";
        let cx = completion_context(text, 38, Dialect::Sysml);
        assert_eq!(cx.dot_chain, vec!["fuelTank"]);
        assert_eq!(&text[cx.partial_start as usize..cx.offset as usize], "vol");

        // Multi-hop chains keep every segment, in order.
        let text = "package P { attribute t = sys.tank.liq }";
        let cx = completion_context(text, 38, Dialect::Sysml);
        assert_eq!(cx.dot_chain, vec!["sys", "tank"]);

        // A literal's decimal point is no chain step.
        let text = "package P { attribute t = 9.8 }";
        let cx = completion_context(text, 29, Dialect::Sysml);
        assert!(cx.dot_chain.is_empty());

        // `::` qualifiers keep their own context.
        let text = "package P { part x : ISQ::Torque }";
        let cx = completion_context(text, 32, Dialect::Sysml);
        assert!(cx.dot_chain.is_empty());
    }
}
